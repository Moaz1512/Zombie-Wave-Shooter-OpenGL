/*
 * =============================================================================
 * ZOMBIE WAVE SHOOTER 3D (The Graveyard & Blood Moon Final - No Errors)
 * C++ / OpenGL (freeglut)
 * =============================================================================
 *
 * Controls:
 * W / A / S / D    -- Move forward / left / backward / right
 * Mouse (move)     -- Look around
 * Left Mouse Btn   -- Shoot
 * Q                -- Switch Weapon (Pistol / Shotgun)
 * R                -- Reload Ammo
 * Esc              -- Quit
 * =============================================================================
 */

#ifdef _WIN32
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  ifndef NOMINMAX
#    define NOMINMAX
#  endif
#  include <windows.h>
#endif

#include <GL/glut.h>
#include <cmath>
#include <cstring>
#include <cstdlib>
#include <ctime>
#include <string>
#include <vector>
#include <algorithm>
#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"
GLuint groundTexture;

/* ===========================================================================
   Constants
   =========================================================================== */
static const int   WIN_W = 1280;
static const int   WIN_H = 720;

static const float ARENA_HALF = 30.0f;
static const float PLAYER_SPEED = 0.16f;
static const float BULLET_SPEED = 0.8f;

static const float ZOMBIE_SPEED_BASE = 0.007f;
static const float ZOMBIE_SPEED_INC = 0.001f;

static const float PLAYER_HEIGHT = 1.75f;
static const float PLAYER_RADIUS = 0.5f;
static const float ZOMBIE_RADIUS = 0.6f;
static const float BULLET_RADIUS = 0.15f;
static const int   MAX_HEALTH_INT = 100;
static const float HIT_COOLDOWN = 1.0f;
static const float MOUSE_SENS_F = 0.04f;
static const float WAVE_PAUSE_SEC = 3.0f;
static const float BULLET_MAX_DIST = 60.0f;

static const float MY_PI = 3.14159265358979f;
static const float DEG2RAD = 3.14159265358979f / 180.0f;

/* ===========================================================================
   Math & Structs
   =========================================================================== */
struct Vec3 {
	float x, y, z;
	Vec3() : x(0.0f), y(0.0f), z(0.0f) {}
	Vec3(float ax, float ay, float az) : x(ax), y(ay), z(az) {}
	Vec3 operator+(const Vec3& o) const { return Vec3(x + o.x, y + o.y, z + o.z); }
	Vec3 operator-(const Vec3& o) const { return Vec3(x - o.x, y - o.y, z - o.z); }
	Vec3 operator*(float s)       const { return Vec3(x * s, y * s, z * s); }
	float length() const { return sqrtf(x * x + y * y + z * z); }
	Vec3 normalized() const {
		float l = length();
		if (l < 1e-6f) return Vec3();
		return Vec3(x / l, y / l, z / l);
	}
};

static float g_randf(float lo, float hi) {
	return lo + (hi - lo) * ((float)rand() / (float)RAND_MAX);
}

struct Obstacle { Vec3 pos; float hw, hh, hd; int type; };
struct Bullet { Vec3 pos; Vec3 dir; float distTravelled; bool alive; float damage; };
struct BloodParticle { Vec3 pos; Vec3 vel; float life; float maxLife; bool alive; };

struct Zombie {
	Vec3  pos;
	float health;
	float hitCooldown;
	float walkPhase;
	bool  alive;
	int   type;
	float scale;
	float spdMult;
	float speed;
	float damage;
	float r, g, b;
};

/* ===========================================================================
   Global Game State
   =========================================================================== */
static Vec3  g_playerPos;
static float g_yaw = 0.0f;
static float g_pitch = 0.0f;
static float g_playerHealth = 0.0f;
static int   g_score = 0;

static int   g_weapon = 0;
static int   g_ammo[2] = { 15, 5 };
static int   g_magCapacity[2] = { 15, 5 };
static bool  g_reloading = false;
static float g_reloadTimer = 0.0f;
static float g_fireCooldown = 0.0f;

static int   g_lastMouseX = WIN_W / 2;
static int   g_lastMouseY = WIN_H / 2;
static bool  g_keys[256];

static std::vector<Bullet>   g_bullets;
static std::vector<Zombie>   g_zombies;
static std::vector<Obstacle> g_obstacles;
static std::vector<BloodParticle> g_blood;

struct StarPos { float x, y, z; float bright; };
static std::vector<StarPos> g_stars;

static int   g_wave = 1;
static int   g_zombiesThisWave = 5;
static int   g_zombiesLeft = 0;
static bool  g_waveClear = false;
static float g_waveClearTimer = 0.0f;

static int   g_lastTime = 0;
static float g_gameTime = 0.0f;

static bool  g_gameOver = false;
static bool  g_muzzleOn = false;
static float g_muzzleTimer = 0.0f;
static bool  g_warping = false;

/* ===========================================================================
   Forward Declarations
   =========================================================================== */
static void spawnWave();
static void resetGame();
static void shoot();

/* ===========================================================================
   Collisions
   =========================================================================== */
static bool sphereVsBox(const Vec3& c, float r, const Obstacle& o) {
	float dx = fabsf(c.x - o.pos.x); if (dx > o.hw) dx -= o.hw; else dx = 0.0f;
	float dy = fabsf(c.y - o.pos.y); if (dy > o.hh) dy -= o.hh; else dy = 0.0f;
	float dz = fabsf(c.z - o.pos.z); if (dz > o.hd) dz -= o.hd; else dz = 0.0f;
	return (dx * dx + dy * dy + dz * dz) < r * r;
}

static Vec3 clampArena(Vec3 p, float r) {
	float lim = ARENA_HALF - r;
	if (p.x < -lim) p.x = -lim;
	if (p.x > lim) p.x = lim;
	if (p.z < -lim) p.z = -lim;
	if (p.z > lim) p.z = lim;
	return p;
}

static Vec3 resolveCollisions(Vec3 pos, float radius) {
	pos = clampArena(pos, radius);
	for (int i = 0; i < 3; ++i) {
		for (int oi = 0; oi < (int)g_obstacles.size(); ++oi) {
			const Obstacle& ob = g_obstacles[oi];
			float cx = std::max(ob.pos.x - ob.hw, std::min(pos.x, ob.pos.x + ob.hw));
			float cz = std::max(ob.pos.z - ob.hd, std::min(pos.z, ob.pos.z + ob.hd));
			float dx = pos.x - cx;
			float dz = pos.z - cz;
			float distSq = dx * dx + dz * dz;
			if (distSq < radius * radius && distSq > 0.00001f) {
				float dist = sqrtf(distSq);
				float pen = radius - dist;
				pos.x += (dx / dist) * pen;
				pos.z += (dz / dist) * pen;
			}
			else if (distSq <= 0.00001f) {
				pos.x += 0.01f;
			}
		}
	}
	return clampArena(pos, radius);
}

/* ===========================================================================
   Game Logic Helpers (Graveyard Update)
   =========================================================================== */
static void buildObstacles() {
	g_obstacles.clear();
	Obstacle ob;

	ob.pos = Vec3(0.0f, 0.0f, -5.0f); ob.hw = 0.6f; ob.hh = 3.0f; ob.hd = 0.6f; ob.type = 1; // شجرة
	g_obstacles.push_back(ob);

	float tsHW = 0.5f, tsHH = 0.75f, tsHD = 0.15f;
	Vec3 gravePositions[] = {
		Vec3(5, tsHH, 5), Vec3(-6, tsHH, 8), Vec3(8, tsHH, -5), Vec3(-7, tsHH, -7),
		Vec3(12, tsHH, 0), Vec3(-12, tsHH, 2), Vec3(0, tsHH, 12), Vec3(2, tsHH, -12),
		Vec3(15, tsHH, 15), Vec3(-14, tsHH, -16), Vec3(18, tsHH, -10), Vec3(-15, tsHH, 10),
		Vec3(22, tsHH, 5), Vec3(-22, tsHH, -5), Vec3(5, tsHH, 22), Vec3(-5, tsHH, -22)
	};

	for (int i = 0; i < 16; ++i) {
		ob.pos = gravePositions[i];
		ob.hw = tsHW; ob.hh = tsHH; ob.hd = tsHD; ob.type = 0; // مقبرة
		g_obstacles.push_back(ob);
	}
}

static void spawnWave() {
	g_zombiesLeft = g_zombiesThisWave;

	// 🔥 إعدادات السرعة
	float baseSpeed = 0.04f;
	float maxSpeed = 0.08f;

	for (int i = 0; i < g_zombiesThisWave; ++i) {
		Zombie zz;

		zz.alive = true;
		zz.hitCooldown = 0.0f;
		zz.walkPhase = g_randf(0.0f, 2.0f * MY_PI);

		int chance = rand() % 100;

		// 🧟 تحديد نوع الزومبي
		if (chance < 60) {
			// Normal
			zz.type = 0;
			zz.health = 100.0f;
			zz.scale = 1.0f;
			zz.spdMult = 1.0f;
			zz.damage = 15.0f;

			zz.r = 0.18f; zz.g = 0.38f; zz.b = 0.16f;
		}
		else if (chance < 85) {
			// Fast
			zz.type = 1;
			zz.health = 40.0f;
			zz.scale = 0.90f;

			// 🔥 عدلنا السرعة عشان متبقاش مجنونة
			zz.spdMult = 1.8f;

			zz.damage = 8.0f;
			zz.r = 0.5f; zz.g = 0.1f; zz.b = 0.1f;
		}
		else {
			// Tank
			zz.type = 2;
			zz.health = 400.0f;
			zz.scale = 1.5f;
			zz.spdMult = 0.5f;
			zz.damage = 40.0f;

			zz.r = 0.15f; zz.g = 0.15f; zz.b = 0.15f;
		}

		// 🔥 حساب السرعة حسب الليفل (wave)
		float levelFactor = baseSpeed + g_wave * 0.003f;

		if (levelFactor > maxSpeed)
			levelFactor = maxSpeed;

		zz.speed = levelFactor * zz.spdMult;

		// 📍 تحديد مكان الspawn
		float angle = g_randf(0.0f, 2.0f * MY_PI);
		float dist = g_randf(ARENA_HALF * 0.65f, ARENA_HALF * 0.90f);

		zz.pos = Vec3(cosf(angle) * dist, 0.0f, sinf(angle) * dist);

		g_zombies.push_back(zz);
	}
}

static void resetGame() {
	g_playerPos = Vec3(0.0f, PLAYER_HEIGHT, 5.0f);
	g_yaw = 0.0f;
	g_pitch = 0.0f;
	g_playerHealth = (float)MAX_HEALTH_INT;
	g_score = 0;
	g_wave = 1;
	g_zombiesThisWave = 5;
	g_waveClear = false;
	g_waveClearTimer = 0.0f;
	g_gameOver = false;

	g_weapon = 0;
	g_ammo[0] = g_magCapacity[0];
	g_ammo[1] = g_magCapacity[1];
	g_reloading = false;
	g_fireCooldown = 0.0f;

	g_muzzleOn = false;
	g_muzzleTimer = 0.0f;
	g_gameTime = 0.0f;
	memset(g_keys, 0, sizeof(g_keys));
	g_bullets.clear();
	g_zombies.clear();
	g_blood.clear();
	buildObstacles();
	spawnWave();

	g_stars.clear();
	g_stars.reserve(300);
	for (int i = 0; i < 300; ++i) {
		float theta = g_randf(0.0f, 2.0f * MY_PI);
		float phi = g_randf(0.08f, MY_PI * 0.5f);
		float R = 170.0f;
		StarPos sp;
		sp.x = cosf(theta) * cosf(phi) * R;
		sp.y = sinf(phi) * R;
		sp.z = sinf(theta) * cosf(phi) * R;
		sp.bright = g_randf(0.55f, 1.0f);
		g_stars.push_back(sp);
	}
}

/* ===========================================================================
   Custom GLU rendering helper
   =========================================================================== */
static void drawSolidCylinder(float radius, float height, int slices, int stacks) {
	GLUquadric* quad = gluNewQuadric();
	gluCylinder(quad, radius, radius, height, slices, stacks);
	glPushMatrix();
	glRotatef(180.0f, 1.0f, 0.0f, 0.0f);
	gluDisk(quad, 0.0f, radius, slices, 1);
	glPopMatrix();
	glPushMatrix();
	glTranslatef(0.0f, 0.0f, height);
	gluDisk(quad, 0.0f, radius, slices, 1);
	glPopMatrix();
	gluDeleteQuadric(quad);
}

/* ===========================================================================
   Renderings
   =========================================================================== */
static void drawBox(float hw, float hh, float hd) {
	glPushMatrix();
	glScalef(hw * 2.0f, hh * 2.0f, hd * 2.0f);
	glutSolidCube(1.0);
	glPopMatrix();
}

static void drawText2D(const std::string& s, float px, float py, float cr, float cg, float cb) {
	glColor3f(cr, cg, cb);
	glRasterPos2f(px, py);
	for (int i = 0; i < (int)s.size(); ++i)
		glutBitmapCharacter(GLUT_BITMAP_HELVETICA_18, (int)s[i]);
}

GLuint loadTexture(const char* filename) {
	int width, height, nrChannels;

	// 👇 Debug مهم
	printf("Trying to load: %s\n", filename);

	unsigned char* data = stbi_load(filename, &width, &height, &nrChannels, 0);

	if (!data) {
		printf("❌ Failed to load texture: %s\n", filename);
		return 0; // 🔥 مهم جدًا
	}

	printf("✅ Loaded: %s | %dx%d\n", filename, width, height);

	GLuint textureID;
	glGenTextures(1, &textureID);
	glBindTexture(GL_TEXTURE_2D, textureID);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_REPEAT);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_REPEAT);

	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
	glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);

	GLenum format = (nrChannels == 4) ? GL_RGBA : GL_RGB;

	glTexImage2D(GL_TEXTURE_2D, 0, format, width, height, 0, format, GL_UNSIGNED_BYTE, data);

	stbi_image_free(data);

	return textureID;
}

static void renderGround() {
	glEnable(GL_TEXTURE_2D); // تفعيل الـ Textures
	glBindTexture(GL_TEXTURE_2D, groundTexture); // ربط صورة الأرضية

	// مهم جداً نخلي اللون أبيض عشان الصورة تظهر بلونها الأصلي
	// لو معملناش كدا الصورة هتاخد آخر لون تم استخدامه في الكود
	glColor3f(1.0f, 1.0f, 1.0f);

	int tiles = 30;
	float tileSize = ARENA_HALF * 2.0f / (float)tiles;

	glBegin(GL_QUADS);
	for (int ii = 0; ii < tiles; ++ii) {
		for (int jj = 0; jj < tiles; ++jj) {
			float x0 = -ARENA_HALF + (float)ii * tileSize;
			float z0 = -ARENA_HALF + (float)jj * tileSize;

			// ربط إحداثيات الصورة (glTexCoord2f) مع إحداثيات المجسم (glVertex3f)
			glTexCoord2f(0.0f, 0.0f); glVertex3f(x0, 0.0f, z0);
			glTexCoord2f(1.0f, 0.0f); glVertex3f(x0 + tileSize, 0.0f, z0);
			glTexCoord2f(1.0f, 1.0f); glVertex3f(x0 + tileSize, 0.0f, z0 + tileSize);
			glTexCoord2f(0.0f, 1.0f); glVertex3f(x0, 0.0f, z0 + tileSize);
		}
	}
	glEnd();

	glDisable(GL_TEXTURE_2D); // نقفلها عشان متأثرش على باقي رسم اللعبة (الزومبي والسماء)
}

static void renderSky() {
	glDisable(GL_LIGHTING); glDisable(GL_DEPTH_TEST);
	float R = 180.0f; int stacks = 8, slices = 24;
	for (int si = 0; si < stacks; ++si) {
		float phi0 = (float)si / (float)stacks * MY_PI * 0.5f;
		float phi1 = (float)(si + 1) / (float)stacks * MY_PI * 0.5f;
		float t0 = (float)si / (float)stacks; float t1 = (float)(si + 1) / (float)stacks;

		float r0 = 0.20f - 0.18f * t0, g0 = 0.02f, b0 = 0.02f;
		float r1 = 0.20f - 0.18f * t1, g1 = 0.02f, b1 = 0.02f;

		glBegin(GL_QUAD_STRIP);
		for (int sl = 0; sl <= slices; ++sl) {
			float theta = (float)sl / (float)slices * 2.0f * MY_PI;
			float ct = cosf(theta), st = sinf(theta);
			glColor3f(r0, g0, b0); glVertex3f(ct * cosf(phi0) * R, sinf(phi0) * R, st * cosf(phi0) * R);
			glColor3f(r1, g1, b1); glVertex3f(ct * cosf(phi1) * R, sinf(phi1) * R, st * cosf(phi1) * R);
		}
		glEnd();
	}

	glPointSize(2.2f); glBegin(GL_POINTS);
	for (int i = 0; i < (int)g_stars.size(); ++i) {
		glColor3f(g_stars[i].bright, g_stars[i].bright * 0.8f, g_stars[i].bright * 0.8f);
		glVertex3f(g_stars[i].x, g_stars[i].y, g_stars[i].z);
	}
	glEnd(); glPointSize(1.0f);

	glPushMatrix();
	glTranslatef(-70.0f, 45.0f, -120.0f);

	glEnable(GL_BLEND);
	glColor4f(0.9f, 0.1f, 0.0f, 0.4f);
	glutSolidSphere(18.0, 20, 20);
	glDisable(GL_BLEND);

	glColor3f(0.8f, 0.05f, 0.05f);
	glutSolidSphere(16.0, 30, 30);
	glPopMatrix();

	glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING);
}

static void renderArenaWalls() {
	glColor3f(0.05f, 0.05f, 0.05f);
	float W = ARENA_HALF;

	for (float i = -W; i <= W; i += 2.0f) {
		glPushMatrix(); glTranslatef(i, 1.5f, -W); drawBox(0.08f, 1.5f, 0.08f); glPopMatrix();
		glPushMatrix(); glTranslatef(i, 1.5f, W); drawBox(0.08f, 1.5f, 0.08f); glPopMatrix();
		glPushMatrix(); glTranslatef(-W, 1.5f, i); drawBox(0.08f, 1.5f, 0.08f); glPopMatrix();
		glPushMatrix(); glTranslatef(W, 1.5f, i); drawBox(0.08f, 1.5f, 0.08f); glPopMatrix();
	}

	for (float h = 0.5f; h <= 2.5f; h += 1.0f) {
		glPushMatrix(); glTranslatef(0.0f, h, -W); drawBox(W, 0.04f, 0.04f); glPopMatrix();
		glPushMatrix(); glTranslatef(0.0f, h, W); drawBox(W, 0.04f, 0.04f); glPopMatrix();
		glPushMatrix(); glTranslatef(-W, h, 0.0f); drawBox(0.04f, 0.04f, W); glPopMatrix();
		glPushMatrix(); glTranslatef(W, h, 0.0f); drawBox(0.04f, 0.04f, W); glPopMatrix();
	}
}

static void renderDeadTree(const Obstacle& ob) {
	glColor3f(0.15f, 0.1f, 0.05f);
	glPushMatrix();
	glTranslatef(ob.pos.x, 0.0f, ob.pos.z);

	glPushMatrix();
	glRotatef(-90.0f, 1.0f, 0.0f, 0.0f);
	drawSolidCylinder(0.4f, 5.0f, 10, 1);
	glPopMatrix();

	glPushMatrix(); glTranslatef(0.0f, 2.5f, 0.0f); glRotatef(45.0f, 0.0f, 1.0f, 0.0f); glRotatef(-45.0f, 1.0f, 0.0f, 0.0f); drawSolidCylinder(0.15f, 2.5f, 8, 1); glPopMatrix();
	glPushMatrix(); glTranslatef(0.0f, 3.2f, 0.0f); glRotatef(-60.0f, 0.0f, 1.0f, 0.0f); glRotatef(-30.0f, 1.0f, 0.0f, 0.0f); drawSolidCylinder(0.12f, 2.0f, 8, 1); glPopMatrix();
	glPushMatrix(); glTranslatef(0.0f, 4.0f, 0.0f); glRotatef(120.0f, 0.0f, 1.0f, 0.0f); glRotatef(-50.0f, 1.0f, 0.0f, 0.0f); drawSolidCylinder(0.1f, 1.8f, 8, 1); glPopMatrix();
	glPushMatrix(); glTranslatef(0.0f, 1.8f, 0.0f); glRotatef(180.0f, 0.0f, 1.0f, 0.0f); glRotatef(-40.0f, 1.0f, 0.0f, 0.0f); drawSolidCylinder(0.18f, 2.2f, 8, 1); glPopMatrix();

	glPopMatrix();
}

static void renderObstacles() {
	for (int oi = 0; oi < (int)g_obstacles.size(); ++oi) {
		const Obstacle& ob = g_obstacles[oi];

		if (ob.type == 1) {
			renderDeadTree(ob);
		}
		else {
			glPushMatrix();
			glTranslatef(ob.pos.x, ob.pos.y, ob.pos.z);

			glColor3f(0.45f, 0.45f, 0.48f);
			drawBox(ob.hw, ob.hh, ob.hd);

			glTranslatef(0.0f, ob.hh, 0.0f);
			glScalef(ob.hw, ob.hw, ob.hd);
			glutSolidSphere(1.0, 10, 10);

			glPopMatrix();
		}
	}
}

static void drawBloodDrip(float lx, float ly, float lz, float size) {
	glDisable(GL_LIGHTING); glColor3f(0.55f, 0.0f, 0.0f); glBegin(GL_TRIANGLES);
	glVertex3f(lx, ly + size, lz); glVertex3f(lx - size * 0.5f, ly - size * 0.5f, lz); glVertex3f(lx + size * 0.5f, ly - size * 0.5f, lz);
	glVertex3f(lx - 0.03f, ly - size * 0.5f, lz); glVertex3f(lx + 0.03f, ly - size * 0.5f, lz); glVertex3f(lx, ly - size * 1.6f, lz);
	glEnd(); glEnable(GL_LIGHTING);
}

static void renderZombies() {
	for (int zi = 0; zi < (int)g_zombies.size(); ++zi) {
		const Zombie& zz = g_zombies[zi];
		if (!zz.alive) continue;

		float dx = g_playerPos.x - zz.pos.x;
		float ddz = g_playerPos.z - zz.pos.z;
		float ang = atan2f(dx, ddz) * (180.0f / MY_PI);

		float phase = g_gameTime * (1.8f * zz.spdMult) + zz.walkPhase;

		float sway = sinf(phase);
		float stepL = sinf(phase);
		float stepR = -sinf(phase);
		float bob = fabsf(sinf(phase)) * 0.04f;
		float armFwd = 55.0f + sinf(phase * 0.5f) * 20.0f;

		glPushMatrix();
		glTranslatef(zz.pos.x, bob * zz.scale, zz.pos.z);
		glRotatef(ang, 0.0f, 1.0f, 0.0f);
		glRotatef(sway * 6.0f, 0.0f, 0.0f, 1.0f);

		glScalef(zz.scale, zz.scale, zz.scale);

		/* BODY */
		glColor3f(zz.r, zz.g, zz.b);
		glPushMatrix(); glTranslatef(0.0f, 0.9f, 0.0f); drawBox(0.35f, 0.45f, 0.25f); glPopMatrix();
		glPushMatrix(); glTranslatef(0.0f, 0.9f, 0.251f);
		drawBloodDrip(0.08f, 0.15f, 0.0f, 0.07f); drawBloodDrip(-0.10f, 0.05f, 0.0f, 0.055f); drawBloodDrip(0.00f, -0.10f, 0.0f, 0.06f);
		glPopMatrix();

		/* NECK */
		glColor3f(zz.r * 0.8f, zz.g * 0.8f, zz.b * 0.8f);
		glPushMatrix(); glTranslatef(0.0f, 1.40f, 0.0f); drawBox(0.12f, 0.08f, 0.10f); glPopMatrix();

		/* HEAD */
		glPushMatrix();
		glTranslatef(0.0f, 1.65f, 0.0f);
		glRotatef(sinf(phase * 0.4f) * 8.0f, 0.0f, 0.0f, 1.0f);
		glRotatef(-15.0f, 1.0f, 0.0f, 0.0f);

		glColor3f(zz.r * 1.1f, zz.g * 1.1f, zz.b * 1.1f);
		drawBox(0.22f, 0.22f, 0.22f);

		glDisable(GL_LIGHTING);
		glColor3f(0.05f, 0.0f, 0.0f);
		glPushMatrix(); glTranslatef(-0.09f, 0.06f, 0.221f); drawBox(0.055f, 0.045f, 0.005f); glPopMatrix();
		glColor3f(0.85f, 0.05f, 0.0f);
		glPushMatrix(); glTranslatef(-0.09f, 0.06f, 0.227f); drawBox(0.030f, 0.025f, 0.005f); glPopMatrix();
		glColor3f(0.05f, 0.0f, 0.0f);
		glPushMatrix(); glTranslatef(0.09f, 0.06f, 0.221f); drawBox(0.055f, 0.045f, 0.005f); glPopMatrix();
		glColor3f(0.85f, 0.05f, 0.0f);
		glPushMatrix(); glTranslatef(0.09f, 0.06f, 0.227f); drawBox(0.030f, 0.025f, 0.005f); glPopMatrix();
		glEnable(GL_LIGHTING);

		glColor3f(zz.r * 0.9f, zz.g * 0.9f, zz.b * 0.9f);
		glPushMatrix(); glTranslatef(0.0f, -0.13f, 0.10f); drawBox(0.14f, 0.06f, 0.13f); glPopMatrix();

		glDisable(GL_LIGHTING); glColor3f(0.92f, 0.90f, 0.85f); glBegin(GL_TRIANGLES);
		glVertex3f(-0.06f, -0.07f, 0.225f); glVertex3f(-0.03f, -0.05f, 0.220f); glVertex3f(-0.09f, -0.05f, 0.220f);
		glVertex3f(0.06f, -0.07f, 0.225f); glVertex3f(0.03f, -0.05f, 0.220f); glVertex3f(0.09f, -0.05f, 0.220f);
		glEnd(); glColor3f(0.60f, 0.0f, 0.0f); glLineWidth(1.5f); glBegin(GL_LINES);
		glVertex3f(-0.06f, -0.07f, 0.226f); glVertex3f(-0.06f, -0.14f, 0.224f);
		glVertex3f(0.06f, -0.07f, 0.226f); glVertex3f(0.06f, -0.14f, 0.224f);
		glEnd(); glLineWidth(1.0f); glEnable(GL_LIGHTING);

		glPushMatrix(); glTranslatef(0.0f, 0.0f, 0.222f);
		drawBloodDrip(0.12f, 0.10f, 0.0f, 0.045f); drawBloodDrip(-0.05f, 0.14f, 0.0f, 0.040f);
		glPopMatrix(); glPopMatrix();

		/* ARMS */
		glColor3f(zz.r, zz.g, zz.b);
		glPushMatrix(); glTranslatef(-0.40f, 1.15f, 0.0f); glRotatef(-armFwd + stepL * 20.0f, 1.0f, 0.0f, 0.0f); glRotatef(20.0f, 0.0f, 0.0f, 1.0f);
		drawBox(0.10f, 0.38f, 0.09f);
		glPushMatrix(); glTranslatef(0.0f, -0.38f, 0.0f); glRotatef(stepL * 15.0f - 30.0f, 1.0f, 0.0f, 0.0f); drawBox(0.075f, 0.28f, 0.075f);
		glDisable(GL_LIGHTING); glColor3f(0.22f, 0.12f, 0.08f);
		for (int c = -1; c <= 1; ++c) { glPushMatrix(); glTranslatef(c * 0.06f, -0.32f, 0.0f); glScalef(0.04f, 0.12f, 0.04f); glutSolidCone(1.0, 1.0, 4, 1); glPopMatrix(); }
		glEnable(GL_LIGHTING); glPopMatrix(); glPopMatrix();

		glPushMatrix(); glTranslatef(0.40f, 1.15f, 0.0f); glRotatef(-armFwd + stepR * 20.0f, 1.0f, 0.0f, 0.0f); glRotatef(-20.0f, 0.0f, 0.0f, 1.0f);
		drawBox(0.10f, 0.38f, 0.09f);
		glPushMatrix(); glTranslatef(0.0f, -0.38f, 0.0f); glRotatef(stepR * 15.0f - 30.0f, 1.0f, 0.0f, 0.0f); drawBox(0.075f, 0.28f, 0.075f);
		glDisable(GL_LIGHTING); glColor3f(0.22f, 0.12f, 0.08f);
		for (int c = -1; c <= 1; ++c) { glPushMatrix(); glTranslatef(c * 0.06f, -0.32f, 0.0f); glScalef(0.04f, 0.12f, 0.04f); glutSolidCone(1.0, 1.0, 4, 1); glPopMatrix(); }
		glEnable(GL_LIGHTING); glPopMatrix(); glPopMatrix();

		/* LEGS */
		glColor3f(zz.r * 0.7f, zz.g * 0.7f, zz.b * 0.7f);
		glPushMatrix(); glTranslatef(-0.17f, 0.50f, 0.0f); glRotatef(stepL * 22.0f, 1.0f, 0.0f, 0.0f); drawBox(0.12f, 0.28f, 0.11f);
		glPushMatrix(); glTranslatef(0.0f, -0.28f, 0.0f); glRotatef(fabsf(stepL) * 18.0f, 1.0f, 0.0f, 0.0f); drawBox(0.10f, 0.22f, 0.09f); glPopMatrix(); glPopMatrix();
		glPushMatrix(); glTranslatef(0.17f, 0.50f, 0.0f); glRotatef(stepR * 22.0f, 1.0f, 0.0f, 0.0f); drawBox(0.12f, 0.28f, 0.11f);
		glPushMatrix(); glTranslatef(0.0f, -0.28f, 0.0f); glRotatef(fabsf(stepR) * 18.0f, 1.0f, 0.0f, 0.0f); drawBox(0.10f, 0.22f, 0.09f); glPopMatrix(); glPopMatrix();

		/* BLOOD POOL */
		glDisable(GL_LIGHTING); glDisable(GL_DEPTH_TEST); glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glColor4f(0.45f, 0.0f, 0.0f, 0.55f); glBegin(GL_TRIANGLE_FAN); glVertex3f(0.0f, 0.01f, 0.0f);
		for (int si = 0; si <= 12; ++si) {
			float a = (float)si / 12.0f * 2.0f * MY_PI;
			float r = 0.32f + 0.10f * sinf(a * 3.0f + zz.walkPhase);
			glVertex3f(cosf(a) * r, 0.01f, sinf(a) * r);
		}
		glEnd(); glDisable(GL_BLEND); glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING);

		glPopMatrix();
	}
}

static void renderBullets() {
	glColor3f(1.0f, 0.9f, 0.2f);
	for (int bi = 0; bi < (int)g_bullets.size(); ++bi) {
		if (!g_bullets[bi].alive) continue;
		glPushMatrix(); glTranslatef(g_bullets[bi].pos.x, g_bullets[bi].pos.y, g_bullets[bi].pos.z);
		glutSolidSphere((double)BULLET_RADIUS, 8, 8); glPopMatrix();
	}
}

static void renderBloodParticles() {
	if (g_blood.empty()) return;
	glDisable(GL_LIGHTING); glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	for (int bi = 0; bi < (int)g_blood.size(); ++bi) {
		if (!g_blood[bi].alive) continue;
		float t = g_blood[bi].life / g_blood[bi].maxLife;
		float alpha = t * 0.92f; float sz = 0.05f + 0.04f * t;
		if (g_blood[bi].vel.x == 0.0f && g_blood[bi].vel.y == 0.0f && g_blood[bi].vel.z == 0.0f) {
			glColor4f(0.35f, 0.0f, 0.0f, alpha * 0.8f); glBegin(GL_TRIANGLE_FAN); glVertex3f(g_blood[bi].pos.x, 0.015f, g_blood[bi].pos.z);
			for (int k = 0; k <= 8; ++k) {
				float a = (float)k / 8.0f * 2.0f * MY_PI;
				glVertex3f(g_blood[bi].pos.x + cosf(a) * sz * 2.0f, 0.015f, g_blood[bi].pos.z + sinf(a) * sz * 2.0f);
			}
			glEnd();
		}
		else {
			glColor4f(0.75f, 0.02f, 0.02f, alpha); glPushMatrix(); glTranslatef(g_blood[bi].pos.x, g_blood[bi].pos.y, g_blood[bi].pos.z);
			glutSolidSphere((double)sz, 6, 4); glPopMatrix();
		}
	}
	glDisable(GL_BLEND); glEnable(GL_LIGHTING);
}

static void renderMuzzleFlash3D() {
	if (!g_muzzleOn) return;
	float yR = g_yaw * DEG2RAD; float pR = g_pitch * DEG2RAD;
	Vec3 fwd(cosf(pR) * sinf(yR), sinf(pR), cosf(pR) * (-cosf(yR)));
	Vec3 right(cosf(yR), 0.0f, sinf(yR)); Vec3 up(0.0f, 1.0f, 0.0f);
	Vec3 tip = g_playerPos + fwd * 0.6f + right * 0.35f + up * (-0.25f);

	glDisable(GL_LIGHTING); glDisable(GL_DEPTH_TEST);
	float t = g_muzzleTimer / 0.08f; float alpha = t * 0.95f;
	glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE);

	float rad = (g_weapon == 1 ? 0.35f : 0.22f) + 0.08f * t;
	glColor4f(1.0f, 0.65f, 0.10f, alpha * 0.55f); glPushMatrix(); glTranslatef(tip.x, tip.y, tip.z);
	float camX = g_playerPos.x - tip.x; float camZ = g_playerPos.z - tip.z;
	float ang = atan2f(camX, camZ) * (180.0f / MY_PI); glRotatef(ang, 0.0f, 1.0f, 0.0f);
	glBegin(GL_TRIANGLE_FAN); glVertex3f(0.0f, 0.0f, 0.0f);
	for (int i = 0; i <= 16; ++i) { float a = (float)i / 16.0f * 2.0f * MY_PI; glVertex3f(cosf(a) * rad, sinf(a) * rad, 0.0f); }
	glEnd(); glPopMatrix();

	glColor4f(1.0f, 0.95f, 0.70f, alpha); glPushMatrix(); glTranslatef(tip.x, tip.y, tip.z); glRotatef(ang, 0.0f, 1.0f, 0.0f);
	float cr = rad * 0.35f; glBegin(GL_TRIANGLE_FAN); glVertex3f(0, 0, 0);
	for (int i = 0; i <= 10; ++i) { float a = (float)i / 10.0f * 2.0f * MY_PI; glVertex3f(cosf(a) * cr, sinf(a) * cr, 0.0f); }
	glEnd(); glPopMatrix();

	glColor4f(1.0f, 0.80f, 0.20f, alpha * 0.8f); glLineWidth(2.5f); glPushMatrix(); glTranslatef(tip.x, tip.y, tip.z); glRotatef(ang, 0.0f, 1.0f, 0.0f);
	float sp = rad * 1.6f; glBegin(GL_LINES);
	for (int i = 0; i < 8; ++i) { float a = (float)i / 8.0f * 2.0f * MY_PI; glVertex3f(0.0f, 0.0f, 0.0f); glVertex3f(cosf(a) * sp, sinf(a) * sp, 0.0f); }
	glEnd(); glPopMatrix(); glLineWidth(1.0f);

	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA); glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING); glDisable(GL_BLEND);
}

static void renderWeapon() {
	glMatrixMode(GL_PROJECTION); glPushMatrix(); glMatrixMode(GL_MODELVIEW); glPushMatrix();
	glLoadIdentity(); glClear(GL_DEPTH_BUFFER_BIT);

	float recoil = 0.0f;
	if (g_muzzleOn) recoil = (g_muzzleTimer / 0.08f) * (g_weapon == 1 ? 0.15f : 0.08f);

	float reloadDrop = 0.0f;
	if (g_reloading) {
		reloadDrop = sinf((g_reloadTimer / 1.5f) * MY_PI) * 0.4f;
	}

	glTranslatef(0.35f, -0.25f - reloadDrop, -0.45f + recoil);

	if (g_weapon == 0) {
		glColor3f(0.25f, 0.25f, 0.28f); drawBox(0.02f, 0.025f, 0.15f);
		glPushMatrix(); glTranslatef(0.0f, -0.02f, 0.15f); drawBox(0.03f, 0.04f, 0.1f); glPopMatrix();
		glColor3f(0.2f, 0.15f, 0.1f); glPushMatrix(); glTranslatef(0.0f, -0.1f, 0.2f); glRotatef(15.0f, 1.0f, 0.0f, 0.0f); drawBox(0.02f, 0.06f, 0.03f); glPopMatrix();
		glColor3f(0.5f, 0.5f, 0.5f); glPushMatrix(); glTranslatef(0.0f, 0.03f, -0.1f); drawBox(0.003f, 0.008f, 0.003f); glPopMatrix();
	}
	else {
		glColor3f(0.15f, 0.15f, 0.15f);
		glPushMatrix(); glTranslatef(-0.015f, 0.0f, -0.1f); drawBox(0.015f, 0.015f, 0.35f); glPopMatrix();
		glPushMatrix(); glTranslatef(0.015f, 0.0f, -0.1f); drawBox(0.015f, 0.015f, 0.35f); glPopMatrix();
		glColor3f(0.3f, 0.2f, 0.1f);
		glPushMatrix(); glTranslatef(0.0f, -0.03f, 0.15f); drawBox(0.04f, 0.05f, 0.15f); glPopMatrix();
		glPushMatrix(); glTranslatef(0.0f, -0.12f, 0.28f); glRotatef(25.0f, 1.0f, 0.0f, 0.0f); drawBox(0.025f, 0.08f, 0.04f); glPopMatrix();
	}

	glPopMatrix(); glMatrixMode(GL_PROJECTION); glPopMatrix(); glMatrixMode(GL_MODELVIEW);
}

static void renderHUD() {
	glMatrixMode(GL_PROJECTION); glPushMatrix(); glLoadIdentity(); gluOrtho2D(0, WIN_W, 0, WIN_H);
	glMatrixMode(GL_MODELVIEW); glPushMatrix(); glLoadIdentity();
	glDisable(GL_DEPTH_TEST); glDisable(GL_LIGHTING);

	if (g_muzzleOn) {
		float t = g_muzzleTimer / 0.08f; glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
		glColor4f(1.0f, 0.75f, 0.15f, t * 0.35f); glBegin(GL_QUADS);
		glVertex2f(0.0f, 0.0f); glVertex2f((float)WIN_W, 0.0f); glVertex2f((float)WIN_W, (float)WIN_H); glVertex2f(0.0f, (float)WIN_H);
		glEnd(); glDisable(GL_BLEND);
	}

	/* Health */
	glColor4f(0.15f, 0.15f, 0.15f, 0.7f); glBegin(GL_QUADS);
	glVertex2f(20.0f, 20.0f); glVertex2f(220.0f, 20.0f); glVertex2f(220.0f, 38.0f); glVertex2f(20.0f, 38.0f); glEnd();
	float hPct = g_playerHealth / (float)MAX_HEALTH_INT;
	glColor4f(1.0f - hPct, hPct * 0.8f, 0.1f, 0.9f); glBegin(GL_QUADS);
	glVertex2f(21.0f, 21.0f); glVertex2f(21.0f + 198.0f * hPct, 21.0f); glVertex2f(21.0f + 198.0f * hPct, 37.0f); glVertex2f(21.0f, 37.0f); glEnd();
	drawText2D("HP: " + std::to_string((int)g_playerHealth), 25.0f, 23.0f, 1, 1, 1);

	/* Ammo & Weapon Info */
	std::string wpnName = (g_weapon == 0) ? "PISTOL" : "SHOTGUN";
	std::string ammoText = "Ammo: " + std::to_string(g_ammo[g_weapon]) + " / " + std::to_string(g_magCapacity[g_weapon]);
	drawText2D(wpnName, 20.0f, 70.0f, 0.8f, 0.8f, 1.0f);
	if (g_reloading) {
		drawText2D("RELOADING...", 20.0f, 50.0f, 1.0f, 0.2f, 0.2f);
	}
	else if (g_ammo[g_weapon] == 0) {
		drawText2D("PRESS 'R' TO RELOAD", 20.0f, 50.0f, 1.0f, 0.0f, 0.0f);
	}
	else {
		drawText2D(ammoText, 20.0f, 50.0f, 1.0f, 1.0f, 0.2f);
	}

	float tx = (float)(WIN_W - 180);
	drawText2D("Score:   " + std::to_string(g_score), tx, (float)(WIN_H - 30), 1.0f, 1.0f, 0.3f);
	drawText2D("Wave:    " + std::to_string(g_wave), tx, (float)(WIN_H - 55), 0.6f, 1.0f, 0.6f);
	drawText2D("Zombies: " + std::to_string(g_zombiesLeft), tx, (float)(WIN_H - 80), 1.0f, 0.5f, 0.5f);

	/* Crosshair */
	glColor3f(1.0f, 1.0f, 1.0f);
	float cx = (float)(WIN_W / 2); float cy = (float)(WIN_H / 2); float sz = 12.0f, gap = 4.0f;
	glLineWidth(1.5f); glBegin(GL_LINES);
	glVertex2f(cx - sz, cy); glVertex2f(cx - gap, cy); glVertex2f(cx + gap, cy); glVertex2f(cx + sz, cy);
	glVertex2f(cx, cy - sz); glVertex2f(cx, cy - gap); glVertex2f(cx, cy + gap); glVertex2f(cx, cy + sz);
	glEnd(); glLineWidth(1.0f);

	if (g_waveClear) drawText2D("Wave " + std::to_string(g_wave - 1) + " cleared!  Next wave incoming...", (float)(WIN_W / 2 - 185), (float)(WIN_H / 2 + 50), 0.3f, 1.0f, 0.5f);

	glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING);
	glMatrixMode(GL_PROJECTION); glPopMatrix(); glMatrixMode(GL_MODELVIEW); glPopMatrix();
}

static void renderGameOver() {
	glMatrixMode(GL_PROJECTION); glPushMatrix(); glLoadIdentity(); gluOrtho2D(0, WIN_W, 0, WIN_H);
	glMatrixMode(GL_MODELVIEW); glPushMatrix(); glLoadIdentity(); glDisable(GL_DEPTH_TEST); glDisable(GL_LIGHTING);
	glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glColor4f(0.0f, 0.0f, 0.0f, 0.78f); glBegin(GL_QUADS);
	glVertex2f(0.0f, 0.0f); glVertex2f((float)WIN_W, 0.0f); glVertex2f((float)WIN_W, (float)WIN_H); glVertex2f(0.0f, (float)WIN_H);
	glEnd(); glDisable(GL_BLEND);
	float ocx = (float)(WIN_W / 2); float ocy = (float)(WIN_H / 2);
	glColor3f(0.9f, 0.1f, 0.1f); glRasterPos2f(ocx - 100.0f, ocy + 40.0f);
	const char* gtxt = "G A M E   O V E R"; for (const char* cp = gtxt; *cp; ++cp) glutBitmapCharacter(GLUT_BITMAP_TIMES_ROMAN_24, (int)*cp);
	drawText2D("Score:        " + std::to_string(g_score), ocx - 90.0f, ocy, 1, 1, 0.3f);
	drawText2D("Wave reached: " + std::to_string(g_wave), ocx - 90.0f, ocy - 30.0f, 0.7f, 1.0f, 0.7f);
	drawText2D("Press  R  to restart   Esc  to quit", ocx - 165.0f, ocy - 80.0f, 0.8f, 0.8f, 0.8f);
	glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING);
	glMatrixMode(GL_PROJECTION); glPopMatrix(); glMatrixMode(GL_MODELVIEW); glPopMatrix();
}

/* ===========================================================================
   Shooting System
   =========================================================================== */
static void shoot() {
	if (g_gameOver || g_reloading || g_fireCooldown > 0.0f) return;
	if (g_ammo[g_weapon] <= 0) return;

	g_ammo[g_weapon]--;
	float yR = g_yaw * DEG2RAD;
	float pR = g_pitch * DEG2RAD;

	if (g_weapon == 0) {
		Bullet bl;
		bl.pos = g_playerPos;
		bl.dir = Vec3(cosf(pR) * sinf(yR), sinf(pR), cosf(pR) * (-cosf(yR))).normalized();
		bl.alive = true;
		bl.distTravelled = 0.0f;
		bl.damage = 50.0f;
		g_bullets.push_back(bl);
		g_fireCooldown = 0.1f;
	}
	else {
		for (int i = 0; i < 5; ++i) {
			float spreadY = g_randf(-0.06f, 0.06f);
			float spreadP = g_randf(-0.06f, 0.06f);
			Bullet bl;
			bl.pos = g_playerPos;
			bl.dir = Vec3(cosf(pR + spreadP) * sinf(yR + spreadY), sinf(pR + spreadP), cosf(pR + spreadP) * (-cosf(yR + spreadY))).normalized();
			bl.alive = true;
			bl.distTravelled = 0.0f;
			bl.damage = 35.0f;
			g_bullets.push_back(bl);
		}
		g_fireCooldown = 0.7f;
	}

	g_muzzleOn = true;
	g_muzzleTimer = 0.08f;
}

static void reloadWeapon() {
	if (g_gameOver || g_reloading || g_ammo[g_weapon] == g_magCapacity[g_weapon]) return;
	g_reloading = true;
	g_reloadTimer = (g_weapon == 0) ? 1.5f : 2.0f;
}

static void switchWeapon() {
	if (g_gameOver) return;
	g_weapon = (g_weapon == 0) ? 1 : 0;
	g_reloading = false;
	g_fireCooldown = 0.2f;
}

/* ===========================================================================
   Game Loop
   =========================================================================== */
static void updateGame(float dt) {
	if (g_gameOver) return;
	g_gameTime += dt;

	if (g_fireCooldown > 0.0f) g_fireCooldown -= dt;

	if (g_reloading) {
		g_reloadTimer -= dt;
		if (g_reloadTimer <= 0.0f) {
			g_ammo[g_weapon] = g_magCapacity[g_weapon];
			g_reloading = false;
		}
	}

	if (g_muzzleOn) {
		g_muzzleTimer -= dt;
		if (g_muzzleTimer <= 0.0f) g_muzzleOn = false;
	}

	if (g_waveClear) {
		g_waveClearTimer -= dt;
		if (g_waveClearTimer <= 0.0f) {
			g_waveClear = false;
			spawnWave();
		}
		return;
	}

	float yR = g_yaw * DEG2RAD;
	Vec3 fwd(sinf(yR), 0.0f, -cosf(yR)); Vec3 rgt(cosf(yR), 0.0f, sinf(yR)); Vec3 move;
	if (g_keys[(unsigned char)'w'] || g_keys[(unsigned char)'W']) move = move + fwd;
	if (g_keys[(unsigned char)'s'] || g_keys[(unsigned char)'S']) move = move - fwd;
	if (g_keys[(unsigned char)'a'] || g_keys[(unsigned char)'A']) move = move - rgt;
	if (g_keys[(unsigned char)'d'] || g_keys[(unsigned char)'D']) move = move + rgt;
	float ml = move.length();
	if (ml > 0.001f) {
		move = move * (1.0f / ml);
		Vec3 desired = g_playerPos + move * PLAYER_SPEED * dt * 60.0f;
		desired.y = PLAYER_HEIGHT;
		g_playerPos = resolveCollisions(desired, PLAYER_RADIUS);
		g_playerPos.y = PLAYER_HEIGHT;
	}

	for (int bi = 0; bi < (int)g_bullets.size(); ++bi) {
		Bullet& bl = g_bullets[bi];
		if (!bl.alive) continue;
		bl.pos = bl.pos + bl.dir * BULLET_SPEED;
		bl.distTravelled += BULLET_SPEED;
		if (bl.distTravelled > BULLET_MAX_DIST || fabsf(bl.pos.x) > ARENA_HALF || fabsf(bl.pos.z) > ARENA_HALF) { bl.alive = false; continue; }

		bool hitObs = false;
		for (int oi = 0; oi < (int)g_obstacles.size(); ++oi)
			if (sphereVsBox(bl.pos, BULLET_RADIUS, g_obstacles[oi])) { hitObs = true; break; }
		if (hitObs) { bl.alive = false; continue; }

		for (int zi = 0; zi < (int)g_zombies.size(); ++zi) {
			Zombie& zz = g_zombies[zi];
			if (!zz.alive) continue;
			Vec3 diff = bl.pos - Vec3(zz.pos.x, 1.0f * zz.scale, zz.pos.z);
			if (diff.length() < (ZOMBIE_RADIUS * zz.scale) + BULLET_RADIUS) {
				zz.health -= bl.damage;
				bl.alive = false;
				{
					Vec3 hitPt(zz.pos.x, 1.0f * zz.scale, zz.pos.z);
					int  count = 6 + rand() % 5;
					for (int p = 0; p < count; ++p) {
						BloodParticle bp; bp.pos = hitPt;
						bp.vel = Vec3(g_randf(-3.0f, 3.0f), g_randf(1.5f, 5.0f), g_randf(-3.0f, 3.0f));
						bp.maxLife = g_randf(0.35f, 0.70f); bp.life = bp.maxLife; bp.alive = true; g_blood.push_back(bp);
					}
				}
				if (zz.health <= 0.0f) {
					zz.alive = false;
					g_score += (zz.type == 2) ? 50 : ((zz.type == 1) ? 20 : 10);
					g_zombiesLeft--;
					{
						Vec3 hitPt(zz.pos.x, 0.8f * zz.scale, zz.pos.z);
						for (int p = 0; p < 20; ++p) {
							BloodParticle bp; bp.pos = hitPt;
							bp.vel = Vec3(g_randf(-4.0f, 4.0f), g_randf(2.0f, 6.0f), g_randf(-4.0f, 4.0f));
							bp.maxLife = g_randf(0.5f, 1.0f); bp.life = bp.maxLife; bp.alive = true; g_blood.push_back(bp);
						}
					}
				}
				break;
			}
		}
	}

	float baseZspd = ZOMBIE_SPEED_BASE + ZOMBIE_SPEED_INC * (float)(g_wave - 1);
	int aliveCount = 0;
	for (int zi = 0; zi < (int)g_zombies.size(); ++zi) {
		Zombie& zz = g_zombies[zi];
		if (!zz.alive) continue;
		++aliveCount;

		zz.hitCooldown -= dt;
		if (zz.hitCooldown < 0.0f) zz.hitCooldown = 0.0f;

		float zspd = baseZspd * zz.spdMult;
		float zRadius = ZOMBIE_RADIUS * zz.scale;

		Vec3 toP = Vec3(g_playerPos.x, 0.0f, g_playerPos.z) - Vec3(zz.pos.x, 0.0f, zz.pos.z);
		float dist = toP.length();
		if (dist > 0.1f) {
			Vec3 dir = toP * (1.0f / dist);
			Vec3 desired = zz.pos + dir * zspd;
			Vec3 newPos = resolveCollisions(desired, zRadius);

			float movedSq = (newPos.x - zz.pos.x) * (newPos.x - zz.pos.x) + (newPos.z - zz.pos.z) * (newPos.z - zz.pos.z);
			if (movedSq < (zspd * 0.5f) * (zspd * 0.5f)) {
				float sign = (fmod(zz.walkPhase, 2.0f) > 1.0f) ? 1.0f : -1.0f;
				Vec3 slideDir(-dir.z * sign, 0.0f, dir.x * sign);
				Vec3 slideDesired = zz.pos + (dir + slideDir * 2.0f).normalized() * zspd;
				newPos = resolveCollisions(slideDesired, zRadius);
			}
			zz.pos = newPos; zz.pos.y = 0.0f;
		}

		Vec3 diff = g_playerPos - Vec3(zz.pos.x, PLAYER_HEIGHT, zz.pos.z);
		if (diff.length() < PLAYER_RADIUS + zRadius && zz.hitCooldown <= 0.0f) {
			g_playerHealth -= zz.damage;
			zz.hitCooldown = HIT_COOLDOWN;

			if (g_playerHealth <= 0.0f) {
				g_playerHealth = 0.0f;
				g_gameOver = true;
				return;
			}
		}
	}

	if (aliveCount == 0 && !g_waveClear) {
		g_waveClear = true;
		g_waveClearTimer = WAVE_PAUSE_SEC;
		g_wave++;
		g_zombiesThisWave = 5 + (g_wave - 1) * 3;
	}

	for (int bi = 0; bi < (int)g_blood.size(); ++bi) {
		BloodParticle& bp = g_blood[bi];
		if (!bp.alive) continue;
		bp.vel.y -= 9.8f * dt;
		bp.pos = bp.pos + bp.vel * dt;
		if (bp.pos.y < 0.01f) { bp.pos.y = 0.01f; bp.vel = Vec3(0, 0, 0); }
		bp.life -= dt;
		if (bp.life <= 0.0f) bp.alive = false;
	}

	{ std::vector<Bullet> nb; nb.reserve(g_bullets.size()); for (int bi = 0; bi < (int)g_bullets.size(); ++bi) if (g_bullets[bi].alive) nb.push_back(g_bullets[bi]); g_bullets.swap(nb); }
	{ std::vector<Zombie> nz; nz.reserve(g_zombies.size()); for (int zi = 0; zi < (int)g_zombies.size(); ++zi) if (g_zombies[zi].alive) nz.push_back(g_zombies[zi]); g_zombies.swap(nz); }
	{ std::vector<BloodParticle> nb; nb.reserve(g_blood.size()); for (int bi = 0; bi < (int)g_blood.size(); ++bi) if (g_blood[bi].alive) nb.push_back(g_blood[bi]); g_blood.swap(nb); }
}

/* ===========================================================================
   GLUT Callbacks
   =========================================================================== */
static void display() {
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	glMatrixMode(GL_PROJECTION); glLoadIdentity(); gluPerspective(70.0, (double)WIN_W / (double)WIN_H, 0.05, 200.0);
	glMatrixMode(GL_MODELVIEW); glLoadIdentity();

	float yR = g_yaw * DEG2RAD; float pR = g_pitch * DEG2RAD;
	Vec3 lookDir(cosf(pR) * sinf(yR), sinf(pR), cosf(pR) * (-cosf(yR)));

	Vec3 eye = g_playerPos;
	Vec3 target = g_playerPos + lookDir;

	gluLookAt((double)eye.x, (double)eye.y, (double)eye.z, (double)target.x, (double)target.y, (double)target.z, 0.0, 1.0, 0.0);

	// إضاءة القمر الدموي
	GLfloat la[4] = { 0.40f, 0.15f, 0.15f, 1.0f };
	GLfloat ld[4] = { 0.85f, 0.30f, 0.20f, 1.0f };
	GLfloat lp[4] = { -70.0f, 45.0f, -120.0f, 1.0f };
	glLightfv(GL_LIGHT0, GL_AMBIENT, la); glLightfv(GL_LIGHT0, GL_DIFFUSE, ld); glLightfv(GL_LIGHT0, GL_POSITION, lp);

	renderSky(); renderGround(); renderArenaWalls(); renderObstacles(); renderZombies(); renderBullets(); renderBloodParticles(); renderMuzzleFlash3D();
	renderWeapon(); renderHUD(); if (g_gameOver) renderGameOver();

	glutSwapBuffers();
}

static void reshape(int w, int h) { glViewport(0, 0, w, h); }

static void idle() {
	int now = glutGet(GLUT_ELAPSED_TIME); float dt = (float)(now - g_lastTime) / 1000.0f; g_lastTime = now;
	if (dt > 0.05f) dt = 0.05f; updateGame(dt); glutPostRedisplay();
}

static void keyDown(unsigned char key, int /*x*/, int /*y*/) {
	if (key == 27) exit(0);
	g_keys[key] = true;
	if (key == ' ') shoot();
	if ((key == 'r' || key == 'R')) {
		if (g_gameOver) resetGame(); else reloadWeapon();
	}
	if (key == 'q' || key == 'Q') switchWeapon();
}

static void keyUp(unsigned char key, int /*x*/, int /*y*/) { g_keys[key] = false; }

static void mouseButton(int button, int action, int /*x*/, int /*y*/) {
	if (button == GLUT_LEFT_BUTTON && action == GLUT_DOWN) shoot();
}

static void mouseMotion(int mx, int my) {
	if (g_warping) { g_warping = false; return; }
	int cx = glutGet(GLUT_WINDOW_WIDTH) / 2; int cy = glutGet(GLUT_WINDOW_HEIGHT) / 2;
	int dx = mx - cx; int dy = my - cy;
	if (dx == 0 && dy == 0) return;
	g_yaw += (float)dx * MOUSE_SENS_F; g_pitch -= (float)dy * MOUSE_SENS_F;
	if (g_pitch > 89.0f) g_pitch = 89.0f; if (g_pitch < -89.0f) g_pitch = -89.0f;
	if (g_yaw < 0.0f) g_yaw += 360.0f; if (g_yaw >= 360.0f) g_yaw -= 360.0f;
	g_warping = true; glutWarpPointer(cx, cy); glutPostRedisplay();
}

/* ===========================================================================
   Entry Point
   =========================================================================== */
int main(int argc, char** argv) {
	srand((unsigned int)time(NULL));
	glutInit(&argc, argv); glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH); glutInitWindowSize(WIN_W, WIN_H);
	glutCreateWindow("Zombie Wave Shooter 3D (Graveyard)");

	glEnable(GL_DEPTH_TEST); glEnable(GL_LIGHTING); glEnable(GL_LIGHT0); glEnable(GL_COLOR_MATERIAL);
	glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE); glShadeModel(GL_SMOOTH);
	glEnable(GL_BLEND); glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

	glClearColor(0.02f, 0.02f, 0.02f, 1.0f);

	glutDisplayFunc(display); glutReshapeFunc(reshape); glutIdleFunc(idle);
	glutKeyboardFunc(keyDown); glutKeyboardUpFunc(keyUp); glutMouseFunc(mouseButton);
	glutPassiveMotionFunc(mouseMotion); glutMotionFunc(mouseMotion);

	g_lastTime = glutGet(GLUT_ELAPSED_TIME); resetGame();

	glutSetCursor(GLUT_CURSOR_NONE); g_warping = true; glutWarpPointer(WIN_W / 2, WIN_H / 2);

	groundTexture = loadTexture("C:/Solar System/Solar System Project/x64/Debug/ground.jpg");

	glutMainLoop();
	return 0;
}