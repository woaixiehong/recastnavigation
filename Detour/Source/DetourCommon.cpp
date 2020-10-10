//
// Copyright (c) 2009-2010 Mikko Mononen memon@inside.org
//
// This software is provided 'as-is', without any express or implied
// warranty.  In no event will the authors be held liable for any damages
// arising from the use of this software.
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it
// freely, subject to the following restrictions:
// 1. The origin of this software must not be misrepresented; you must not
//    claim that you wrote the original software. If you use this software
//    in a product, an acknowledgment in the product documentation would be
//    appreciated but is not required.
// 2. Altered source versions must be plainly marked as such, and must not be
//    misrepresented as being the original software.
// 3. This notice may not be removed or altered from any source distribution.
//

#include "DetourCommon.h"
#include "DetourMath.h"

//////////////////////////////////////////////////////////////////////////////////////////

void dtClosestPtPointTriangle(float* closest, const float* p,
							  const float* a, const float* b, const float* c)
{
	// Check if P in vertex region outside A
	float ab[3], ac[3], ap[3];
	dtVsub(ab, b, a);
	dtVsub(ac, c, a);
	dtVsub(ap, p, a);
	float d1 = dtVdot(ab, ap);
	float d2 = dtVdot(ac, ap);
	if (d1 <= 0.0f && d2 <= 0.0f)
	{
		// barycentric coordinates (1,0,0)
		dtVcopy(closest, a);
		return;
	}
	
	// Check if P in vertex region outside B
	float bp[3];
	dtVsub(bp, p, b);
	float d3 = dtVdot(ab, bp);
	float d4 = dtVdot(ac, bp);
	if (d3 >= 0.0f && d4 <= d3)
	{
		// barycentric coordinates (0,1,0)
		dtVcopy(closest, b);
		return;
	}
	
	// Check if P in edge region of AB, if so return projection of P onto AB
	float vc = d1*d4 - d3*d2;
	if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f)
	{
		// barycentric coordinates (1-v,v,0)
		float v = d1 / (d1 - d3);
		closest[0] = a[0] + v * ab[0];
		closest[1] = a[1] + v * ab[1];
		closest[2] = a[2] + v * ab[2];
		return;
	}
	
	// Check if P in vertex region outside C
	float cp[3];
	dtVsub(cp, p, c);
	float d5 = dtVdot(ab, cp);
	float d6 = dtVdot(ac, cp);
	if (d6 >= 0.0f && d5 <= d6)
	{
		// barycentric coordinates (0,0,1)
		dtVcopy(closest, c);
		return;
	}
	
	// Check if P in edge region of AC, if so return projection of P onto AC
	float vb = d5*d2 - d1*d6;
	if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f)
	{
		// barycentric coordinates (1-w,0,w)
		float w = d2 / (d2 - d6);
		closest[0] = a[0] + w * ac[0];
		closest[1] = a[1] + w * ac[1];
		closest[2] = a[2] + w * ac[2];
		return;
	}
	
	// Check if P in edge region of BC, if so return projection of P onto BC
	float va = d3*d6 - d5*d4;
	if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f)
	{
		// barycentric coordinates (0,1-w,w)
		float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
		closest[0] = b[0] + w * (c[0] - b[0]);
		closest[1] = b[1] + w * (c[1] - b[1]);
		closest[2] = b[2] + w * (c[2] - b[2]);
		return;
	}
	
	// P inside face region. Compute Q through its barycentric coordinates (u,v,w)
	float denom = 1.0f / (va + vb + vc);
	float v = vb * denom;
	float w = vc * denom;
	closest[0] = a[0] + ab[0] * v + ac[0] * w;
	closest[1] = a[1] + ab[1] * v + ac[1] * w;
	closest[2] = a[2] + ab[2] * v + ac[2] * w;
}

// xiehong：一个线段可能穿越一个多边形，min表示进入多边形的交点，max表示出多边形的交点，
// 当然也可能没有min（起点在这个多边形内）
// 或者没有max（终点这个多边形内）
// 或者都没有（线段本身在多边形内）
bool dtIntersectSegmentPoly2D(const float* p0, const float* p1,
							  const float* verts, int nverts,
							  float& tmin, float& tmax,
							  int& segMin, int& segMax)
{
	static const float EPS = 0.00000001f;
	
	tmin = 0;
	tmax = 1;
	segMin = -1;
	segMax = -1;
	
	float dir[3];
	dtVsub(dir, p1, p0);
	
	for (int i = 0, j = nverts-1; i < nverts; j=i++)
	{
		float edge[3], diff[3];
		dtVsub(edge, &verts[i*3], &verts[j*3]);
		dtVsub(diff, p0, &verts[j*3]);
		const float n = dtVperp2D(edge, diff);
		const float d = dtVperp2D(dir, edge);
		if (fabsf(d) < EPS)
		{
			// S is nearly parallel to this edge
			// xiehong：与某条边平行，并且这条边还是最靠近的边（n<0, 表示diff在edge的左边）
			if (n < 0)
				return false;
			else
				continue;
		}
		const float t = n / d;
		// xiehong： 因为poly是顺时针转的，所以在dir左边的边，总是距离p0近的边，而反之，在dir右边的边，总是距离p0远的边
		// 所以可以通过判断每条边在dir左边还是右边来判断它是距离p0远还是近
		if (d < 0)
		{
			// xiehong： dir 叉乘 edge <0 表示edge在dir的左边（由于poly是顺时针的，也表示靠近p0的edge）
			// segment S is entering across this edge
			if (t > tmin)
			{
				// t表示edge（或延长线）到dir（或延长线）上的交点p2到p0长度比上p0到p1的长度（这个通过面积可以算出来）
				tmin = t;
				segMin = j;
				// S enters after leaving polygon
				if (tmin > tmax)
					return false;
			}
		}
		else
		{
			// xiehong： dir 叉乘 edge <0 表示edge在dir的右边（由于poly是顺时针的，也表示靠近p0的edge）
			// segment S is leaving across this edge
			if (t < tmax)
			{
				tmax = t;
				segMax = j;
				// S leaves before entering polygon
				if (tmax < tmin)
					return false;
			}
		}
	}
	
	return true;
}

float dtDistancePtSegSqr2D(const float* pt, const float* p, const float* q, float& t)
{
	// xiehong：计算在x-z平面上一个点到一条线段的距离，注意是线段而不是直线。
	// 所以不能简单的做垂线，而是要判断垂线到达的点是不是在线段上，如果不是则要取线段的端点
	// 返回值是距离的平方
	// p、q是线段两个端点，t是取得点在这个线段上的百分比，从p开始算：位置 = p + t * (q - p)
	float pqx = q[0] - p[0];
	float pqz = q[2] - p[2];
	float dx = pt[0] - p[0];
	float dz = pt[2] - p[2];
	float d = pqx*pqx + pqz*pqz;
	t = pqx*dx + pqz*dz;	// t这里求出的是qp和ppt两个向量的点积，同时 t 还等于|pq|*|ppt|*cosθ，假设pt在pq向量上的投影点为pt1，则t=|pq|*|ppt1|
	if (d > 0) t /= d;		// d = |pq|*|pq|，因此 t/d = |ppt1|/|pq|，而|ppt1|/|pq|很好理解，如果大于1或者小于0，都表示pt1不在pq线段上，因此需要约束在0-1之内
	if (t < 0) t = 0;
	else if (t > 1) t = 1;
	dx = p[0] + t*pqx - pt[0];
	dz = p[2] + t*pqz - pt[2];
	return dx*dx + dz*dz;
}

void dtCalcPolyCenter(float* tc, const unsigned short* idx, int nidx, const float* verts)
{
	tc[0] = 0.0f;
	tc[1] = 0.0f;
	tc[2] = 0.0f;
	for (int j = 0; j < nidx; ++j)
	{
		const float* v = &verts[idx[j]*3];
		tc[0] += v[0];
		tc[1] += v[1];
		tc[2] += v[2];
	}
	const float s = 1.0f / nidx;
	tc[0] *= s;
	tc[1] *= s;
	tc[2] *= s;
}

bool dtClosestHeightPointTriangle(const float* p, const float* a, const float* b, const float* c, float& h)
{
	const float EPS = 1e-6f;
	float v0[3], v1[3], v2[3];

	dtVsub(v0, c, a);
	dtVsub(v1, b, a);
	dtVsub(v2, p, a);

	// Compute scaled barycentric coordinates
	float denom = v0[0] * v1[2] - v0[2] * v1[0];
	if (fabsf(denom) < EPS)
		return false;

	float u = v1[2] * v2[0] - v1[0] * v2[2];
	float v = v0[0] * v2[2] - v0[2] * v2[0];

	if (denom < 0) {
		denom = -denom;
		u = -u;
		v = -v;
	}

	// If point lies inside the triangle, return interpolated ycoord.
	if (u >= 0.0f && v >= 0.0f && (u + v) <= denom) {
		h = a[1] + (v0[1] * u + v1[1] * v) / denom;
		return true;
	}
	return false;
}

/// @par
///
/// All points are projected onto the xz-plane, so the y-values are ignored.
bool dtPointInPolygon(const float* pt, const float* verts, const int nverts)
{
	// TODO: Replace pnpoly with triArea2D tests?
	int i, j;
	bool c = false;
	for (i = 0, j = nverts-1; i < nverts; j = i++)
	{
		const float* vi = &verts[i*3];
		const float* vj = &verts[j*3];
		if (((vi[2] > pt[2]) != (vj[2] > pt[2])) &&
			(pt[0] < (vj[0]-vi[0]) * (pt[2]-vi[2]) / (vj[2]-vi[2]) + vi[0]) )
			c = !c;
	}
	return c;
}

bool dtDistancePtPolyEdgesSqr(const float* pt, const float* verts, const int nverts,
							  float* ed, float* et)
{
	// TODO: Replace pnpoly with triArea2D tests?
	int i, j;
	bool c = false;
	for (i = 0, j = nverts-1; i < nverts; j = i++)
	{
		const float* vi = &verts[i*3];
		const float* vj = &verts[j*3];
		// xiehong：这里判断一个点是否在一个凸多边形之内，没看太明白
		if (((vi[2] > pt[2]) != (vj[2] > pt[2])) &&
			(pt[0] < (vj[0]-vi[0]) * (pt[2]-vi[2]) / (vj[2]-vi[2]) + vi[0]) )
			c = !c;
		ed[j] = dtDistancePtSegSqr2D(pt, vj, vi, et[j]);
	}
	return c;
}

static void projectPoly(const float* axis, const float* poly, const int npoly,
						float& rmin, float& rmax)
{
	rmin = rmax = dtVdot2D(axis, &poly[0]);
	for (int i = 1; i < npoly; ++i)
	{
		const float d = dtVdot2D(axis, &poly[i*3]);
		rmin = dtMin(rmin, d);
		rmax = dtMax(rmax, d);
	}
}

inline bool overlapRange(const float amin, const float amax,
						 const float bmin, const float bmax,
						 const float eps)
{
	return ((amin+eps) > bmax || (amax-eps) < bmin) ? false : true;
}

/// @par
///
/// All vertices are projected onto the xz-plane, so the y-values are ignored.
// xiehong： 判断两个多边形是否会重叠
// 如果两个多边形不重叠，那么一定存在一个多边形的某条边的垂线，当两个多边形都向这条边投影后（成为两条线段），投影后的两条线段不重合
bool dtOverlapPolyPoly2D(const float* polya, const int npolya,
						 const float* polyb, const int npolyb)
{
	const float eps = 1e-4f;
	
	for (int i = 0, j = npolya-1; i < npolya; j=i++)
	{
		const float* va = &polya[j*3];
		const float* vb = &polya[i*3];
		const float n[3] = { vb[2]-va[2], 0, -(vb[0]-va[0]) };
		float amin,amax,bmin,bmax;
		projectPoly(n, polya, npolya, amin,amax);
		projectPoly(n, polyb, npolyb, bmin,bmax);
		if (!overlapRange(amin,amax, bmin,bmax, eps))
		{
			// Found separating axis
			return false;
		}
	}
	for (int i = 0, j = npolyb-1; i < npolyb; j=i++)
	{
		const float* va = &polyb[j*3];
		const float* vb = &polyb[i*3];
		const float n[3] = { vb[2]-va[2], 0, -(vb[0]-va[0]) };
		float amin,amax,bmin,bmax;
		projectPoly(n, polya, npolya, amin,amax);
		projectPoly(n, polyb, npolyb, bmin,bmax);
		if (!overlapRange(amin,amax, bmin,bmax, eps))
		{
			// Found separating axis
			return false;
		}
	}
	return true;
}

// Returns a random point in a convex polygon.
// Adapted from Graphics Gems article.
void dtRandomPointInConvexPoly(const float* pts, const int npts, float* areas,
							   const float s, const float t, float* out)
{
	// Calc triangle araes
	float areasum = 0.0f;
	for (int i = 2; i < npts; i++) {
		areas[i] = dtTriArea2D(&pts[0], &pts[(i-1)*3], &pts[i*3]);
		areasum += dtMax(0.001f, areas[i]);
	}
	// Find sub triangle weighted by area.
	const float thr = s*areasum;
	float acc = 0.0f;
	float u = 1.0f;
	int tri = npts - 1;
	for (int i = 2; i < npts; i++) {
		const float dacc = areas[i];
		if (thr >= acc && thr < (acc+dacc))
		{
			u = (thr - acc) / dacc;
			tri = i;
			break;
		}
		acc += dacc;
	}
	
	float v = dtMathSqrtf(t);
	
	const float a = 1 - v;
	const float b = (1 - u) * v;
	const float c = u * v;
	const float* pa = &pts[0];
	const float* pb = &pts[(tri-1)*3];
	const float* pc = &pts[tri*3];
	
	out[0] = a*pa[0] + b*pb[0] + c*pc[0];
	out[1] = a*pa[1] + b*pb[1] + c*pc[1];
	out[2] = a*pa[2] + b*pb[2] + c*pc[2];
}

inline float vperpXZ(const float* a, const float* b) { return a[0]*b[2] - a[2]*b[0]; }

// xiehong：计算两条线段交点分别距离两条线段开头的位置（百分比）
// 通过叉乘在平面上的几何意义是面积来换算，s表示交点在a线段上距离ap与aq距离ap的比例，t同理
bool dtIntersectSegSeg2D(const float* ap, const float* aq,
						 const float* bp, const float* bq,
						 float& s, float& t)
{
	float u[3], v[3], w[3];
	dtVsub(u,aq,ap);
	dtVsub(v,bq,bp);
	dtVsub(w,ap,bp);
	float d = vperpXZ(u,v);
	if (fabsf(d) < 1e-6f) return false;
	s = vperpXZ(v,w) / d;
	t = vperpXZ(u,w) / d;
	return true;
}

