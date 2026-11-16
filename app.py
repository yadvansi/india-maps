"""India Maps - Full India Geocoding, Road Routing & User Persistence API (Flask + SQLite).

Endpoints
  GET  /                     -> serves the dashboard (static/index.html)
  GET  /health               -> uptime check for Render / Railway / Fly.io
  GET  /api/network          -> major cities + highway edges
  GET  /api/cities           -> major cities with congestion score for an hour
  GET  /api/rush?hour=18     -> congestion index (0-100) for major metros
  GET  /api/geocode?q=...    -> live India-wide place/address search (OSM Nominatim)
  GET  /api/reverse?lat=..&lon=.. -> reverse geocode map clicks / GPS coordinates
  GET  /api/route?from_lat=..&from_lon=..&to_lat=..&to_lon=..&vehicle=car&hour=9
                             -> real road routes (OSRM) + rush-hour traffic & lane guidance
  POST /api/auth/signup      -> create account & return session token
  POST /api/auth/login       -> verify credentials & return session token
  POST /api/auth/logout      -> revoke current session token
  GET  /api/trips            -> fetch user's saved & recent trips (Bearer token)
  POST /api/trips/save       -> toggle saved trip
  POST /api/trips/recent     -> log recent trip
"""
import hashlib
import heapq
import hmac
import json
import math
import os
import re
import secrets
import sqlite3
import ssl
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from functools import lru_cache, wraps

from flask import Flask, g, jsonify, request, send_from_directory
from flask_cors import CORS

app = Flask(__name__, static_folder="static")
CORS(app)

DB_PATH = os.environ.get("INDIA_MAPS_DB", "india_maps.db")
USER_AGENT = "IndiaMapsApp/2.0 (contact: dev@indiamaps.local)"

# Major Indian cities (used for Congestion Index, Heatmap & offline routing fallback)
CITIES = [
    ("delhi", "Delhi", "Delhi", 77.2090, 28.6139, 92),
    ("jaipur", "Jaipur", "Rajasthan", 75.7873, 26.9124, 70),
    ("agra", "Agra", "Uttar Pradesh", 78.0081, 27.1767, 55),
    ("lucknow", "Lucknow", "Uttar Pradesh", 80.9462, 26.8467, 68),
    ("kanpur", "Kanpur", "Uttar Pradesh", 80.3319, 26.4499, 55),
    ("varanasi", "Varanasi", "Uttar Pradesh", 82.9739, 25.3176, 58),
    ("patna", "Patna", "Bihar", 85.1376, 25.5941, 66),
    ("kolkata", "Kolkata", "West Bengal", 88.3639, 22.5726, 90),
    ("guwahati", "Guwahati", "Assam", 91.7362, 26.1445, 52),
    ("bhubaneswar", "Bhubaneswar", "Odisha", 85.8245, 20.2961, 50),
    ("ranchi", "Ranchi", "Jharkhand", 85.3096, 23.3441, 45),
    ("raipur", "Raipur", "Chhattisgarh", 81.6296, 21.2514, 45),
    ("nagpur", "Nagpur", "Maharashtra", 79.0882, 21.1458, 58),
    ("bhopal", "Bhopal", "Madhya Pradesh", 77.4126, 23.2599, 52),
    ("indore", "Indore", "Madhya Pradesh", 75.8577, 22.7196, 62),
    ("ahmedabad", "Ahmedabad", "Gujarat", 72.5714, 23.0225, 72),
    ("surat", "Surat", "Gujarat", 72.8311, 21.1702, 66),
    ("mumbai", "Mumbai", "Maharashtra", 72.8777, 19.0760, 95),
    ("pune", "Pune", "Maharashtra", 73.8567, 18.5204, 80),
    ("hyderabad", "Hyderabad", "Telangana", 78.4867, 17.3850, 85),
    ("bengaluru", "Bengaluru", "Karnataka", 77.5946, 12.9716, 96),
    ("chennai", "Chennai", "Tamil Nadu", 80.2707, 13.0827, 88),
    ("kochi", "Kochi", "Kerala", 76.2673, 9.9312, 60),
    ("tvm", "Thiruvananthapuram", "Kerala", 76.9366, 8.5241, 48),
    ("chandigarh", "Chandigarh", "Chandigarh", 76.7794, 30.7333, 50),
    ("amritsar", "Amritsar", "Punjab", 74.8723, 31.6340, 48),
    ("vizag", "Visakhapatnam", "Andhra Pradesh", 83.2185, 17.6868, 52),
    ("coimbatore", "Coimbatore", "Tamil Nadu", 76.9558, 11.0168, 52),
    ("goa", "Panaji", "Goa", 73.8278, 15.4909, 40),
]
CITY = {c[0]: dict(id=c[0], name=c[1], state=c[2], lon=c[3], lat=c[4], base=c[5]) for c in CITIES}

EDGES = [
    ("delhi", "chandigarh", "h"), ("chandigarh", "amritsar", "h"), ("delhi", "jaipur", "h"), ("delhi", "agra", "h"),
    ("agra", "lucknow", "h"), ("lucknow", "kanpur", "l"), ("lucknow", "varanasi", "h"), ("varanasi", "patna", "h"),
    ("patna", "kolkata", "h"), ("kolkata", "ranchi", "l"), ("ranchi", "patna", "l"), ("kolkata", "bhubaneswar", "h"),
    ("bhubaneswar", "vizag", "h"), ("vizag", "chennai", "h"), ("vizag", "hyderabad", "l"), ("kolkata", "guwahati", "l"),
    ("guwahati", "patna", "l"), ("jaipur", "ahmedabad", "h"), ("ahmedabad", "surat", "h"), ("surat", "mumbai", "h"),
    ("mumbai", "pune", "h"), ("pune", "hyderabad", "h"), ("pune", "bengaluru", "h"), ("bengaluru", "chennai", "h"),
    ("hyderabad", "bengaluru", "h"), ("bengaluru", "coimbatore", "l"), ("coimbatore", "kochi", "l"), ("kochi", "tvm", "l"),
    ("chennai", "coimbatore", "l"), ("mumbai", "goa", "l"), ("goa", "bengaluru", "l"), ("agra", "bhopal", "l"),
    ("jaipur", "indore", "l"), ("indore", "bhopal", "l"), ("bhopal", "nagpur", "l"), ("nagpur", "hyderabad", "h"),
    ("nagpur", "raipur", "l"), ("raipur", "bhubaneswar", "l"), ("agra", "kanpur", "l"), ("indore", "ahmedabad", "l"),
    ("indore", "mumbai", "l"), ("jaipur", "agra", "l"), ("kanpur", "varanasi", "l"), ("raipur", "ranchi", "l"),
    ("nagpur", "indore", "l"),
]

VEHICLES = {
    "car":  {"osrm": "driving", "sh": 80, "sl": 55, "sens": 0.80, "speed_factor": 1.00},
    "bike": {"osrm": "driving", "sh": 58, "sl": 42, "sens": 0.45, "speed_factor": 1.12},
    "walk": {"osrm": "foot",    "sh": 5,  "sl": 5,  "sens": 0.00, "speed_factor": 1.00},
    "pt":   {"osrm": "driving", "sh": 65, "sl": 42, "sens": 0.35, "speed_factor": 1.25},
}
LIMITS = {"car": (100, 60), "bike": (60, 45), "pt": (80, 50), "walk": (0, 0)}


# ==================== SQLite Database & Auth Helpers ====================

def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
        g.db.execute("PRAGMA foreign_keys = ON")
    return g.db


@app.teardown_appcontext
def close_db(exc):
    db = g.pop("db", None)
    if db is not None:
        db.close()


def init_db():
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute("PRAGMA journal_mode = WAL")
        conn.execute("PRAGMA foreign_keys = ON")
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                email TEXT PRIMARY KEY,
                name TEXT NOT NULL,
                salt BLOB NOT NULL,
                pw_hash BLOB NOT NULL,
                home_city TEXT DEFAULT '',
                created_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS sessions (
                token TEXT PRIMARY KEY,
                email TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(email) REFERENCES users(email) ON DELETE CASCADE
            );
            CREATE TABLE IF NOT EXISTS trips (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                email TEXT NOT NULL,
                kind TEXT NOT NULL CHECK(kind IN ('saved', 'recent')),
                origin_name TEXT NOT NULL,
                origin_lat REAL NOT NULL,
                origin_lon REAL NOT NULL,
                dest_name TEXT NOT NULL,
                dest_lat REAL NOT NULL,
                dest_lon REAL NOT NULL,
                vehicle TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE(email, kind, origin_name, dest_name, vehicle),
                FOREIGN KEY(email) REFERENCES users(email) ON DELETE CASCADE
            );
            """
        )


init_db()


def _hash_password(password: str, salt: bytes) -> bytes:
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 150_000)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def require_auth(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        auth = request.headers.get("Authorization", "")
        token = auth[7:].strip() if auth.startswith("Bearer ") else ""
        if not token:
            return jsonify(error="Authentication required"), 401
        row = get_db().execute(
            "SELECT u.email, u.name, u.home_city FROM sessions s JOIN users u ON s.email = u.email WHERE s.token = ?",
            (token,),
        ).fetchone()
        if not row:
            return jsonify(error="Invalid or expired session"), 401
        g.user = dict(row)
        return fn(*args, **kwargs)

    return wrapper


# ==================== Traffic & Congestion Model ====================

def haversine(lat1, lon1, lat2, lon2):
    r = math.radians
    dl, dn = r(lat2 - lat1), r(lon2 - lon1)
    q = math.sin(dl / 2) ** 2 + math.cos(r(lat1)) * math.cos(r(lat2)) * math.sin(dn / 2) ** 2
    return 12742 * math.asin(math.sqrt(q))


def _g(x, m, s):
    return math.exp(-((x - m) ** 2) / (2 * s * s))


def profile(hour):
    """Traffic profile: morning (9:30) and evening (18:30) peaks, never below 0.15."""
    return 0.15 + 0.85 * max(
        _g(hour, 9.5, 1.7),
        _g(hour, 18.5, 2.1),
        _g(hour + 24, 18.5, 2.1),
        _g(hour - 24, 9.5, 1.7),
    )


def rush(city_id, hour):
    return CITY[city_id]["base"] * profile(hour)


def spatial_rush(lat, lon, hour):
    """Estimate congestion at any (lat, lon) in India weighted by proximity to major metros."""
    prof = profile(hour)
    best_score = 32.0 * prof
    for c in CITY.values():
        d = haversine(lat, lon, c["lat"], c["lon"])
        # Influence radius of ~65 km around major metros
        influence = math.exp(-(d / 65.0) ** 2)
        score = (30.0 + (c["base"] - 30.0) * influence) * prof
        if score > best_score:
            best_score = score
    return round(min(100.0, best_score), 1)


def level(r):
    return "Heavy" if r >= 65 else "Moderate" if r >= 40 else "Light"


def fmt(m):
    m = round(m)
    if m < 60:
        return f"{m} min"
    if m < 1440:
        return f"{m // 60}h {m % 60}m"
    return f"{m // 1440}d {round(m % 1440 / 60)}h"


def lane_advice(vehicle, kind, side):
    lane = 1 if kind == "straight" else 0 if side == "left" else 2
    if vehicle == "pt":
        return 0, "Stay in the bus lane (leftmost) and follow the service board"
    if vehicle == "walk":
        return lane, {
            0: "Stay on the left footpath",
            2: "Cross at the zebra crossing, then use the right footpath",
        }.get(lane, "Keep walking on the footpath")
    if vehicle == "bike":
        if kind == "uturn":
            return 2, "Right lane, U-turn at the median cut"
        return {
            0: (0, "Leftmost lane (two-wheeler edge)"),
            2: (2, "Signal, then merge into the right lane early"),
        }.get(lane, (0, "Stay in the left lane"))
    if kind == "uturn":
        return 2, "Right-most lane, U-turn at the median cut"
    return {
        0: (0, "Keep in the LEFT lane"),
        2: (2, "Move to the RIGHT lane (nearest the median)"),
    }.get(lane, (1, "Stay in the MIDDLE lane"))


# ==================== External Geocoding & OSRM Routing ====================

def _fetch_json(url: str, timeout: float = 8.0):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
    ctx = ssl._create_unverified_context()
    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
        return json.loads(resp.read().decode("utf-8"))


@lru_cache(maxsize=512)
def geocode_india(query: str):
    q = query.strip()
    ql = q.lower()
    results = []

    # 1. Always surface matching major metros first for instant response
    for c in CITY.values():
        if ql in c["name"].lower() or ql in c["state"].lower():
            results.append({
                "id": c["id"],
                "name": c["name"],
                "display_name": f"{c['name']}, {c['state']}, India",
                "state": c["state"],
                "lat": c["lat"],
                "lon": c["lon"],
                "major": True,
            })

    # 2. Query OpenStreetMap Nominatim for all towns, localities, stations, POIs in India
    if len(q) >= 2:
        params = urllib.parse.urlencode({
            "q": q,
            "countrycodes": "in",
            "format": "jsonv2",
            "addressdetails": 1,
            "limit": 8,
        })
        try:
            data = _fetch_json(f"https://nominatim.openstreetmap.org/search?{params}", timeout=6.0)
            seen = {(round(r["lat"], 3), round(r["lon"], 3)) for r in results}
            for item in data:
                lat, lon = float(item["lat"]), float(item["lon"])
                key = (round(lat, 3), round(lon, 3))
                if key in seen:
                    continue
                seen.add(key)
                addr = item.get("address", {})
                short = (
                    item.get("name")
                    or addr.get("city")
                    or addr.get("town")
                    or addr.get("village")
                    or addr.get("suburb")
                    or item.get("display_name", "").split(",")[0]
                )
                state = addr.get("state") or addr.get("county") or "India"
                results.append({
                    "id": f"osm_{item.get('place_id', '')}",
                    "name": short,
                    "display_name": item.get("display_name", f"{short}, {state}"),
                    "state": state,
                    "lat": lat,
                    "lon": lon,
                    "major": False,
                })
        except Exception:
            pass

    return results[:10]


@lru_cache(maxsize=256)
def reverse_geocode_india(lat_r: float, lon_r: float):
    params = urllib.parse.urlencode({"lat": lat_r, "lon": lon_r, "format": "jsonv2", "zoom": 14})
    try:
        data = _fetch_json(f"https://nominatim.openstreetmap.org/reverse?{params}", timeout=5.0)
        addr = data.get("address", {})
        name = (
            data.get("name")
            or addr.get("suburb")
            or addr.get("neighbourhood")
            or addr.get("town")
            or addr.get("city")
            or addr.get("village")
            or f"{lat_r:.4f}, {lon_r:.4f}"
        )
        state = addr.get("state") or "India"
        return {"name": name, "state": state, "display_name": data.get("display_name", name), "lat": lat_r, "lon": lon_r}
    except Exception:
        return {"name": f"{lat_r:.4f}, {lon_r:.4f}", "state": "India", "display_name": f"{lat_r:.4f}, {lon_r:.4f}", "lat": lat_r, "lon": lon_r}


def _map_osrm_turn(step, vehicle, dst_name):
    m = step.get("maneuver", {})
    mtype = m.get("type", "turn")
    mod = m.get("modifier", "")
    road = step.get("name") or step.get("ref") or ("Footpath" if vehicle == "walk" else "Local Road")
    dist_km = round(step.get("distance", 0) / 1000.0, 1)
    loc = m.get("location", [0, 0])  # [lon, lat]

    if mtype == "arrive":
        return {
            "arrive": True,
            "lat": loc[1],
            "lon": loc[0],
            "text": f"Arrive at {dst_name}",
        }

    side = "left" if "left" in mod else "right"
    if "uturn" in mod:
        kind, text = "uturn", "Make a U-turn"
    elif "sharp" in mod:
        kind, text = "sharp", f"Take a sharp {side}"
    elif "slight" in mod:
        kind, text = "slight", f"Keep {side}"
    elif mtype in ("fork", "off ramp", "on ramp"):
        kind, text = "slight", f"Take the {side} ramp"
    elif mtype == "roundabout":
        ex = m.get("exit", 1)
        kind, text = "turn", f"At roundabout, take exit {ex}"
    elif "left" in mod or "right" in mod:
        kind, text = "turn", f"Turn {side}"
    else:
        kind, text = "straight", "Continue straight"

    lane_idx, lane_txt = lane_advice(vehicle, kind, side)
    is_hwy = bool(step.get("ref")) or "NH" in road or "Expressway" in road
    speed_lim = LIMITS[vehicle][0 if is_hwy else 1]

    return {
        "arrive": False,
        "lat": loc[1],
        "lon": loc[0],
        "kind": kind,
        "side": side,
        "text": text,
        "road": road,
        "next": road,
        "next_km": dist_km,
        "speed_limit": speed_lim,
        "lane_index": lane_idx,
        "lane": lane_txt,
    }


def osrm_routes(lat1, lon1, lat2, lon2, dst_name, vehicle, hour):
    vcfg = VEHICLES[vehicle]
    profile_name = vcfg["osrm"]
    url = (
        f"https://router.project-osrm.org/route/v1/{profile_name}/"
        f"{lon1},{lat1};{lon2},{lat2}?alternatives=true&overview=full&geometries=geojson&steps=true"
    )
    data = _fetch_json(url, timeout=9.0)
    if data.get("code") != "Ok" or not data.get("routes"):
        return None

    r_start = spatial_rush(lat1, lon1, hour)
    r_mid = spatial_rush((lat1 + lat2) / 2, (lon1 + lon2) / 2, hour)
    r_end = spatial_rush(lat2, lon2, hour)
    peak_rush = round(max(r_start, r_mid, r_end))
    avg_rush = (r_start + r_mid + r_end) / 3.0
    traffic_mult = 1.0 + vcfg["sens"] * (avg_rush / 100.0)

    labels = [("Fastest Route", "bolt"), ("Alternative Route", "road"), ("Secondary Option", "leaf")]
    out = []

    for idx, r in enumerate(data["routes"][:3]):
        km = round(r["distance"] / 1000.0, 1)
        base_mins = (r["duration"] / 60.0) * vcfg["speed_factor"]
        adj_mins = base_mins * traffic_mult

        # GeoJSON coordinates come as [lon, lat] -> convert to [lat, lon] for Leaflet
        coords = [[pt[1], pt[0]] for pt in r["geometry"]["coordinates"]]

        steps = []
        for leg in r.get("legs", []):
            steps.extend(leg.get("steps", []))

        depart_road = steps[0].get("name") or steps[0].get("ref") or "the starting road" if steps else "route"
        turns = [_map_osrm_turn(s, vehicle, dst_name) for s in steps[1:]] if len(steps) > 1 else [
            {"arrive": True, "lat": lat2, "lon": lon2, "text": f"Arrive at {dst_name}"}
        ]

        label, icon = labels[idx] if idx < len(labels) else (f"Route {idx + 1}", "road")
        out.append({
            "rank": "primary" if idx == 0 else "alternative",
            "name": label,
            "icon": icon,
            "coords": coords,
            "km": round(km) if km >= 10 else km,
            "minutes": round(adj_mins),
            "free_flow_minutes": round(base_mins),
            "traffic_delay_minutes": max(0, round(adj_mins - base_mins)),
            "eta": fmt(adj_mins),
            "peak_rush": peak_rush,
            "traffic": level(peak_rush),
            "turn_count": sum(1 for t in turns if not t["arrive"] and t["kind"] != "straight"),
            "depart": f"Head onto {depart_road}",
            "turns": turns,
        })

    return out


# ==================== Offline Fallback Graph (if OSRM is unreachable) ====================

ADJ = {c: [] for c in CITY}
for a, b, t in EDGES:
    d = haversine(CITY[a]["lat"], CITY[a]["lon"], CITY[b]["lat"], CITY[b]["lon"]) * 1.3
    ADJ[a].append((b, d, t))
    ADJ[b].append((a, d, t))


def _nearest_city(lat, lon):
    return min(CITY.values(), key=lambda c: haversine(lat, lon, c["lat"], c["lon"]))


def fallback_route(lat1, lon1, lat2, lon2, dst_name, vehicle, hour):
    c1, c2 = _nearest_city(lat1, lon1), _nearest_city(lat2, lon2)
    src, dst = c1["id"], c2["id"]
    dist, prev, heap = {src: 0.0}, {}, [(0.0, src)]
    vcfg = VEHICLES[vehicle]
    while heap:
        du, u = heapq.heappop(heap)
        if du > dist.get(u, math.inf) or u == dst:
            continue
        for v, d, t in ADJ[u]:
            w = d / (vcfg["sh"] if t == "h" else vcfg["sl"]) * 60
            if du + w < dist.get(v, math.inf):
                dist[v], prev[v] = du + w, u
                heapq.heappush(heap, (dist[v], v))
    nodes = [dst]
    while nodes[-1] != src and nodes[-1] in prev:
        nodes.append(prev[nodes[-1]])
    nodes.reverse()

    coords = [[lat1, lon1]] + [[CITY[n]["lat"], CITY[n]["lon"]] for n in nodes] + [[lat2, lon2]]
    km = sum(haversine(coords[i][0], coords[i][1], coords[i + 1][0], coords[i + 1][1]) * 1.25 for i in range(len(coords) - 1))
    peak = round(max(spatial_rush(lat1, lon1, hour), spatial_rush(lat2, lon2, hour)))
    mins = km / vcfg["sh"] * 60 * (1 + vcfg["sens"] * peak / 100)
    turns = [
        {
            "arrive": False, "lat": CITY[n]["lat"], "lon": CITY[n]["lon"],
            "kind": "straight", "side": "right", "text": f"Continue via {CITY[n]['name']}",
            "road": "National Highway", "next": CITY[n]["name"], "next_km": round(km / max(1, len(nodes)), 1),
            "speed_limit": LIMITS[vehicle][0], "lane_index": 1, "lane": "Stay in the MIDDLE lane",
        }
        for n in nodes[1:-1]
    ] + [{"arrive": True, "lat": lat2, "lon": lon2, "text": f"Arrive at {dst_name}"}]

    return [{
        "rank": "primary", "name": "Highway Corridor (Offline Fallback)", "icon": "road",
        "coords": coords, "km": round(km), "minutes": round(mins), "free_flow_minutes": round(mins * 0.85),
        "traffic_delay_minutes": round(mins * 0.15), "eta": fmt(mins), "peak_rush": peak,
        "traffic": level(peak), "turn_count": len(turns) - 1, "depart": "Head towards highway corridor",
        "turns": turns,
    }]


def _hour():
    try:
        return int(request.args.get("hour", datetime.now().hour)) % 24
    except ValueError:
        return datetime.now().hour


# ==================== Routes: Map, Geocoding & Navigation ====================

@app.get("/")
def index():
    return send_from_directory(app.static_folder, "index.html")


@app.get("/health")
def health():
    return jsonify(status="ok", cities=len(CITY), edges=len(EDGES), time=_now_iso())


@app.get("/api/network")
def network():
    h = _hour()
    return jsonify(
        cities=[dict(c, rush=round(rush(c["id"], h)), level=level(rush(c["id"], h))) for c in CITY.values()],
        edges=[{"from": a, "to": b, "type": t} for a, b, t in EDGES],
    )


@app.get("/api/rush")
def rush_index():
    h = _hour()
    rows = sorted(
        (
            {
                "id": c,
                "name": CITY[c]["name"],
                "lat": CITY[c]["lat"],
                "lon": CITY[c]["lon"],
                "score": round(rush(c, h)),
                "level": level(rush(c, h)),
            }
            for c in CITY
        ),
        key=lambda r: -r["score"],
    )
    return jsonify(dict(hour=h, scale="0-100", cities=rows))


@app.get("/api/geocode")
def geocode():
    q = request.args.get("q", "").strip()
    if not q:
        h = _hour()
        top = sorted(CITY.values(), key=lambda c: -rush(c["id"], h))[:8]
        return jsonify(results=[
            {
                "id": c["id"], "name": c["name"], "display_name": f"{c['name']}, {c['state']}, India",
                "state": c["state"], "lat": c["lat"], "lon": c["lon"], "major": True,
            }
            for c in top
        ])
    return jsonify(results=geocode_india(q))


@app.get("/api/reverse")
def reverse_geocode():
    try:
        lat = round(float(request.args["lat"]), 4)
        lon = round(float(request.args["lon"]), 4)
    except (KeyError, ValueError):
        return jsonify(error="lat and lon query params required"), 400
    return jsonify(reverse_geocode_india(lat, lon))


@app.get("/api/route")
def route():
    vehicle = request.args.get("vehicle", "car")
    if vehicle not in VEHICLES:
        return jsonify(error=f"vehicle must be one of {sorted(VEHICLES)}"), 400

    try:
        lat1 = float(request.args["from_lat"])
        lon1 = float(request.args["from_lon"])
        lat2 = float(request.args["to_lat"])
        lon2 = float(request.args["to_lon"])
    except (KeyError, ValueError):
        return jsonify(error="from_lat, from_lon, to_lat, to_lon are required"), 400

    if haversine(lat1, lon1, lat2, lon2) < 0.05:
        return jsonify(error="Origin and destination are the same location"), 400

    dst_name = request.args.get("to_name", "Destination").strip() or "Destination"
    h = _hour()

    try:
        routes = osrm_routes(lat1, lon1, lat2, lon2, dst_name, vehicle, h)
    except Exception:
        routes = None

    if not routes:
        routes = fallback_route(lat1, lon1, lat2, lon2, dst_name, vehicle, h)

    return jsonify(hour=h, vehicle=vehicle, routes=routes)


# ==================== Routes: Auth & Saved Trips ====================

@app.post("/api/auth/signup")
def signup():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email", "")).strip().lower()
    name = str(data.get("name", "")).strip()
    password = str(data.get("password", ""))
    home = str(data.get("home", "")).strip()

    if not re.match(r"^\S+@\S+\.\S+$", email):
        return jsonify(error="Enter a valid email address."), 400
    if not name:
        return jsonify(error="Please enter your name."), 400
    if len(password) < 6:
        return jsonify(error="Password must be at least 6 characters."), 400
    if home and home not in CITY:
        home = ""

    db = get_db()
    if db.execute("SELECT 1 FROM users WHERE email = ?", (email,)).fetchone():
        return jsonify(error="An account with this email already exists."), 409

    salt = os.urandom(16)
    pw_hash = _hash_password(password, salt)
    token = secrets.token_urlsafe(32)
    now = _now_iso()

    db.execute(
        "INSERT INTO users (email, name, salt, pw_hash, home_city, created_at) VALUES (?, ?, ?, ?, ?, ?)",
        (email, name, salt, pw_hash, home, now),
    )
    db.execute("INSERT INTO sessions (token, email, created_at) VALUES (?, ?, ?)", (token, email, now))
    db.commit()
    return jsonify(token=token, user={"email": email, "name": name, "home": home}), 201


@app.post("/api/auth/login")
def login():
    data = request.get_json(silent=True) or {}
    email = str(data.get("email", "")).strip().lower()
    password = str(data.get("password", ""))

    db = get_db()
    row = db.execute("SELECT email, name, salt, pw_hash, home_city FROM users WHERE email = ?", (email,)).fetchone()
    if not row or not hmac.compare_digest(_hash_password(password, row["salt"]), row["pw_hash"]):
        return jsonify(error="Incorrect email or password."), 401

    token = secrets.token_urlsafe(32)
    db.execute("INSERT INTO sessions (token, email, created_at) VALUES (?, ?, ?)", (token, email, _now_iso()))
    db.commit()
    return jsonify(token=token, user={"email": row["email"], "name": row["name"], "home": row["home_city"]})


@app.post("/api/auth/logout")
@require_auth
def logout():
    auth = request.headers.get("Authorization", "")
    token = auth[7:].strip()
    db = get_db()
    db.execute("DELETE FROM sessions WHERE token = ?", (token,))
    db.commit()
    return jsonify(ok=True)


@app.get("/api/trips")
@require_auth
def get_trips():
    db = get_db()
    rows = db.execute(
        """
        SELECT kind, origin_name, origin_lat, origin_lon, dest_name, dest_lat, dest_lon, vehicle
        FROM trips WHERE email = ? ORDER BY updated_at DESC
        """,
        (g.user["email"],),
    ).fetchall()

    def pack(r):
        return {
            "f": {"name": r["origin_name"], "lat": r["origin_lat"], "lon": r["origin_lon"]},
            "t": {"name": r["dest_name"], "lat": r["dest_lat"], "lon": r["dest_lon"]},
            "v": r["vehicle"],
        }

    saved = [pack(r) for r in rows if r["kind"] == "saved"][:8]
    recent = [pack(r) for r in rows if r["kind"] == "recent"][:5]
    return jsonify(saved=saved, recent=recent)


@app.post("/api/trips/save")
@require_auth
def toggle_saved_trip():
    data = request.get_json(silent=True) or {}
    f, t, v = data.get("f") or {}, data.get("t") or {}, data.get("v", "car")
    if not f.get("name") or not t.get("name") or v not in VEHICLES:
        return jsonify(error="Invalid trip parameters"), 400

    db = get_db()
    exists = db.execute(
        """
        SELECT id FROM trips
        WHERE email = ? AND kind = 'saved' AND origin_name = ? AND dest_name = ? AND vehicle = ?
        """,
        (g.user["email"], f["name"], t["name"], v),
    ).fetchone()
    if exists:
        db.execute("DELETE FROM trips WHERE id = ?", (exists["id"],))
    else:
        db.execute(
            """
            INSERT INTO trips (email, kind, origin_name, origin_lat, origin_lon, dest_name, dest_lat, dest_lon, vehicle, updated_at)
            VALUES (?, 'saved', ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (g.user["email"], f["name"], float(f["lat"]), float(f["lon"]), t["name"], float(t["lat"]), float(t["lon"]), v, _now_iso()),
        )
    db.commit()
    return get_trips()


@app.post("/api/trips/recent")
@require_auth
def add_recent_trip():
    data = request.get_json(silent=True) or {}
    f, t, v = data.get("f") or {}, data.get("t") or {}, data.get("v", "car")
    if not f.get("name") or not t.get("name") or v not in VEHICLES:
        return jsonify(error="Invalid trip parameters"), 400

    db = get_db()
    db.execute(
        """
        INSERT INTO trips (email, kind, origin_name, origin_lat, origin_lon, dest_name, dest_lat, dest_lon, vehicle, updated_at)
        VALUES (?, 'recent', ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(email, kind, origin_name, dest_name, vehicle)
        DO UPDATE SET updated_at = excluded.updated_at
        """,
        (g.user["email"], f["name"], float(f["lat"]), float(f["lon"]), t["name"], float(t["lat"]), float(t["lon"]), v, _now_iso()),
    )
    db.execute(
        """
        DELETE FROM trips
        WHERE email = ? AND kind = 'recent' AND id NOT IN (
            SELECT id FROM trips WHERE email = ? AND kind = 'recent'
            ORDER BY updated_at DESC LIMIT 5
        )
        """,
        (g.user["email"], g.user["email"]),
    )
    db.commit()
    return get_trips()


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5000))
    debug = os.environ.get("FLASK_DEBUG", "0") == "1"
    app.run(debug=debug, host="0.0.0.0", port=port)