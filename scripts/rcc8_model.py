"""Shared model of the Lean RCC8 abstraction and of rectangles.

Mirrors LeanGeospatial/CompositionTable.lean (signatures and schemas) and the
rectangle lemmas in LeanGeospatial/RCC8Witnesses.lean. Used to search for
witnesses; the Lean proofs do not trust it.
"""
from itertools import product

RELS = ["dc", "ec", "po", "eq", "tpp", "ntpp", "tppi", "ntppi"]
CONVERSE = {"dc": "dc", "ec": "ec", "po": "po", "eq": "eq",
            "tpp": "tppi", "ntpp": "ntppi", "tppi": "tpp", "ntppi": "ntpp"}

# Signature fields: c (meet), o (interiors meet), p (X within Y), q (Y within X),
# n (X within interior Y), m (Y within interior X).
def sig(c, o, p, q, n, m):
    return (c, o, p, q, n, m)

SIGS = {
    "dc":    [sig(0, 0, 0, 0, 0, 0)],
    "ec":    [sig(1, 0, 0, 0, 0, 0)],
    "po":    [sig(1, 1, 0, 0, 0, 0)],
    "eq":    [sig(1, 1, 1, 1, 0, 0), sig(1, 1, 1, 1, 1, 1)],
    "tpp":   [sig(1, 1, 1, 0, 0, 0)],
    "ntpp":  [sig(1, 1, 1, 0, 1, 0)],
    "tppi":  [sig(1, 1, 0, 1, 0, 0)],
    "ntppi": [sig(1, 1, 0, 1, 0, 1)],
}

def swap(s):
    c, o, p, q, n, m = s
    return (c, o, q, p, m, n)

def schema(xy, yz, xz):
    c1, o1, p1, _, n1, _ = xy
    c2, o2, p2, _, n2, _ = yz
    c3, o3, p3, _, n3, _ = xz
    imp = lambda a, b: (not a) or b
    return all([
        imp(p1 and p2, p3),            # S1
        imp(n1 and p2, n3),            # S2
        imp(p1 and n2, n3),            # S3
        imp(p1 and not c2, not c3),    # S4
        imp(p1 and not o2, not o3),    # S5
        imp(n1 and not o2, not c3),    # S6
        imp(c1 and n2, o3),            # S7
        imp(o1 and p2, o3),            # S8
        imp(c1 and p2, c3),            # S9
    ])

def consistent(ab, bc, ac):
    ba, cb, ca = swap(ab), swap(bc), swap(ac)
    return (schema(ab, bc, ac) and schema(ac, cb, ab) and schema(ba, ac, bc)
            and schema(bc, ca, ba) and schema(ca, ab, cb) and schema(cb, ba, ca))

def table(r, s):
    return [t for t in RELS
            if any(consistent(ab, bc, ac)
                   for ab in SIGS[r] for bc in SIGS[s] for ac in SIGS[t])]

# Closed axis-aligned rectangles (xmin, xmax, ymin, ymax), positive size.
def rel(a, b):
    ax0, ax1, ay0, ay1 = a
    bx0, bx1, by0, by1 = b
    c = ax0 <= bx1 and bx0 <= ax1 and ay0 <= by1 and by0 <= ay1
    o = ax0 < bx1 and bx0 < ax1 and ay0 < by1 and by0 < ay1
    p = bx0 <= ax0 and ax1 <= bx1 and by0 <= ay0 and ay1 <= by1
    q = ax0 <= bx0 and bx1 <= ax1 and ay0 <= by0 and by1 <= ay1
    n = bx0 < ax0 and ax1 < bx1 and by0 < ay0 and ay1 < by1
    m = ax0 < bx0 and bx1 < ax1 and ay0 < by0 and by1 < ay1
    if not c: return "dc"
    if not o: return "ec"
    if p and q: return "eq"
    if p: return "ntpp" if n else "tpp"
    if q: return "ntppi" if m else "tppi"
    return "po"

def rects(lo=0, hi=4):
    xs = [(a, b) for a in range(lo, hi + 1) for b in range(lo, hi + 1) if a < b]
    return [(x0, x1, y0, y1) for (x0, x1) in xs for (y0, y1) in xs]

def canonical(r, s):
    """Representative of the converse orbit {(r,s), (s˘,r˘)}."""
    other = (CONVERSE[s], CONVERSE[r])
    return min((r, s), other, key=lambda k: (RELS.index(k[0]), RELS.index(k[1])))
