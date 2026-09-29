"""Refine20 source-case bounds in Schroeder edition1.0.1's SAME capped source.

Geometric helper routines below are adapted from Michael Schroeder's
checks/verify.py, Copyright (c) 2026 Michael Schroeder, MIT license.
The full license is supplied in e7_refined_source_MIT.txt. Their finite maxima use the author's
geometry.cpp, freshly compiled and run from the supplied archive. Explicit
ValueError guards replace assertions and remain active under Python -O.

The existing all-height source construction, source-case completeness,
vertex interpolation and compatible-screen theorems remain attributed.
This consumer changes no kernel, phase, padding or conditional cap.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import time
P = (7, 11, 13, 17, 19, 23)
T = (2, 4, 4, 8, 8, 12)
CAP = tuple((F(p - 1, p - 1 - t) for p, t in zip(P, T)))
RATIOS = tuple(sorted({F(t, m) for t in T for m in range(1, t)}))
MODS = (3, 9, 27, 5, 15, 45)
REGIONS = tuple(product((False, True), repeat=2))
PROJECTIONS = tuple(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
ROWS3 = tuple((r for r in range(27) if r % 3 and r % 9 != 1 and (r != 4)))
ETA165 = (1, 4, 7, 8, 11, 13, 14)
INTEGER_QUERIES = 0
GENERATED = 0
GEOMETRY_SIZES = {}

def up(x):
    if not x >= 0:
        raise ValueError('Author geometric interface or exact identity failed: x >= 0')
    return F(-(-x.numerator * 10 ** 10 // x.denominator), 10 ** 10)

def depth(p, positive, stop):
    if not positive:
        return (((0, F(1)),), (F(1), F(0)), (F(0), F(0)), (F(1), F(0)))
    atoms = tuple(((j, F(p - 1, p ** (j + 1))) for j in range(1, stop)))
    retained = (sum((w for j, w in atoms)), sum((j * w for j, w in atoms)))
    tail = (F(1, p ** stop), F(1, p ** stop) * (stop + F(1, p - 1)))
    whole = (F(1, p), F(1, p - 1))
    if not tuple((retained[i] + tail[i] for i in range(2))) == whole:
        raise ValueError('Author geometric interface or exact identity failed: tuple((retained[i] + tail[i] for i in range(2))) == whole')
    return (atoms, retained, tail, whole)

@lru_cache(None)
def cells(a, b, r):
    return tuple((x for x in range(135) if x % 3 and x % 9 != 1 and (x % 27 != b) and x % 5 and (x % 15 != a) and (r < 0 or x % 45 != r)))

def rreps(a, b, c):
    representatives = {}
    for r in range(45):
        if r % 3 and r % 9 != 1 and r % 5 and (r % 15 != a):
            sig = (r % 3, r % 9 == b % 9, r % 5 == a, r % 5 == c)
            representatives.setdefault(sig, r)
    return tuple(representatives.values())

def weights(node, region):
    a, b, c, r, j, d, k, i, z = node
    return tuple(((1 if region[0] else 4 - 3 * (x % 27 == z)) * (1 if region[1] else 16 - 4 * (x % 5 == c) - (x % 5 == j) - (4 - i) * (d != 0 and x % 3 == d and (x % 5 == k))) for x in cells(a, b, r)))

def counts(cs, projection):
    return tuple((sum((x % m == v for m, v in zip((3, 5, 9, 15), projection))) for x in cs))

def coefficients(mode, u, v, m=1):
    if mode in ('current', 'common'):
        return (F(1, 7), F(1, 7), 1 + u, v + F(1, 7), v + F(1, 7), 1 + v, (1 + u) * (1 + v))
    co = [m, m, m * (1 + u), m * (1 + v), m * (1 + v), m * (1 + v), m * (1 + u) * (1 + v)]
    if mode == 'label':
        co[4] -= F(10, 11)
    return tuple(co)

def geometry(cs, ws, mode, region, projection, m, eta):
    global INTEGER_QUERIES, GENERATED
    if not (1 <= len(cs) <= 135 and len(cs) == len(ws)):
        raise ValueError('Author geometric interface or exact identity failed: 1 <= len(cs) <= 135 and len(cs) == len(ws)')
    if not all((0 <= w <= 704 for w in ws)):
        raise ValueError('Author geometric interface or exact identity failed: all((0 <= w <= 704 for w in ws))')
    uv = tuple(product(range(1, 12) if region[0] else (0,), range(1, 9) if region[1] else (0,)))
    ts = RATIOS if mode == 'ordinary' else (F(1 if mode == 'current' else 2 if mode == 'common' else 4),)
    off = tuple((6 * s for s in counts(cs, projection))) if mode == 'current' else tuple((10 * (x % 15 == eta) for x in cs)) if mode == 'label' else (0,) * len(cs)
    lines = [str(len(cs))] + [f'{x} {w} {o}' for x, w, o in zip(cs, ws, off)]
    labels = []
    for u, v in uv:
        co = coefficients(mode, u, v, m)
        for t in ts:
            den = t.denominator if mode == 'ordinary' else 11 if mode == 'label' else 7
            base = den if mode == 'ordinary' else 11 * m if mode == 'label' else 13 if mode == 'common' else 0
            ico = [int(den * x) for x in co]
            if not all((F(x, den) == y for x, y in zip(ico, co))):
                raise ValueError('Author geometric interface or exact identity failed: all((F(x, den) == y for x, y in zip(ico, co)))')
            if not (den > 0 and t >= 0 and all((x >= 0 for x in ico))):
                raise ValueError('Author geometric interface or exact identity failed: den > 0 and t >= 0 and all((x >= 0 for x in ico))')
            if not 0 <= base + max(off, default=0) + sum(ico) < 8192:
                raise ValueError('Author geometric interface or exact identity failed: 0 <= base + max(off, default=0) + sum(ico) < 8192')
            lines.append(' '.join(map(str, [len(labels), den, base, *ico, int(den * t)])))
            labels.append((u, v, t, den))
    payload = '\n'.join(lines) + '\n'
    key = sha256(payload.encode()).hexdigest()
    GEOMETRY_SIZES[key] = len(labels)
    path = CACHE / (key + '.json')
    if path.exists():
        raw = json.loads(path.read_text())
    else:
        run = subprocess.run([str(ROOT / 'checks/geometry')], input=payload, capture_output=True, text=True, check=True)
        raw = [list(map(int, line.split())) for line in run.stdout.splitlines()]
        path.write_text(json.dumps(raw, separators=(',', ':')) + '\n')
        GENERATED += 1
    if not len(raw) == len(labels):
        raise ValueError('Author geometric interface or exact identity failed: len(raw) == len(labels)')
    if not all((row[0] == i and row[1] == lab[3] and (0 <= row[2] < 2 ** 30) for i, (row, lab) in enumerate(zip(raw, labels)))):
        raise ValueError('Author geometric interface or exact identity failed: all((row[0] == i and row[1] == lab[3] and (0 <= row[2] < 2 ** 30) for i, (row, lab) in enumerate(zip(raw, labels))))')
    INTEGER_QUERIES += len(raw)
    table = {(u, v, t): F(row[2], den) for (u, v, t, den), row in zip(labels, raw)}
    inc = tuple((max((sum((w for x, w in zip(cs, ws) if x % g == rr)) for rr in range(g))) for g in MODS))
    mass, maxweight = (sum(ws), max(ws))
    offset = F(1, 7) * sum((w * o for w, o in zip(ws, off))) if mode == 'current' else F(1, 11) * sum((w * o for w, o in zip(ws, off))) if mode == 'label' else F(0)
    base = F(13, 7) if mode == 'common' else 0 if mode == 'current' else m

    def linear(u, v):
        co = coefficients(mode, u, v, m)
        return base * mass + sum((c * h for c, h in zip(co, inc))) + co[6] * maxweight + offset
    return (table, linear, mass, ts)

@lru_cache(maxsize=16000)
def envelope(node, mode='ordinary', projection=(), killed=False, m=1, eta=-1):
    cs = cells(node[0], node[1], node[3])
    un = counts(cs, projection) if projection else ()
    vals = None
    mass = whole = F(0)
    for region in REGIONS:
        ws = weights(node, region)
        if killed:
            ws = tuple((w * (11, 11, 9, 6, 3)[n] for w, n in zip(ws, un)))
        table, linear, g_mass, ts = geometry(cs, ws, mode, region, projection, m, eta)
        if vals is None:
            vals = {t: F(0) for t in ts}
        ud, ur, ut, ua = depth(3, region[0], 12)
        vd, vr, vt, va = depth(5, region[1], 9)
        scale = F(1, (1 if region[0] else 6) * (1 if region[1] else 20))

        def integral(aa, bb):
            return aa[0] * bb[0] * linear(aa[1] / aa[0], bb[1] / bb[0]) if aa[0] and bb[0] else F(0)
        tail = integral(ut, va) + integral(ur, vt)
        if not tail >= 0:
            raise ValueError('Author geometric interface or exact identity failed: tail >= 0')
        mass += scale * ua[0] * va[0] * g_mass
        whole += scale * integral(ua, va)
        for t in ts:
            vals[t] += scale * (sum((p * q * table[u, v, t] for u, p in ud for v, q in vd)) + tail)
    return (mass, whole, vals)

def update(dist, mean, p, cap):
    out = defaultdict(F)
    for m, w in dist.items():
        for e in range(31 // m):
            pr = 1 - cap / p if e == 0 else cap * F(p - 1, p ** (e + 1))
            out[m * (e + 1)] += w * pr
    return (dict(out), mean * (1 + cap / F(p - 1)))

@lru_cache(None)
def distributions(skip7=False):
    dist, mean = ({1: F(1)}, F(1))
    out = []
    for p, cap in zip(P, CAP):
        out.append((dist, mean))
        if not (skip7 and p == 7):
            dist, mean = update(dist, mean, p, cap)
    return tuple(out)

def expectation(env, dist, mean, t):
    mass, whole, vals = env
    low = [(m, w) for m, w in dist.items() if m < t]
    prob = sum((w for m, w in low))
    first = sum((m * w for m, w in low))
    return sum((w * m * vals[F(t, m)] for m, w in low)) + (mean - first) * whole - t * (1 - prob) * mass

def reserve(node):
    a, b, c, r, j, d, k, i, row = node
    z = F(1, 2) if row >= 0 else F(0)
    gamma15 = 3 * (a == 1) + (b % 3 == a % 3) + z * (row % 3 == a % 3)
    gamma45 = F(b % 9 == r % 9) + z * (row % 9 == r % 9)
    D = lambda h: F(c == h, 5) + F(j == h, 20)
    value = F(135, 4) + gamma15 + (9 - gamma15) * D(a)
    if r >= 0:
        value += gamma45 + (3 - gamma45) * D(r % 5)
    if d:
        B = sum((1 - z * (x % 27 == row) for x in cells(a, b, r) if x % 3 == d and x % 5 == k))
        value += F(9, 5) - B * F(4 - i, 20)
    return value

@lru_cache(maxsize=3000)
def ordinary(node):
    env = envelope(node)
    return tuple((up(expectation(env, dist, mean, t) / (p - 1 - t)) for p, t, (dist, mean) in zip(P, T, distributions())))

def spatial(node, projection):
    costs = list(ordinary(node))
    costs[0] = up(envelope(node, 'current', projection)[2][F(1)] / 4)
    env = envelope(node)
    killed = envelope(node, 'ordinary', projection, True)
    for q in range(1, 6):
        dist, mean = distributions(True)[q]
        old = expectation(env, dist, mean, T[q])
        new = expectation(killed, dist, mean, T[q])
        saving = (11 * old - new) / (14 * (P[q] - 1 - T[q]))
        if not saving >= 0:
            raise ValueError('Author geometric interface or exact identity failed: saving >= 0')
        costs[q] -= saving
        if not costs[q] >= 0:
            raise ValueError('Author geometric interface or exact identity failed: costs[q] >= 0')
    return tuple(costs)

def fixed165(node, projection, eta):
    total = envelope(node, 'label', projection, True, 1, eta)[2][F(4)] / 14
    total += F(9, 49) * envelope(node, 'label', projection, False, 2, eta)[2][F(4)]
    total += F(9, 343) * envelope(node, 'label', projection, False, 3, eta)[2][F(4)]
    mass, whole, _ = envelope(node)
    cs = cells(node[0], node[1], node[3])
    correction = F(0)
    for region in REGIONS:
        ws = weights(node, region)
        scale = F(1, (1 if region[0] else 6) * (1 if region[1] else 20))
        scale *= (F(1, 3) if region[0] else 1) * (F(1, 5) if region[1] else 1)
        h15 = max((sum((w for x, w in zip(cs, ws) if x % 15 == r)) for r in range(15)))
        correction += scale * (sum((w for x, w in zip(cs, ws) if x % 15 == eta)) - h15)
    total += F(25, 1372) * whole + F(3, 686) * (F(10, 11) * correction - 4 * mass)
    return up(total / 6)

import tempfile
import zipfile
from io import BytesIO

BASELINE_DIGEST = 'a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac'
TARGET_UNITS = 12
NEW_SOURCE_MASS = F(1, 11250)
EXPECTED_PHASES = {'basic':16,'basic75':4,'mixed':420,'anchor':184,
                   'coarse':25840,'spatial':1003,'pure3':506,'closing':28}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def parse_baseline(raw):
    need(sha256(raw).hexdigest() == BASELINE_DIGEST,
         'Author original certificate DATA bytes match the attributed baseline')
    data=json.loads(raw)
    need(data['mass_denominator']==135000 and data['row_format']==
         ['phase','configuration','reserve_lower','loss_upper'], 'Baseline units and schema')
    rows=data['rows']
    need(len(rows)==28001 and Counter(r[0]for r in rows)==EXPECTED_PHASES,
         'All28001 original source-case certificate rows are present')
    need(len({(r[0],tuple(r[1]))for r in rows})==len(rows), 'Baseline row identities unique')
    need(all(type(x)is int for r in rows for x in r[2:]) and
         min(r[2]-r[3]for r in rows)==4, 'Original exact integer surplus four')
    weak=[r for r in rows if r[2]-r[3]<TARGET_UNITS]
    need(len(weak)==20 and Counter(r[0]for r in weak)=={'anchor':4,'coarse':4,'pure3':12},
         'Exactly20 weak leaves require stronger bounds')
    retained=[r for r in rows if r[2]-r[3]>=TARGET_UNITS]
    need(len(retained)==27981 and min(r[2]-r[3]for r in retained)==12,
         'Every untouched leaf has surplus at least twelve')
    return data,weak,retained


def checked_minimum(values):
    need(bool(values) and all(isinstance(x,F)for x in values), 'Nonempty exact case family')
    value=min(values)
    need(value>=F(TARGET_UNITS,1000), 'Every refined case pays twelve thousandths')
    return value


def refine(raw):
    data,weak,retained=parse_baseline(raw)
    records=[]
    for phase,key,rl,lu in weak:
        if phase=='anchor':
            need(len(key)==5,'Old anchor key has five coordinates')
            node0=(2,4,1,*key,-1)
            R0,L0=reserve(node0),ordinary(node0)
            need(1000*R0>=rl and 1000*sum(L0)<=lu,
                 'Anchor key reconstructs its original coarse comparison')
            cases=[]
            for z in ROWS3:
                node=(2,4,1,*key,z)
                R,L=reserve(node),ordinary(node)
                cases.append({'pure3_row':z,'reserve':R,'six_losses':L,'surplus':R-sum(L)})
            method='All14 pure3 budget vertices, unchanged ordinary six losses'
        elif phase=='coarse':
            need(len(key)==9,'Old coarse key has five source and four projection coordinates')
            node=(2,4,1,*key[:5],-1);proj=tuple(key[5:])
            need(proj in PROJECTIONS,'Same actual7 projections in permitted source domain')
            R,L=reserve(node),spatial(node,proj)
            need(1000*R>=rl,'Same source reserve')
            cases=[{'projection':proj,'reserve':R,'six_losses':L,'surplus':R-sum(L)}]
            method='Spatial7 current loss and its matching first-hit continuation'
        else:
            need(phase=='pure3'and len(key)==10,'Old pure3 key has ten coordinates')
            node=(2,4,1,*key[:5],key[-1]);proj=tuple(key[5:9])
            need(node[-1]in ROWS3 and proj in PROJECTIONS,'Actual source/projection domain')
            cs=cells(node[0],node[1],node[3])
            need(tuple(sorted({x%15 for x in cs}))==ETA165,
                 'All live15 projections represented; excluded projections have zero background')
            R,L=reserve(node),spatial(node,proj)
            need(1000*R>=rl and 1000*sum(L)<=lu,'Pure3 key reconstructs its original comparison')
            cases=[]
            for eta in ETA165:
                label=fixed165(node,proj,eta)
                need(label<=L[1],'Fixed original165 comparison improves same stage11 bound')
                refined=L[:1]+(label,)+L[2:]
                cases.append({'eta165':eta,'reserve':R,'six_losses':refined,'surplus':R-sum(refined)})
            method='One fixed165 projection throughout each auxiliary expectation; all7 live projections'
        minimum=checked_minimum([r['surplus']for r in cases])
        records.append({'phase':phase,'original_key':key,'original_integer_surplus':rl-lu,
                        'method':method,'refined_surplus':minimum,'cases':cases})
    need(len(records)==20,'Every and only weak source leaf refined')
    need(NEW_SOURCE_MASS==F(TARGET_UNITS,data['mass_denominator']), 'Mass conversion by135-cell units')
    return {
      'scope':'Same Schroeder1.0.1 actual full-height eight-prime source, same kernels, '
              'initial pure anchor, actual completion, charged7 padding, global original '
              'phases and conditional caps; sharper same-source case bounds only.',
      'source_construction_and_case_completeness':'Attributed source theorems, not replayed or Lean-verified here.',
      'baseline_certificate_data_sha256':BASELINE_DIGEST,
      'baseline_count':28001,'unchanged_count':27981,'refined_count':20,
      'baseline_minimum_integer_surplus':4,'unchanged_minimum_integer_surplus':12,
      'guaranteed_integer_surplus':12,'guaranteed_same_source_mass':NEW_SOURCE_MASS,
      'reference_primes':(3,5,7,11,13,17,19,23),
      'conditional_caps':list(zip(P,CAP)),
      'refinements':records,
      'fresh_geometry_batches':len(GEOMETRY_SIZES),
      'fresh_distinct_integer_queries':sum(GEOMETRY_SIZES.values()),
      'integer_geometry_program':'Author geometry.cpp freshly compiled; no program-byte acceptance gate.',
      'auxiliary_infinite_remainders':'Exact geometric mass and first-moment tails retained at every envelope.',
      'all_original_finite_heights':True,'lean_verification':False,
    }


def load_archive(source):
    with zipfile.ZipFile(source) as archive:
        raw=archive.read('nine-prime-support/certificate/integer_certificate.json')
        geometry_source=archive.read('nine-prime-support/checks/geometry.cpp')
    parse_baseline(raw)
    return raw,geometry_source


def validate_retained(fresh,retained):
    need(fresh==retained, 'Fresh exact refinement equals retained result in every branch')


def self_test(raw,result):
    def forged_archive():
        changed=json.loads(raw)
        changed['rows'][0][2]+=1
        stream=BytesIO()
        with zipfile.ZipFile(stream,'w')as archive:
            archive.writestr('nine-prime-support/certificate/integer_certificate.json',json.dumps(changed))
            archive.writestr('nine-prime-support/checks/geometry.cpp','rejected before compilation')
        stream.seek(0)
        load_archive(stream)
    forged_mass=json.loads(json.dumps(result))
    forged_mass['guaranteed_same_source_mass']='1/100'
    forged_branch=json.loads(json.dumps(result))
    forged_branch['refinements'][0]['cases'][0]['surplus']='1'
    failures=[]
    for name,op in [
        ('changed original certificate data',lambda:parse_baseline(raw+b' ')),
        ('empty refinement family',lambda:checked_minimum([])),
        ('insufficient refined surplus',lambda:checked_minimum([F(11,1000)])),
        ('inexact numerical input',lambda:checked_minimum([0.02])),
        ('forged archive certificate',forged_archive),
        ('forged retained mass',lambda:validate_retained(result,forged_mass)),
        ('forged retained branch',lambda:validate_retained(result,forged_branch)),
    ]:
        try:op()
        except ValueError:failures.append(name)
        else:raise ValueError('Invalid input accepted: '+name)
    return failures


def main():
    global ROOT,CACHE
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--write-result',type=Path)
    parser.add_argument('--result',type=Path)
    parser.add_argument('--self-test',action='store_true')
    args=parser.parse_args()
    raw,geometry_source=load_archive(args.archive)
    compiler=shutil.which('c++')or shutil.which('clang++')or shutil.which('g++')
    need(compiler is not None,'C++17 compiler available for fresh exact geometry')
    with tempfile.TemporaryDirectory(prefix='e7_refined_source_',dir='/tmp')as scratch:
        ROOT=Path(scratch);CACHE=ROOT/'cache';CACHE.mkdir()
        checks=ROOT/'checks';checks.mkdir()
        (checks/'geometry.cpp').write_bytes(geometry_source)
        subprocess.run([compiler,'-O3','-std=c++17','-fsanitize=undefined',
                        '-fno-sanitize-recover=undefined',str(checks/'geometry.cpp'),
                        '-o',str(checks/'geometry')],check=True)
        result=json.loads(json.dumps(refine(raw),default=str))
    if args.self_test:print(json.dumps({'rejected_invalid_inputs':self_test(raw,result)}))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:validate_retained(result,json.loads((args.result or Path(__file__).with_suffix('.json')).read_text()))
    print(json.dumps({k:result[k]for k in('baseline_count','unchanged_count','refined_count',
        'guaranteed_same_source_mass','fresh_geometry_batches','fresh_distinct_integer_queries',
        'lean_verification')},indent=2))

if __name__=='__main__':main()
