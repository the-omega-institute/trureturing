#!/usr/bin/env python3
"""Refine the only surviving fourth-vector tube and exclude (6,6,6,1).

Reuses the exact circle-arc support and sublevel Krawczyk owners. No stored
PASS or sampled root list is used as a coverage proof. Without --full-cover,
the output is a conditional finite/local certificate only. The C++ and
analytic transfer are not Lean-kernel-verified.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import check_real_x_arc_constellation as arc

RADIUS = F(1, 16)
REFINED_RADIUS = F(1, 32)
TAU = F(1, 256)
ETA = TAU * TAU
EPSILON = F(1, 128)
SIGMA = F(3, 4096)
LABEL = 5


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def asymmetric_relative_arc(t, tsign, rt, s, ssign, rs):
    """Endpoints plus rational guards for unequal Cayley radii."""
    require(rt > 0 and rs > 0, 'nonpositive radius')
    tl, th, sl, sh = t-rt, t+rt, s-rs, s+rs
    guards = [(min(1+th*tl, 1+th*th), min(1+sl*sl, 1+sl*sh)),
              (min(1+tl*tl, 1+tl*th), min(1+sh*sl, 1+sh*sh))]
    for a, b in guards:
        require(a > 0 and b > 0 and (th-tl)*(sh-sl) < a*b,
                'unequal-radius arc membership not certified')
    lo = arc.mul(arc.conj(arc.cayley(th, tsign)), arc.cayley(sl, ssign))
    hi = arc.mul(arc.conj(arc.cayley(tl, tsign)), arc.cayley(sh, ssign))
    require(arc.cross(lo, hi) > 0 and arc.dot(lo, hi) > 0,
            'not an oriented short relative arc')
    return lo, hi


def overlap_bounds(x, rx, y, ry):
    arcs, center = [], (F(1), F(0))
    for (t, tsign), (s, ssign) in zip(x, y):
        arcs.append(asymmetric_relative_arc(t, tsign, rx, s, ssign, ry))
        center = arc.add(center, arc.mul(arc.conj(arc.cayley(t, tsign)),
                                        arc.cayley(s, ssign)))
    directions = [(F(1), F(0))]
    if center != (0, 0):
        directions.append(center)
    lower, upper = F(0), F(1)
    for g in directions:
        ig = (-g[1], g[0])
        real, imag = [g[0], g[0]], [ig[0], ig[0]]
        for lo, hi in arcs:
            r, s = arc.projection(lo, hi, g), arc.projection(lo, hi, ig)
            real = [real[j]+r[j] for j in (0, 1)]
            imag = [imag[j]+s[j] for j in (0, 1)]
        r, s = arc.square_range(tuple(real)), arc.square_range(tuple(imag))
        den = 36*arc.dot(g, g)
        require(den > 0, 'zero projection direction')
        lower = max(lower, (r[0]+s[0])/den)
        upper = min(upper, (r[1]+s[1])/den)
    require(lower <= upper, 'inconsistent overlap enclosure')
    scale = 1 << 60
    return (F(lower.numerator*scale//lower.denominator, scale),
            F(-((-upper.numerator*scale)//upper.denominator), scale))


def common_partners(A, B):
    cliques = arc.prior.enumerate_six_cliques(A)
    remaining = []
    for c in cliques:
        mask = (1 << 60)-1
        for i in c:
            mask &= B[i]
        if mask:
            remaining.append([list(c), list(arc.prior.vertices(mask))])
    return cliques, remaining


# The exact sublevel_krawczyk definition is taken byte-for-byte from the
# existing source prefix; this driver only changes the initial/target sets.
LOCAL_MAIN = r'''
int main(int argc,char**argv){try{
 if(argc!=6)throw runtime_error("centers label epsilon_bits target_bits cap");
 seed();load_roots(argv[1]);int label=stoi(argv[2]),eb=stoi(argv[3]),tb=stoi(argv[4]);long cap=stol(argv[5]);
 if(label<0||label>=60||eb<1||eb>39||tb<4||tb>30||cap<1)throw runtime_error("invalid local input");
 auto it=find_if(roots.begin(),roots.end(),[&](Root const&r){return r.id==label;});
 if(it==roots.end())throw runtime_error("missing label");auto r=*it;Box initial,target;
 for(int j=0;j<5;j++){ll m=mid(r.x[j]);initial[j]=I(checked((wide)m-(ONE>>4)),checked((wide)m+(ONE>>4)));target[j]=I(checked((wide)m-(ONE>>tb)),checked((wide)m+(ONE>>tb)));}
 auto contained=[&](Box const&X){for(int j=0;j<5;j++)if(X[j].l<target[j].l||X[j].h>target[j].h)return false;return true;};
 vector<Node> pending{{initial,0}};long nodes=0,excluded=0,inside=0,unresolved=0;ll eps=ONE>>eb;
 while(!pending.empty()&&nodes<cap){auto[X,depth]=pending.back();pending.pop_back();nodes++;
  if(contained(X)){inside++;continue;}
  I f[5];eval(X,r.mask,f,nullptr);bool no=false;for(auto v:f)no|=v.l>eps||v.h<-eps;
  if(no){excluded++;continue;}
  Kr k;if(sublevel_krawczyk(X,r.mask,eps,k)){
   bool empty=false;for(int j=0;j<5;j++)empty|=k.k[j].h<X[j].l||k.k[j].l>X[j].h;
   if(empty){excluded++;continue;}
   Box Y;bool shrink=false;for(int j=0;j<5;j++){Y[j]=I(max(X[j].l,k.k[j].l),min(X[j].h,k.k[j].h));shrink|=((wide)5*(Y[j].h-Y[j].l)<(wide)3*(X[j].h-X[j].l));}
   if(contained(Y)){inside++;continue;}
   if(shrink){pending.push_back({Y,depth+1});continue;}
  }
  int j=0;for(int k=1;k<5;k++)if(X[k].h-X[k].l>X[j].h-X[j].l)j=k;
  ll m=mid(X[j]);if(depth>180||m<=X[j].l||m>=X[j].h){unresolved++;continue;}
  Box Y=X;Y[j].l=m;X[j].h=m;pending.push_back({Y,depth+1});pending.push_back({X,depth+1});
 }
 bool pass=pending.empty()&&unresolved==0;
 cout<<"{\"status\":\""<<(pass?"REFINEMENT_COVERED":"INCOMPLETE")<<"\",\"label\":"<<label<<",\"epsilon_bits\":"<<eb<<",\"outer_bits\":4,\"target_bits\":"<<tb<<",\"nodes\":"<<nodes<<",\"excluded\":"<<excluded<<",\"inside\":"<<inside<<",\"pending\":"<<pending.size()<<",\"unresolved\":"<<unresolved<<"}\n";
 return pass?0:2;
}catch(exception const&e){cerr<<e.what()<<'\n';return 1;}}
'''


def prepare_local(scriptdir, output):
    source = scriptdir/'check_real_x_residual_barrier.cpp'
    raw = source.read_text()
    marker = 'int main(int argc,char** argv)'
    require(raw.count(marker) == 1, 'sublevel source boundary changed')
    prefix = raw.split(marker)[0]
    require('bool sublevel_krawczyk(' in prefix and
            'Cpre[i][a]*I(-epsilon,epsilon)' in prefix,
            'sublevel enclosure owner is missing')
    cpp = output/'local_refinement.cpp'
    cpp.write_text(prefix+LOCAL_MAIN)
    binary = (output/'local_refinement').resolve()
    subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra',
                    '-I', str(scriptdir), str(cpp), '-o', str(binary)], check=True)
    return binary


def local_refinement(binary, centers, cap, label=LABEL, target_bits=5):
    done = subprocess.run([str(binary), str(centers.resolve()), str(label), '7',
                           str(target_bits), str(cap)], check=True,
                          text=True, stdout=subprocess.PIPE)
    r = json.loads(done.stdout)
    require(r['status'] == 'REFINEMENT_COVERED' and
            r['pending'] == r['unresolved'] == 0 and
            r['label'] == label and r['epsilon_bits'] == 7 and
            r['outer_bits'] == 4 and r['target_bits'] == target_bits,
            'local refinement did not complete')
    return r


def full_cover(scriptdir, centers, output, jobs, cap):
    source = scriptdir/'check_real_x_residual_barrier.cpp'
    binary = (output/'global_sublevel').resolve()
    subprocess.run(['g++', '-O3', '-std=c++17', '-Wall', '-Wextra',
                    str(source), '-o', str(binary)], check=True)
    def chart(k):
        target = (output/f'chart_{k:02d}.json').resolve()
        target.unlink(missing_ok=True)
        subprocess.run([str(binary), str(centers.resolve()), str(k), str(cap),
                        '7', '4', str(target), '--raw-tube-cover'],
                       stdout=subprocess.DEVNULL, check=True)
        return json.loads(target.read_text())
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        reports = list(pool.map(chart, range(32)))
    require(len(reports) == 32 and {r['chart'] for r in reports} == set(range(32)),
            'not all global charts are present')
    for r in reports:
        require(r['status'] == 'SUBLEVEL_COVERED' and
                r['pending'] == r['unresolved'] == 0 and
                r['epsilon_bits'] == 7 and r['guard_radius_bits'] == 4 and
                r['dyadic_bits'] == 40 and r['tube_uniqueness_checked'] is False,
                'incomplete or mismatched global coverage')
    return {'charts': 32, 'nodes': sum(r['nodes'] for r in reports),
            'pending': 0, 'unresolved': 0, 'epsilon_bits': 7,
            'outer_tube_bits': 4, 'tube_uniqueness_used': False}


def run(centers, output, replay_global=False, jobs=4, cap=1500000):
    require(__debug__, 'the reused interval owners require ordinary Python')
    require(1 <= jobs <= 32 and cap > 0, 'invalid resource budget')
    require(arc.RADIUS == RADIUS and arc.TAU == TAU and arc.ETA == ETA,
            'upstream arc constants changed')
    output.mkdir(parents=True, exist_ok=True)
    (output/'verification.json').unlink(missing_ok=True)
    scriptdir = Path(__file__).resolve().parent
    values = arc.read_centers(centers)
    A, B, original_bounds, same = arc.relations(values)
    first, before = common_partners(A, B)
    require({j for _, w in before for j in w} == {LABEL},
            'more than the certified single refinement is needed')
    binary = prepare_local(scriptdir, output)
    local = local_refinement(binary, centers, cap)
    (output/'local_refinement.json').write_text(json.dumps(local, indent=2)+'\n')
    removed, refined_bounds = [], []
    for i in range(60):
        lo, hi = overlap_bounds(values[i], REFINED_RADIUS if i == LABEL else RADIUS,
                                values[LABEL], REFINED_RADIUS)
        refined_bounds.append([i, str(lo), str(hi)])
        if lo > F(1, 6)+TAU or hi < F(1, 6)-TAU:
            if B[i] & (1 << LABEL):
                removed.append(i)
            B[i] &= ~(1 << LABEL)
            B[LABEL] &= ~(1 << i)
    _, after = common_partners(A, B)
    require(not after, 'a possible fourth vector remains')
    require(same > F(3, 4) > ETA and TAU <= F(1, 4), 'overlap budget')
    transfer = TAU+SIGMA*(5+SIGMA)
    require(transfer < EPSILON, 'matrix perturbation budget exhausted')
    (output/'refined_overlaps.json').write_text(json.dumps(refined_bounds, indent=2)+'\n')
    (output/'relations.json').write_text(json.dumps({'orthogonality': A,
        'refined_unbiasedness': B, 'first_cliques': first}, indent=2)+'\n')
    result = {'status': 'FINITE_AND_LOCAL_REFINEMENT_VERIFIED',
        'seed_field': 'Q(i,sqrt(21))', 'original_tubes': 60,
        'whole_tube_pairs': len(original_bounds),
        'orthogonality_edges': sum(a.bit_count() for a in A)//2,
        'first_six_cliques': len(first), 'before_nonempty_partner_sets': len(before),
        'refined_label': LABEL, 'original_radius': str(RADIUS),
        'refined_radius': str(REFINED_RADIUS), 'local_cover': local,
        'removed_unbiased_neighbors': removed, 'remaining_partner_sets': 0,
        'candidate_tolerance': str(TAU), 'orthogonality_threshold': str(ETA),
        'seed_sublevel': str(EPSILON), 'column_l1_radius': str(SIGMA),
        'entrywise_radius': str(SIGMA/6), 'transferred_residual_upper': str(transfer),
        'partial_constellation_energy_lower_bound': str(ETA),
        'global_cover_replayed': False, 'lean_kernel_verified': False,
        'scope': 'one additional vector after a six-frame; all seven vectors exactly coordinate-flat',
        'hashes': {p.name: digest(p) for p in [Path(__file__), Path(arc.__file__), centers,
            scriptdir/'check_real_x_residual_barrier.cpp', scriptdir/'check_real_x_global_cover.cpp']}}
    if replay_global:
        result['global_cover'] = full_cover(scriptdir, centers, output, jobs, cap)
        result['global_cover_replayed'] = True
        result['status'] = 'COMPUTATIONAL_STRONG_UNEXTENDIBILITY_VERIFIED'
    (output/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('centers', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--full-cover', action='store_true')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--max-nodes', type=int, default=1500000)
    a = p.parse_args()
    try:
        print(json.dumps(run(a.centers, a.output, a.full_cover, a.jobs, a.max_nodes), indent=2))
    except Exception as e:
        a.output.mkdir(parents=True, exist_ok=True)
        (a.output/'verification.json').unlink(missing_ok=True)
        (a.output/'failure.json').write_text(json.dumps({'status': 'FAIL', 'error': str(e)})+'\n')
        raise
