"""Exact ordinary certificates for 255 actual xi7 at one fixed source node.

Numerical current7 and actual-zero7 envelopes are pinned inputs. Their separate
geometry replay reconstructs them; this arithmetic consumer does not rerun it.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse, hashlib, json, runpy

ROOT = Path(__file__).resolve().parent
BOUNDS_SHA256 = '5f506cd32264ae3c247c3055b2dd84004625d6fb7fa7aebec22fac2f365b7065'
BASE_VERIFY_SHA256 = 'a519fef29bb1fb76370ea1ca4d252365205093448d53b4442fd445d80e30018f'
BASE_REPLAY_SHA256 = 'd0c5dbf54089cf05da07e562b34b639890fb722fbf9efb96bc8a5068c729ed9a'
ETAS = (1, 4, 7, 8, 11, 13, 14)
DOMAIN = tuple(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), ETAS))
STAGES = ((11, 4), (13, 4), (17, 8), (19, 8), (29, 16))
RESERVE = F(135, 4)
UNSUPPLIED = {(1, 4, 7, 14), (2, 4, 2, 14), (2, 4, 5, 14)}

def demand(condition, message):
    if not condition:
        raise ValueError(message)

def load_inputs():
    raw = (ROOT / 'bounds.json').read_bytes()
    demand(hashlib.sha256(raw).hexdigest() == BOUNDS_SHA256, 'pinned ordinary inputs')
    data = json.loads(raw)
    demand(data['model'] == dict(core=[3,5,7,11,13,17,19,29], node=[2,4,1,8,1,2,1,0,13], thresholds=[2,4,4,8,8,16], query=16), 'fixed source, complete schedule and query')
    return data

def envelope(record):
    e = record['zero_envelope']
    env = F(e['mass']), F(e['whole']), {F(t):F(a) for t,a in e['values'].items()}
    demand(set(env[2]) == set(map(F, range(1,29))) and env[0] > 0 and env[1] > 0 and all(a >= 0 for a in env[2].values()), 'complete actual-zero7 envelope')
    return env

def continuation(v, components):
    # Each component is (complete multiplier law, source envelope, scalar).
    losses = []
    for p, t in STAGES:
        h = sum((scale * v['hinge'](t, dist, env) for dist, env, scale in components), F(0))
        losses.append(v['ceil_fraction'](h / (p - 1 - t)))
        components = [(v['mul'](dist, v['full'](p,t)), env, scale) for dist,env,scale in components]
    h16 = sum((scale * v['hinge'](16,dist,env) for dist,env,scale in components), F(0))
    return losses, h16

def certificate(v, current, losses, h16):
    live = RESERVE - current - sum(losses, F(0))
    slack = 14 * live - h16
    passed = live > 0 and slack > 0
    return dict(passes=passed, loss_uppers=list(map(str,losses)), H16=str(h16), live_lower=str(live), slack_lower=str(slack), query_upper=str(v['ceil_fraction'](15+h16/live)) if live > 0 else None)

def verify(base):
    data = load_inputs()
    for name, pin in (('verify.py', BASE_VERIFY_SHA256), ('geometry_replay.py', BASE_REPLAY_SHA256)):
        demand(hashlib.sha256((base/name).read_bytes()).hexdigest() == pin, 'pinned base '+name)
    v = runpy.run_path(str(base/'verify.py'))
    current = {tuple(r['xi7']):F(r['current7']) for r in data['current7']}
    demand(len(data['current7']) == 280 and set(current) == set(DOMAIN) and all(x >= 0 for x in current.values()), 'all280 distinct actual current7 inputs')
    full7 = v['full'](7,2)
    demand(full7[0][1] == F(11,14) and full7[1] == F(5,4) and full7[2] == 1, 'full7 complete mass and moment')
    demand(all(full7[0][m] == v['POS7'][0][m] for m in range(2,v['CUTOFF'])) and full7[1]-F(11,14) == v['POS7'][1] and 1-F(11,14) == v['POS7'][2], 'unchanged complete positive7 part')
    demand(all(0 <= F(k,14) <= full7[0][1] for k in (11,11,9,6,3)), 'pointwise zero7 domination')
    ordinary = v['ENVS'][(0,0,0)]
    common_loss, common_h = continuation(v, [(full7,ordinary,F(1))])
    flat_rows = [dict(xi7=list(xi),current7=str(current[xi]),**certificate(v,current[xi],common_loss,common_h)) for xi in DOMAIN]
    flat_pass = {tuple(r['xi7']) for r in flat_rows if r['passes']}
    supplied = {tuple(r['xi7']):r for r in data['actual_zero7']}
    demand(len(data['actual_zero7']) == 37 and set(supplied) == set(DOMAIN)-flat_pass-UNSUPPLIED, 'the declared37 distinct actual-zero7 comparisons')
    actual_rows = []
    for xi in DOMAIN:
        if xi in supplied:
            losses, h = continuation(v, [(v['POS7'],ordinary,F(1)), (v['UNIT'],envelope(supplied[xi]),F(1,14))])
            actual_rows.append(dict(xi7=list(xi),current7=str(current[xi]),**certificate(v,current[xi],losses,h)))
    actual_pass = {tuple(r['xi7']) for r in actual_rows if r['passes']}
    demand(len(flat_pass) == 240 and len(actual_pass) == 15 and not flat_pass & actual_pass, 'disjoint240 plus15 certified actual sources')
    certified = flat_pass | actual_pass
    pending = set(DOMAIN)-certified
    demand(len(certified) == 255 and len(pending) == 25, 'exact certified and unclaimed source counts')
    selected = [r for r in flat_rows if r['passes']] + [r for r in actual_rows if r['passes']]
    worst = max(selected, key=lambda r:F(r['query_upper']))
    return dict(scope='One fixed A1 node, 255 declared actual xi7, all280^5 later physical labels each. The other25 xi7 are not certified by this package; no claim of infeasibility and no Lean verification.', model=data['model'], flat_certified=240, actual_zero_certified=15, certified_sources=255, future_parameter_tuples_per_source=280**5, certified_parameter_tuples=255*280**5, current7_strict_common_limit=str(RESERVE-sum(common_loss,F(0))-common_h/14), common_loss_uppers=list(map(str,common_loss)), common_H16=str(common_h), worst=worst, unclaimed_xi7=[list(x) for x in DOMAIN if x in pending], certified=[dict(xi7=r['xi7'],route='full7') for r in flat_rows if r['passes']]+[dict(xi7=r['xi7'],route='actual-zero7') for r in actual_rows if r['passes']], actual_zero_comparisons=actual_rows, bounds_sha256=BOUNDS_SHA256, verification='Exact rational combination and source-domain checks. Geometric maxima are inherited pinned inputs with a separate cache-only-by-default replay.')

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--base',type=Path,default=ROOT.parent/'missing23-eta14')
    p.add_argument('--output',type=Path)
    args = p.parse_args()
    result = verify(args.base)
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')
