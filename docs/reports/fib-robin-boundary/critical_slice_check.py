#!/usr/bin/env python3
"""Replay critical-slice certificate, rebuilding all events and covered ranges.

Separate from producer; shares only the previously retained interval primitives.
Accepts no numerical claim without recreating its outward interval and coverage.
"""
import argparse
import gzip
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import importlib.util
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError('run without -O or PYTHONOPTIMIZE; checks require assertions')
# Resolve only the retained engine beside this source, independent of cwd/PYTHONPATH.
_spec = importlib.util.spec_from_file_location('price_band', Path(__file__).resolve().with_name('price_band.py'))
e = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(e)

I,S,Z,O=e.I,e.SCALE,e.ZERO,e.ONE


def same(w,x):
    assert w==x.wire(),('noncanonical or incorrect interval',w,x.wire())


def pof(x):
    return O/(x*e.logiv(x))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--certificate',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    raw=gzip.decompress(args.certificate.read_bytes()); c=json.loads(raw)
    assert c['schema']=='fib-robin-critical-slice-v1'
    assert c['scale']==str(S) and c['start_n']==40000 and c['end_x']==121393
    assert c['gamma_m']==10**6 and c['target']==[51,250000]
    m=c['gamma_m']; h=I(sum(S//k for k in range(1,m+1)),sum(e.ceildiv(S,k) for k in range(1,m+1)))
    base=h-e.lograt(m)
    gamma=I((base-I.rat(1,2*m)).lo,(base-I.rat(1,2*(m+1))).hi)
    same(c['gamma'],gamma)
    start=e.lograt(40000); end=I.rat(121393)
    upper,lower=pof(start),pof(end); target=I.rat(51,250000)
    assert upper.hi<I.rat(1,25).lo
    assert pof(I.rat(121394)).hi<lower.lo
    composites=set()
    primes=[]
    for n in range(2,121394):
        if n in composites: continue
        primes.append(n)
        if n*n<=121393: composites.update(range(n*n,121394,n))
    assert c['primes']==primes
    # Reconstruct the complete set, independently of serialized ordering.
    expected={}; inactive=[]
    for p in primes:
        lp=e.lograt(p); k=1
        while True:
            denominator=sum(p**j for j in range(1,k+1))
            gain=e.lograt(denominator+1,denominator); rate=gain/lp
            if rate.hi<lower.lo:
                inactive.append([p,k,rate.wire()]); break
            assert rate.lo>lower.hi
            expected[p,k]=(lp,gain,rate)
            k+=1
    assert c['first_inactive']==inactive
    assert len(c['layers'])==len(expected)
    seen=set(); previous=None; initial=[]; events=[]
    for item in c['layers']:
        key=item['p'],item['k']; assert key in expected and key not in seen
        seen.add(key); lp,gain,rate=expected[key]
        same(item['logp'],lp); same(item['gain'],gain); same(item['rate'],rate)
        if previous is not None: assert previous.lo>rate.hi
        previous=rate
        if rate.lo>upper.hi: initial.append((key,lp,gain,rate))
        else:
            assert rate.hi<upper.lo
            events.append((key,lp,gain,rate))
    assert seen==set(expected)
    assert c['initial_count']==len(initial)==8
    exponents={}; energy=benefit=Z
    for (p,k),lp,gain,_ in initial:
        assert k==exponents.get(p,0)+1
        exponents[p]=k; energy=energy+lp; benefit=benefit+gain
    assert exponents=={2:4,3:2,5:1,7:1}
    startgap=gamma+e.logiv(e.logiv(start))-benefit+pof(start)*(energy-start)
    same(c['endpoints'][0]['x'],start); same(c['endpoints'][0]['gap'],startgap)
    assert startgap.lo>target.hi
    assert len(c['cells'])==len(events)+1
    expected_critical=[]
    for index,cell in enumerate(c['cells']):
        assert cell['index']==index
        same(cell['energy'],energy); same(cell['benefit'],benefit)
        rate=pof(energy); same(cell['price'],rate)
        high=upper if index==0 else events[index-1][3]
        low=lower if index==len(events) else events[index][3]
        if rate.lo>high.hi: cls='energy_before_cell'
        elif rate.hi<low.lo: cls='energy_after_cell'
        else:
            assert low.hi<rate.lo and rate.hi<high.lo
            cls='strict_self_matching'
            gap=gamma+e.logiv(e.logiv(energy))-benefit
            assert gap.lo>target.hi
            expected_critical.append({'index':index,'energy':energy.wire(),
                'benefit':benefit.wire(),'price':rate.wire(),'gap':gap.wire(),
                'exponents':[[p,k] for p,k in sorted(exponents.items())]})
        assert cell['classification']==cls
        if index<len(events):
            (p,k),lp,gain,_=events[index]
            assert k==exponents.get(p,0)+1
            exponents[p]=k; energy=energy+lp; benefit=benefit+gain
    assert c['critical']==expected_critical
    finalgap=gamma+e.logiv(e.logiv(end))-benefit+pof(end)*(energy-end)
    assert len(c['endpoints'])==2
    same(c['endpoints'][1]['x'],end); same(c['endpoints'][1]['gap'],finalgap)
    assert finalgap.lo>target.hi
    # Divisor sum by an independent multiplicative smallest-prime recurrence.
    spf=list(range(40001))
    for p in range(2,201):
        if spf[p]==p:
            for n in range(p*p,40001,p):
                if spf[n]==n: spf[n]=p
    sigma=[0]*40001; sigma[1]=1
    for n in range(2,40001):
        p=spf[n]; residual=n; power=1; geom=1
        while residual%p==0:
            residual//=p; power*=p; geom+=power
        sigma[n]=geom*sigma[residual]
    nextn=5041
    for block in c['integer_patch']:
        a,b=block['a'],block['b']; assert type(a) is int and type(b) is int
        assert a==nextn and a<=b<=40000
        nmax=max(range(a,b+1),key=lambda n:Fraction(sigma[n],n))
        assert block['maximum_n']==nmax and block['maximum_z']==[sigma[nmax],nmax]
        gap=gamma+e.logiv(e.logiv(e.lograt(a)))-e.lograt(sigma[nmax],nmax)
        same(block['gap'],gap); assert gap.lo>0
        nextn=b+1
    assert nextn==40001
    result={'status':'independent replay passed; not Lean verified',
            'primes':len(primes),'events':len(events),'cells':len(c['cells']),
            'critical_configs':len(expected_critical),'integer_patch_blocks':len(c['integer_patch']),
            'small_integers_independently_recomputed':34960,
            'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (args.out/'check-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
