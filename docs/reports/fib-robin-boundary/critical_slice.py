#!/usr/bin/env python3
"""Critical-cell certificate using integer outward intervals, no floating decisions.

Requires sibling price_band.py (the already retained interval engine).
Produces a complete layer event record and a small independently checkable summary.
This is a paper-backed arithmetic certificate, not a Lean proof or RH proof.
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

I, SCALE, ZERO, ONE = e.I, e.SCALE, e.ZERO, e.ONE
lograt, logiv = e.lograt, e.logiv
END = 121393
GAMMA_M = 10**6


def gamma_interval(m):
    h=I(sum(SCALE//j for j in range(1,m+1)),
        sum(e.ceildiv(SCALE,j) for j in range(1,m+1)))
    base=h-lograt(m)
    return I((base-I.rat(1,2*m)).lo,(base-I.rat(1,2*(m+1))).hi)


def price(x):
    return ONE/(x*logiv(x))


def endpoint_gap(x,energy,benefit,gamma):
    return gamma+logiv(logiv(x))-benefit+price(x)*(energy-x)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    gamma=gamma_interval(GAMMA_M)
    start=lograt(40000); finish=I.rat(END)
    high,low=price(start),price(finish)
    target=I.rat(51,250000)
    assert high.hi<I.rat(1,25).lo
    # For all p >= END+1: r_(p,k) <= r_(p,1) < 1/(p log p) < low.
    assert price(I.rat(END+1)).hi<low.lo
    primes=e.prime_sieve(END+1)
    layers=[]; first_inactive=[]
    for p in primes:
        lp=lograt(p); k=1; power=p; psum=p
        while True:
            gain=lograt(psum+1,psum); rate=gain/lp
            if rate.hi<low.lo:
                first_inactive.append([p,k,rate.wire()]); break
            assert rate.lo>low.hi,('uncertain endpoint',p,k)
            layers.append({'p':p,'k':k,'logp':lp,'gain':gain,'rate':rate})
            k+=1; power*=p; psum+=power
    layers.sort(key=lambda z:z['rate'].lo,reverse=True)
    for left,right in zip(layers,layers[1:]):
        assert left['rate'].lo>right['rate'].hi,('unresolved tie',left['p'],right['p'])
    initial=[]; events=[]
    for layer in layers:
        if layer['rate'].lo>high.hi: initial.append(layer)
        else:
            assert layer['rate'].hi<high.lo
            events.append(layer)
    exp={}
    energy=benefit=ZERO
    for layer in initial:
        assert layer['k']==exp.get(layer['p'],0)+1
        exp[layer['p']]=layer['k']
        energy=energy+layer['logp']; benefit=benefit+layer['gain']
    assert exp=={2:4,3:2,5:1,7:1}
    first_gap=endpoint_gap(start,energy,benefit,gamma)
    assert first_gap.lo>target.hi
    cells=[]; critical=[]; first_integer=None
    for index in range(len(events)+1):
        upper=high if index==0 else events[index-1]['rate']
        lower=low if index==len(events) else events[index]['rate']
        ownprice=price(energy)
        if ownprice.lo>upper.hi: classification='energy_before_cell'
        elif ownprice.hi<lower.lo: classification='energy_after_cell'
        else:
            assert lower.hi<ownprice.lo and ownprice.hi<upper.lo,('uncertain critical classification',index)
            classification='strict_self_matching'
            gap=gamma+logiv(logiv(energy))-benefit
            assert gap.lo>target.hi,('critical gap fails',index)
            point={'index':index,'energy':energy.wire(),'benefit':benefit.wire(),
                   'price':ownprice.wire(),'gap':gap.wire(),
                   'exponents':[[p,a] for p,a in sorted(exp.items())]}
            critical.append(point)
            if first_integer is None:
                first_integer=1
                for p,a in exp.items(): first_integer*=p**a
        cells.append({'index':index,'energy':energy.wire(),'benefit':benefit.wire(),
                      'price':ownprice.wire(),'classification':classification})
        if index<len(events):
            layer=events[index]
            assert layer['k']==exp.get(layer['p'],0)+1
            exp[layer['p']]=layer['k']
            energy=energy+layer['logp']; benefit=benefit+layer['gain']
    last_gap=endpoint_gap(finish,energy,benefit,gamma)
    assert last_gap.lo>target.hi
    # Complete integer patch: each block uses its exact maximum Z and the
    # monotonic Robin budget at its left endpoint. Split only failed blocks.
    sigma=[0]*40001
    for d in range(1,40001):
        for n in range(d,40001,d): sigma[n]+=d
    patch=[]; comparisons=0
    def cover(a,b):
        nonlocal comparisons
        comparisons+=1
        nmax=max(range(a,b+1),key=lambda n:Fraction(sigma[n],n))
        gap=gamma+logiv(logiv(lograt(a)))-lograt(sigma[nmax],nmax)
        if gap.lo>0:
            patch.append({'a':a,'b':b,'maximum_n':nmax,
                          'maximum_z':[sigma[nmax],nmax],'gap':gap.wire()})
        else:
            assert a<b,('Robin patch failed',a)
            mid=(a+b)//2; cover(a,mid); cover(mid+1,b)
    cover(5041,40000)
    minimum=min(critical,key=lambda c:int(c['gap'][0]))
    cert={'schema':'fib-robin-critical-slice-v1','scale':str(SCALE),
          'gamma_m':GAMMA_M,'gamma':gamma.wire(),'start_n':40000,'end_x':END,
          'target':[51,250000],'primes':primes,'first_inactive':first_inactive,
          'initial_count':len(initial),
          'layers':[{'p':a['p'],'k':a['k'],'gain':a['gain'].wire(),
                     'logp':a['logp'].wire(),'rate':a['rate'].wire()} for a in layers],
          'cells':cells,'critical':critical,'endpoints':[
              {'x':start.wire(),'gap':first_gap.wire()},
              {'x':finish.wire(),'gap':last_gap.wire()}],
          'integer_patch':patch}
    raw=json.dumps(cert,separators=(',',':')).encode()
    (args.out/'certificate.json.gz').write_bytes(gzip.compress(raw,mtime=0))
    summary={'status':'all outward integer-interval comparisons passed; not Lean verified',
             'range':['log(40000)',END],'primes':len(primes),'initial_layers':len(initial),
             'activation_events':len(events),'stable_cells':len(cells),
             'critical_configs':len(critical),'critical_at_or_above_144':sum(int(c['energy'][0])>=144*SCALE for c in critical),
             'first_critical_integer':first_integer,
             'first_critical_energy':I(*map(int,critical[0]['energy'])).decimal(),
             'minimum_critical_energy':I(*map(int,minimum['energy'])).decimal(),
             'minimum_critical_gap':I(*map(int,minimum['gap'])).decimal(),
             'start_gap':first_gap.decimal(),'end_gap':last_gap.decimal(),
             'strict_uniform_bound':'51/250000','small_integers':34960,
             'small_patch_blocks':len(patch),'small_patch_bound_evaluations':comparisons,
             'certificate_sha256':hashlib.sha256(raw).hexdigest(),
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'engine_sha256':hashlib.sha256(Path(e.__file__).read_bytes()).hexdigest(),
             'limitations':['Paper proof supplies log-series correctness, gamma enclosure, event completeness criterion, and no-minimum-at-switch theorem.',
                            'No threshold ties occurred in this finite range; paper proof covers simultaneous ties.',
                            'No assertion beyond end_x or of RH is certified.']}
    (args.out/'results.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
