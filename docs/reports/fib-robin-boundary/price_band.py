#!/usr/bin/env python3
"""Independent integer-interval audit of the finite Robin price band.

Every proof comparison uses integer endpoints with denominator 2**128.
Logs use power-of-two reduction and the atanh series with an explicit tail.
No external packages, floating-point comparisons, or assumed RH are used.
This is an executable arithmetic certificate, not a Lean theorem.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from decimal import Decimal, localcontext

BITS = 128
SCALE = 1 << BITS
TERMS = 100

def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi
    @staticmethod
    def rat(a, b=1):
        assert b > 0
        return I(a * SCALE // b, ceildiv(a * SCALE, b))
    def __add__(self, o):
        if isinstance(o, int): o = I.rat(o)
        return I(self.lo + o.lo, self.hi + o.hi)
    def __sub__(self, o):
        if isinstance(o, int): o = I.rat(o)
        return I(self.lo - o.hi, self.hi - o.lo)
    def __mul__(self, o):
        if isinstance(o, int): o = I.rat(o)
        v = [self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi]
        return I(min(v)//SCALE, ceildiv(max(v), SCALE))
    def __truediv__(self, o):
        if isinstance(o, int): o = I.rat(o)
        assert o.lo > 0
        return self * I(SCALE*SCALE//o.hi, ceildiv(SCALE*SCALE, o.lo))
    def wire(self): return [str(self.lo), str(self.hi)]
    def decimal(self):
        with localcontext() as c:
            c.prec = 28
            return [str(Decimal(v)/SCALE) for v in (self.lo, self.hi)]

ZERO = I.rat(0)
ONE = I.rat(1)

def reduced_log(a, b):
    assert b <= a <= 2*b
    z = I.rat(a-b, a+b)
    z2 = z*z
    term, total = z, ZERO
    for j in range(TERMS):
        total = total + term/(2*j+1)
        term = term*z2
    tail = (term*2)/((ONE-z2)*(2*TERMS+1))
    return total*2 + I(0, tail.hi)

LOG2 = reduced_log(2, 1)

def lograt(a, b=1):
    assert a > 0 and b > 0
    e = a.bit_length()-b.bit_length()
    if e >= 0:
        den, num = b << e, a
    else:
        den, num = b, a << -e
    if num < den:
        num *= 2
        e -= 1
    if num >= 2*den:
        den *= 2
        e += 1
    assert den <= num < 2*den
    return reduced_log(num, den) + LOG2*e

def logiv(x):
    assert x.lo > 0
    return I(lograt(x.lo, SCALE).lo, lograt(x.hi, SCALE).hi)

def prime_sieve(limit):
    flags = bytearray(b'\x01')*limit
    flags[:2] = b'\x00\x00'
    p = 2
    while p*p < limit:
        if flags[p]:
            flags[p*p:limit:p] = b'\x00' * ((limit-1-p*p)//p+1)
        p += 1
    return [p for p in range(2,limit) if flags[p]]

def gamma_interval(m):
    # H_m - log m - 1/m < gamma < H_m - log m.
    lo = hi = 0
    for j in range(1,m+1):
        lo += SCALE//j
        hi += ceildiv(SCALE,j)
    h = I(lo,hi)
    base = h-lograt(m)
    return I((base-I.rat(1,m)).lo, base.hi)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    low, high = I.rat(1,10**6), I.rat(1,25)
    target = I.rat(123,500000)
    gamma = gamma_interval(10**6)
    cutoff=100000
    assert (ONE/(lograt(cutoff)*cutoff)).hi < low.lo
    primes=prime_sieve(cutoff)
    layers=[]; inactive_witnesses=[]
    for p in primes:
        lp=lograt(p)
        k, power, psum = 1,p,p
        while True:
            gain=lograt(psum+1,psum)
            rate=gain/lp
            if rate.hi < low.lo:
                inactive_witnesses.append([p,k,rate.wire()]); break
            assert rate.lo > low.hi, ('uncertain cutoff',p,k)
            layers.append(dict(p=p,k=k,logp=lp,gain=gain,rate=rate))
            k+=1; power*=p; psum+=power
    layers.sort(key=lambda x: x['rate'].lo, reverse=True)
    for a,b in zip(layers,layers[1:]):
        assert a['rate'].lo > b['rate'].hi, ('overlapping thresholds',a['p'],a['k'],b['p'],b['k'])
    initial=[a for a in layers if a['rate'].lo > high.hi]
    switches=[a for a in layers if a['rate'].hi < high.lo]
    assert len(initial)+len(switches)==len(layers)
    exponents={}
    for a in initial: exponents[a['p']]=a['k']
    assert exponents=={2:4,3:2,5:1,7:1}
    energy, benefit=ZERO,ZERO
    for a in initial:
        energy=energy+a['logp']; benefit=benefit+a['gain']
    assert not (energy.hi < lograt(5040).lo or lograt(5040).hi < energy.lo)
    # For the initial 5040 cell evaluate K at L=log(8000).
    witness=lograt(8000)
    assert witness.lo > energy.hi
    first_gap = gamma+logiv(logiv(witness))-benefit-high*(witness-energy)
    assert first_gap.lo > target.hi
    cells=[dict(index=0,upper=high.wire(),lower=switches[0]['rate'].wire(),energy=energy.wire(),benefit=benefit.wire(),gap=first_gap.wire(),witness='log(8000)')]
    mingap=None
    for idx,a in enumerate(switches,1):
        assert a['k']==exponents.get(a['p'],0)+1
        exponents[a['p']]=a['k']
        energy=energy+a['logp']; benefit=benefit+a['gain']
        gap=gamma+logiv(logiv(energy))-benefit
        assert gap.lo > target.hi, ('failed cell',idx,gap.decimal())
        if mingap is None or gap.lo < mingap[0]: mingap=(gap.lo,idx,gap)
        nxt=switches[idx]['rate'] if idx < len(switches) else low
        cells.append(dict(index=idx,activated=[a['p'],a['k']],upper=a['rate'].wire(),lower=nxt.wire(),energy=energy.wire(),benefit=benefit.wire(),gap=gap.wire(),witness='own energy'))
    # Exact integer divisor sums plus intervals certify the finite starting patch.
    sigma=[0]*8000
    for d in range(1,8000):
        for n in range(d,8000,d): sigma[n]+=d
    small_min=None
    for n in range(5041,8000):
        gap=gamma+logiv(logiv(lograt(n)))-lograt(sigma[n],n)
        assert gap.lo > 0, ('small n fails',n,gap.decimal())
        if small_min is None or gap.lo < small_min[0]: small_min=(gap.lo,n,gap)
    # The support line covers 8000..40000; these checks are for the integer transfer.
    support=[]
    for n in [8000,40000]:
        en=lograt(n)
        h=gamma+logiv(logiv(en))-lograt(403,105)-high*(en-lograt(5040))
        assert h.lo > 0
        support.append([n,h.wire()])
    e40000=lograt(40000)
    assert (e40000*logiv(e40000)).lo > I.rat(25).hi
    eupper=lograt(10)*30000
    assert (eupper*logiv(eupper)).hi < I.rat(10**6).lo
    # A-rho counterexample: monotonic z log z brackets rho at low price.
    assert (lograt(87847)*87847).hi < I.rat(10**6).lo
    assert (lograt(87848)*87848).lo > I.rat(10**6).hi
    assert energy.lo > I.rat(87848).hi
    certificate={'schema':'fib-robin-peeling-integer-interval-v1','scale':str(SCALE),'atanh_terms':TERMS,'gamma':gamma.wire(),'price_band':[low.wire(),high.wire()],'bound':target.wire(),'prime_cutoff':cutoff,'primes':primes,'inactive_witnesses':inactive_witnesses,'layers':[dict(p=a['p'],k=a['k'],logp=a['logp'].wire(),gain=a['gain'].wire(),rate=a['rate'].wire()) for a in layers],'cells':cells,'support_patch':support}
    cert_bytes=json.dumps(certificate,separators=(',',':')).encode()
    cert_path=args.out/'cells.json.gz'
    cert_path.write_bytes(gzip.compress(cert_bytes,mtime=0))
    result={'status':'all integer-interval comparisons passed; not Lean verified','prime_count':len(primes),'active_layers_at_low':len(layers),'active_prime_directions_at_low':len(exponents),'switches':len(switches),'cells':len(cells),'gamma_interval':gamma.decimal(),'initial_gap':first_gap.decimal(),'minimum_noninitial_gap':mingap[2].decimal(),'minimum_cell':mingap[1],'energy_at_low':energy.decimal(),'rho_at_low_bracket':[87847,87848],'finite_starting_integers':7999-5041+1,'small_minimum_n':small_min[1],'small_minimum_gap':small_min[2].decimal(),'target_margin':'123/500000','integer_transfer_upper':'10^30000','integer_transfer_energy_budget':(eupper*logiv(eupper)).decimal(),'certificate_sha256':hashlib.sha256(cert_bytes).hexdigest(),'script_path':Path(__file__).name,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scale':str(SCALE),'minimum_noninitial_gap_wire':mingap[2].wire(),'limitations':['Analytic correctness of log series, gamma bounds, optimum characterization and transfer is part of the paper argument, not machine proved here.','This executable does not establish any bound below price 1e-6 or RH.']}
    (args.out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
