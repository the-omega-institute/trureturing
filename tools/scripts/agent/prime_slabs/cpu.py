"""Exact inputs for the bounded, foreground actual-prime dual/Hermite inquiry.

This module does not import the fixed-through-19 decoder or any GPU module.
All coordinate-indexed data are constructed after sorting paired (prime,b).
The pure three-row Arb expression in certify.py is the discovery evaluator.
"""
from fractions import Fraction as F
import hashlib
import itertools
import json
import math

DEFINITION = 'actual-prime-closed-slab-dual-minus-hermite-sum-variance-v1'
PRECISIONS = (128, 256, 512)
PILOT_CAP_NS = 600_000_000_000
EXPERIMENT = dict(
    schema='actual-prime-cpu-v1', definition=DEFINITION,
    q=[23,29,31], exponents=list(range(16)), pilot_exponents=[0,5,10,15],
    precisions=list(PRECISIONS), pilot_evaluation_cap_ns=PILOT_CAP_NS,
    mathematical_domain=dict(k=3, cutoff='exp(T0)>5040', slab='closed',
        configurations='two distinct actual exponent vectors in {b_i,b_i+1}',
        shift='M_j=T_j+sum(log(p_i))', endpoints='c_i=(b_i+1)log(p_i); d_i=(b_i+2)log(p_i)',
        f='log(1-exp(-x)), x>0', mu='M1/3',
        variance='V0=sum_i dist([M0/3,M1/3],{c_i,d_i})^2',
        support='mu>0; 0<=V0<6*mu^2; L>0',
        rho='sqrt(V0/6)', L='mu-rho', H='mu+2*rho',
        dual='inf_(lambda>=0) lambda*M1+sum_i max(f(c_i)-lambda*c_i,f(d_i)-lambda*d_i)',
        primal='max sum_i ((1-y_i)*f(c_i)+y_i*f(d_i)); 0<=y_i<=1; sum_i log(p_i)*y_i<=M1-sum_i c_i',
        gap='G=D-(f(H)+2*f(L))', common_constant='log E; E=prod_i (1-1/p_i)^(-1)',
        boundary='Finite nodes only; neither C nor Not C follows from a search dataset.'))


def dumps(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)


def digest(value):
    return hashlib.sha256(dumps(value).encode()).hexdigest()


def coordinates(pairs):
    pairs = tuple(tuple(x) for x in pairs)
    if (len(pairs)!=3 or any(len(x)!=2 for x in pairs) or
        any(type(p) is not int or type(b) is not int or p<2 or b<0
            for p,b in pairs) or len({p for p,_ in pairs})!=3):
        raise ValueError('three distinct actual primes and nonnegative integer exponents required')
    if any(any(p%d==0 for d in range(2,math.isqrt(p)+1)) for p,_ in pairs):
        raise ValueError('composite prime label')
    return tuple(sorted(pairs))


def rational(q):
    if type(q) not in (int,str,F):
        raise ValueError('budget must be an exact integer, rational string or Fraction')
    q=F(q)
    if q<=0: raise ValueError('budget exponential must be positive')
    return str(q)


def canonical_input(pairs,q0,q1):
    return dict(definition=DEFINITION,coordinates=[list(x) for x in coordinates(pairs)],
                exp_M0=rational(q0),exp_M1=rational(q1))


def canonical_key(pairs,q0,q1):
    # Source/program/run hashes are provenance and deliberately absent here.
    return digest(canonical_input(pairs,q0,q1))


def guard_bits(R,cube=None,X=None,E=None,middle=None,upper=None):
    if cube is None: return int(R>5040)
    return sum(int(flag)<<i for i,flag in enumerate(
        (R>5040,cube<X,X*X<E,middle<E,E<upper)))


def make_box(pairs):
    pairs=coordinates(pairs)
    p,b=zip(*pairs); P=math.prod(p)
    C=[pi**(bi+1) for pi,bi in pairs]; D=[pi**(bi+2) for pi,bi in pairs]
    corners=[]
    for mask in range(8):
        a=[b[i]+((mask>>i)&1) for i in range(3)]
        corners.append(dict(mask=mask,exponents=a,product=math.prod(p[i]**a[i] for i in range(3))))
    corners.sort(key=lambda c:c['product'])
    if len({c['product'] for c in corners})!=8: raise ValueError('non-distinct actual corners')
    raw,nodes=[],[]
    for slot in range(25):
        j,i=(slot+1,None) if slot<7 else (1+(slot-7)//3,(slot-7)%3)
        lower,upper=corners[j-1],corners[j]
        R,Ru=lower['product'],upper['product'];X=P*R
        origin=dict(slot=slot,kind='adjacent' if i is None else 'reflection',j=j,i=i)
        guards=dict(R_lower=R,cutoff=5040)
        if i is None:
            bits=guard_bits(R);active=bits==1;q1=F(P*Ru)
        else:
            E=p[i]**(3*(2*b[i]+3)); cube=C[i]**3
            middle=P*P*R*Ru; following=P*P*R*corners[j+1]['product']
            bits=guard_bits(R,cube,X,E,middle,following);active=bits==31;q1=F(E,X)
            guards.update(cube=cube,X=X,X_squared=X*X,E=E,middle=middle,upper=following)
        entry=dict(origin,guard_bits=bits,active=active,key=None)
        if active:
            inp=canonical_input(pairs,X,q1)
            exact=dict(C=C,D=D,exp_T0=str(R),exp_T1=str(q1/P),
                       two_configurations=[lower['exponents'],upper['exponents']],guards=guards)
            node=dict(key=digest(inp),input=inp,exact=exact,origin=origin)
            validate_node(node)
            nodes.append(node);entry['key']=node['key']
        raw.append(entry)
    return dict(coordinates=[list(x) for x in pairs],corners=corners,slots=raw,nodes=nodes)


def validate_node(node):
    """Check actual input identity and domain witnesses before every new key."""
    inp=node['input'];exact=node['exact'];pairs=coordinates(inp['coordinates'])
    q0,q1=F(inp['exp_M0']),F(inp['exp_M1']);P=math.prod(p for p,_ in pairs)
    if inp!=canonical_input(pairs,q0,q1) or node['key']!=digest(inp):
        raise ValueError('canonical input/key/definition mismatch')
    if not 5040<q0/P<q1/P: raise ValueError('strict5040/budget order')
    if exact['C']!=[p**(b+1) for p,b in pairs] or exact['D']!=[p**(b+2) for p,b in pairs]:
        raise ValueError('actual prime/exponent endpoint identity')
    if F(exact['exp_T0'])!=q0/P or F(exact['exp_T1'])!=q1/P:
        raise ValueError('M=T+sum(log p) budget shift')
    aa=exact['two_configurations']
    if len(aa)!=2 or aa[0]==aa[1]: raise ValueError('two distinct configurations required')
    for a in aa:
        if len(a)!=3 or any(type(e) is not int or e not in (b,b+1) for e,(_,b) in zip(a,pairs)):
            raise ValueError('actual configuration exponent')
        n=math.prod(p**e for e,(p,_) in zip(a,pairs))
        if not q0/P<=n<=q1/P: raise ValueError('closed slab configuration membership')
    # This actual positive corner implies the source domain V0<6*mu^2 and L>0.
    if q1<math.prod(exact['C']): raise ValueError('infeasible fractional budget')
    origin=node['origin'];j,i=origin['j'],origin['i']
    if type(j) is not int or not 1<=j<=7: raise ValueError('node index')
    corners=sorted(math.prod(p**(b+e) for (p,b),e in zip(pairs,mask))
                   for mask in itertools.product((0,1),repeat=3))
    R,Ru=corners[j-1:j+1];X=P*R
    guards=dict(R_lower=R,cutoff=5040)
    if i is None:
        valid=(origin==dict(slot=j-1,kind='adjacent',j=j,i=None) and
               guard_bits(R)==1 and q0==X and q1==P*Ru)
    else:
        if type(i) is not int or not 0<=i<3 or j>6: raise ValueError('reflection index')
        p,b=pairs[i];E=p**(3*(2*b+3));cube=p**(3*(b+1))
        middle=P*P*R*Ru;upper=P*P*R*corners[j+1]
        guards.update(cube=cube,X=X,X_squared=X*X,E=E,middle=middle,upper=upper)
        valid=(origin==dict(slot=7+3*(j-1)+i,kind='reflection',j=j,i=i) and
               guard_bits(R,cube,X,E,middle,upper)==31 and q0==X and q1==F(E,X))
    if not valid or exact['guards']!=guards: raise ValueError('exact node guards/origin')


def boxes(phase):
    if phase not in ('pilot','window'): raise ValueError('unknown experiment phase')
    for q in ([23] if phase=='pilot' else EXPERIMENT['q']):
        for b in itertools.product(EXPERIMENT['pilot_exponents'] if phase=='pilot'
                                   else EXPERIMENT['exponents'],repeat=3):
            yield ((2,b[0]),(3,b[1]),(q,b[2]))


def pilot_box(pairs):
    pairs=coordinates(pairs)
    return tuple(p for p,_ in pairs)==(2,3,23) and all(b in (0,5,10,15) for _,b in pairs)


def matching_supports(pairs,records):
    support=tuple(p for p,_ in coordinates(pairs))
    return [r for r in records if tuple(sorted(r['primes']))==support]


def evaluate_tier(node,precision):
    """One uncompleted precision only; never calls certify_row's restart ladder."""
    from flint import arb,ctx
    from . import certify
    if precision not in PRECISIONS: raise ValueError('precision outside registered ladder')
    inp,exact=node['input'],node['exact']
    with ctx.workprec(precision):
        try:
            values=certify.evaluate(exact['C'],exact['D'],F(inp['exp_M0']),F(inp['exp_M1']))
        except ArithmeticError as e:
            return dict(precision=precision,outcome='unresolved',error=str(e),bounds={})
        mu=values['M1']/3
        domain=bool(mu>0 and values['L']>0 and 6*mu*mu-values['V0']>0)
        result=dict(precision=precision,
            outcome=certify.sign(values['G']) if domain else 'unresolved',
            bounds={k:certify.enclosure(v) for k,v in values.items() if isinstance(v,arb)},
            domain_enclosed=domain,nearest_ties=values['nearest_ties'],
            distance_ratios=values['distance_ratios'],
            mixtures=[certify.enclosure(x) for x in values['mixtures']],
            weights=[[certify.enclosure(x) for x in y] for y in values['weights']])
        result['bounds']['scaled_G']=certify.enclosure(min(exact['C'])*values['G'])
        # Exact clipping decisions retain all six orders in their actual interface order.
        result['clipping']=[]
        for order in itertools.permutations(range(3)):
            budget=F(inp['exp_M1'])/math.prod(exact['C']); branches=[None]*3
            for i in order:
                step=F(exact['D'][i],exact['C'][i])
                branches[i]=dict(budget=str(budget),step=str(step),
                    branch='zero' if budget<=1 else 'one' if budget>=step else 'fractional')
                budget/=step
            result['clipping'].append(branches)
        return result
