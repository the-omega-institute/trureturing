"""Actual theta scalar assembly pilot; not a complete spectral trial family."""
import json
import math
import time
from pathlib import Path
import flint
from flint import arb, acb, ctx, fmpq

ctx.prec = 128
RUN = Path(__file__).parent
started = time.monotonic()
ELL = arb(2).log()
HALF = arb(fmpq(1, 2))
EPS = arb(fmpq(1, 4))
C = HALF - EPS / 2
P = 6
GRID = 64
counter = {"theta": 0, "gamma_boxes": 0, "certified_prime_branch_reads": 0}


def phi(z, analytic=False):
    """Original positive-side theta series, uniformly enclosed complex tail."""
    z = acb(z)
    a, b = z.real.lower(), z.real.upper()
    v = abs(z.imag).upper()
    if not v < arb.pi() / 4:
        return acb('nan')
    lam = arb.pi() * (2 * a).exp() * (2 * v).cos()
    if not lam > 0:
        return acb('nan')
    us = []
    for r in (4, 2):
        ratio = (1 + arb(1) / (P + 1))**r * (-lam * (2 * P + 3)).exp()
        if not ratio < 1:
            return acb('nan')
        us.append(arb(P + 1)**r * (-lam * (P + 1)**2).exp() / (1 - ratio))
    err = 4 * arb.pi()**2 * (9 * b / 2).exp() * us[0]
    err += 6 * arb.pi() * (5 * b / 2).exp() * us[1]
    total = acb(0)
    u = (2 * z).exp()
    for n in range(1, P + 1):
        total += (4 * arb.pi()**2 * n**4 * (9 * z / 2).exp()
                  - 6 * arb.pi() * n**2 * (5 * z / 2).exp()) * (-arb.pi() * n*n * u).exp()
    counter['theta'] += 1
    return total + acb(arb(0, err.upper()), arb(0, err.upper()))


def realphi(x):
    value = phi(acb(abs(x)))
    if not value.is_finite():
        raise ValueError('Nonfinite real theta enclosure')
    return value.real


def kappa(t):
    t=arb(t)
    # sinh(t)/t is entire, including its value 1 at zero. All omitted
    # positive-series terms are enclosed by a geometric majorant.
    m=20
    bound=abs(t).upper()
    ratio=bound**2/((2*m+2)*(2*m+3))
    if not ratio < 1:
        return arb('nan')
    total=arb(1)
    term=arb(1)
    for k in range(1,m+1):
        term*=(t*t)/((2*k)*(2*k+1))
        total+=term
    err=bound**(2*m+2)/math.factorial(2*m+3)/(1-ratio)
    return (t/2).exp()/(2*(total+arb(0,err.upper())))


def integrate(callback, a, b):
    value = acb.integral(callback, acb(a), acb(b), abs_tol=arb('1e-20'),
                         rel_tol=arb('1e-20'), eval_limit=100000, depth_limit=30)
    if not value.is_finite():
        raise ValueError('Nonfinite retained one-dimensional integral')
    return value.real


def one_dim(power, density=True):
    def callback(x, analytic):
        p = phi(x, analytic)
        factor = 2 * (x/2).cosh() if density else acb(1)
        return 2 * p * factor * (1 / (ELL*x))**power
    return integrate(callback, HALF, arb(1))


def branch(code, x):
    return arb(0) if code == 0 else code / (ELL*x)


def cbranch(code, x):
    return acb(0) if code == 0 else code / (ELL*x)


def gamma_panels():
    bounds = list(map(arb, [-2, -1, '-0.5', '0.5', 1, 2]))
    codes = [0, -1, 0, 1, 0]
    panels = []
    for i in range(5):
        a, b = bounds[i:i+2]
        ca = codes[i]
        if ca:
            def same(u, v, a=a, b=b, ca=ca):
                x = a + (b-a)*u
                y = x + (b-x)*v
                gap = y-x
                qq = -ca/(ELL*x*y)
                return realphi(x)*realphi(y)*gap*kappa(gap)*(qq*qq)*(b-a)*(b-x)
            panels.append(('same_%d' % i, same))
        for j in range(i+1, 5):
            d, e = bounds[j:j+2]
            cb = codes[j]
            if ca == cb == 0:
                continue
            if j == i+1:
                z, aa, bb = b, b-a, e-d
                for side in range(2):
                    def corner(u, v, z=z, aa=aa, bb=bb, ca=ca, cb=cb, side=side):
                        s, t = (aa*u, bb*u*v) if side == 0 else (aa*u*v, bb*u)
                        denom = aa+bb*v if side == 0 else aa*v+bb
                        x, y = z-s, z+t
                        diff = branch(cb, y)-branch(ca, x)
                        return realphi(x)*realphi(y)*aa*bb*kappa(u*denom)/denom*(diff*diff)
                    panels.append(('jump_%d_%d_%d' % (i,j,side), corner))
            else:
                def rectangle(u,v,a=a,b=b,d=d,e=e,ca=ca,cb=cb):
                    x,y = a+(b-a)*u,d+(e-d)*v
                    gap=y-x
                    diff=branch(cb,y)-branch(ca,x)
                    return realphi(x)*realphi(y)*kappa(gap)/gap*(diff*diff)*(b-a)*(e-d)
                panels.append(('gap_%d_%d' % (i,j), rectangle))
    return panels


def box_integral(func, grid):
    total=arb(0)
    for i in range(grid):
        u=arb(fmpq(2*i+1,2*grid),fmpq(1,2*grid))
        for j in range(grid):
            v=arb(fmpq(2*j+1,2*grid),fmpq(1,2*grid))
            value=func(u,v)
            counter['gamma_boxes']+=1
            if counter['gamma_boxes'] > 131072 or not value.is_finite():
                raise ValueError('Box budget or nonfinite transformed Gamma enclosure: u=%s v=%s boxes=%s' % (u,v,counter['gamma_boxes']))
            total+=value/(grid*grid)
    return total


def active_branch(mid):
    if mid > HALF and mid < 1:
        code=1
    elif mid > -1 and mid < -HALF:
        code=-1
    elif mid < -1 or (mid > -HALF and mid < HALF) or mid > 1:
        code=0
    else:
        raise ValueError('Ambiguous active/zero prime branch: %s' % mid)
    counter['certified_prime_branch_reads']+=1
    return code


def prime_term(n,p):
    shift=arb(n).log()
    # Approximate ordering is only a proposal; each strict order is certified below.
    endpoints=[arb(fmpq(k,2))-s for s in (arb(0),shift) for k in (-2,-1,0,1,2)]
    endpoints.sort(key=lambda z:float(z.mid()))
    if any(not endpoints[k+1]-endpoints[k] > 0 for k in range(len(endpoints)-1)):
        raise ValueError('Uncertified prime breakpoint order')
    total=arb(0)
    for a,b in zip(endpoints,endpoints[1:]):
        mid=(a+b)/2
        ca,cb=active_branch(mid),active_branch(mid+shift)
        if ca==cb==0:
            continue
        sa=1 if mid > 0 else -1
        sb=1 if mid+shift > 0 else -1
        def callback(x,analytic,ca=ca,cb=cb,sa=sa,sb=sb):
            y=x+shift
            return phi(sa*x,analytic)*phi(sb*y,analytic)*(cbranch(cb,y)-cbranch(ca,x))**2
        total+=integrate(callback,a,b)
    return arb(p).log()/arb(n).sqrt()*total


def export(x):
    return {'ball':str(x),'lower':str(x.lower()),'upper':str(x.upper()),
            'lower_dyadic':[str(m) for m in x.lower().man_exp()],
            'upper_dyadic':[str(m) for m in x.upper().man_exp()]}


mass=one_dim(2)
mean=one_dim(1)
h1=one_dim(2,False)
print(json.dumps({'stage':'mass_mean','G':export(mass),'mu':export(mean)},ensure_ascii=False),flush=True)
prime=arb(0)
prime_rows=[]
for n,p in [(2,2),(3,3),(4,2),(5,5),(7,7),(8,2)]:
    val=prime_term(n,p)
    prime+=val
    prime_rows.append({'n':n,'base_prime':p,'energy':export(val)})
print(json.dumps({'stage':'complete_prime_prefix','energy':export(prime)},ensure_ascii=False),flush=True)
gamma=arb(0)
gamma_rows=[]
for name,func in gamma_panels():
    val=box_integral(func,GRID)
    gamma+=val
    gamma_rows.append({'panel':name,'energy':export(val),'boxes':GRID**2})
    print(json.dumps({'stage':'gamma_panel','panel':name,'energy':export(val)},ensure_ascii=False),flush=True)
r=fmpq(round(float(mean.mid())*2**20),2**20)
cr=mass-2*mean*arb(r)+arb(r)**2
lower=gamma+prime-C*cr
gamma_tail=kappa(1)*arb(fmpq(96,5))*arb(-4).exp()*(-arb(fmpq(3,2))*arb(4).exp()).exp()*h1
beta=arb(fmpq(3,2))*arb(-2).exp()
# x in [-1,1]: both beta_+ and beta_- are at least beta.
assert arb(9).log() > 2, 'Disjoint omitted supports must be certified'
prime_tail=arb(fmpq(144,5))/8*(-beta*64).exp()/beta*h1
mean_error=abs(mean-arb(r)).upper()
mean_loss_upper=C*mean_error*mean_error
full_upper=(lower+gamma_tail+prime_tail+mean_loss_upper).upper()
result={'scope':'Scalar assembly pilot only; not the complete EA trial family, RH, Robin or Lean',
        'runtime':{'python_flint':flint.__version__,'flint_version':getattr(flint,'__FLINT_VERSION__','not exposed'),'bits':ctx.prec},
        'parameters':{'delta':'1/2','center':'0','epsilon':'1/4','H':2,'N':8,'theta_terms':P,'gamma_grid':GRID},
        'G':export(mass),'mu':export(mean),'r':str(r),'C_r':export(cr),
        'prime_terms':prime_rows,'D_p_prefix':export(prime),'gamma_panels':gamma_rows,'D_gamma_square':export(gamma),
        'F_r':export(lower),'strict_lower_positive':bool(lower > 0),
        'omitted_gamma_upper':export(gamma_tail),'omitted_prime_upper':export(prime_tail),
        'mean_loss_upper':export(mean_loss_upper),'full_target_upper':export(full_upper),
        'counters':counter,'elapsed_seconds':time.monotonic()-started}
(RUN/'scalar-result.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'stage':'complete','F_r':export(lower),'strict_lower_positive':bool(lower>0),'counters':counter,'seconds':time.monotonic()-started}),flush=True)
