"""Directed original-theta derivative norms and direct bandwidth conditions."""
from pathlib import Path
import json
import hashlib
import sys
import flint
from flint import arb, fmpq, ctx

ctx.prec = 128
run = Path(__file__).parent
TERMS = 6
GRID = 1536
R = 3
N = 64
pi = arb.pi()
c = arb(fmpq(3, 8))


def polys(a, order):
    p = [fmpq(1)]
    for _ in range(order):
        q = [fmpq(0)]*(len(p)+1)
        for k, value in enumerate(p):
            q[k] += (a+2*k)*value
            q[k+1] -= 2*value
        p = q
    return p


coeff = {(j, a): polys(a, j) for j in range(4)
         for a in (fmpq(9, 2), fmpq(5, 2))}
rstar = arb(fmpq(3, 2))**10*(-5*pi).exp()
if not rstar < 1:
    raise RuntimeError('Uncertified geometric tail ratio')


def scalar_constant(j, tail_only=False):
    total = arb(0)
    for a, pref, degree in ((fmpq(9, 2),4*pi*pi,4),
                           (fmpq(5, 2),6*pi,2)):
        for k, p in enumerate(coeff[j, a]):
            power = degree+2*k
            series = arb(0)
            if not tail_only:
                for n in range(1, TERMS+1):
                    series += n**power*(-pi*(n*n-1)).exp()
            n = TERMS+1
            series += n**power*(-pi*(n*n-1)).exp()/(1-rstar)
            total += pref*arb(abs(p))*pi**k*series
    return total.upper()


C = [scalar_constant(j) for j in range(4)]
CT = [scalar_constant(j, True) for j in range(4)]
gamma = [v/18 for v in C]
A1 = gamma[1]/2+arb(fmpq(1, 4))
A2 = (gamma[2]+gamma[1]**2)/2+arb(fmpq(1, 8))
A3 = (gamma[3]+3*gamma[1]*gamma[2]+2*gamma[1]**3)/2+arb(fmpq(1, 8))
B = [arb(1),A1,A1*A1+A2,A1**3+3*A1*A2+A3]
zeta = pi/2-c
K = []
for j in range(4):
    m = 1+2*j
    # A slightly larger scalar maximum: valid also when m/zeta<1.
    # max_{u>=1} u^m exp(-zeta*u) <= (m/zeta)^m exp(-m).
    maximum = (m/zeta)**m*arb(-m).exp()
    K.append((C[0].sqrt()*B[j]*maximum).upper())


def phi_derivatives(x):
    u = (2*x).exp()
    vals = []
    for j in range(4):
        total = arb(0)
        for n in range(1,TERMS+1):
            z = pi*n*n*u
            polyvals = []
            for a in (fmpq(9, 2),fmpq(5, 2)):
                pv = arb(0)
                for pk in reversed(coeff[j,a]):
                    pv = pv*z+arb(pk)
                polyvals.append(pv)
            total += (4*pi*pi*n**4*(arb(fmpq(9, 2))*x).exp()*polyvals[0]
                      -6*pi*n**2*(arb(fmpq(5, 2))*x).exp()*polyvals[1])*(-z).exp()
        tail = (CT[j]*(arb(fmpq(9, 2)+2*j)*x).exp()*(-pi*u).exp()).upper()
        vals.append(total+arb(0,tail))
    if not vals[0].is_finite() or not vals[0].lower()>0:
        raise RuntimeError('Uncertified actual original-theta denominator')
    return vals


bounds = [arb(0) for _ in range(4)]
for i in range(GRID):
    left,right = fmpq(R*i,GRID),fmpq(R*(i+1),GRID)
    x = arb((left+right)/2,arb((right-left)/2).upper())
    p0,p1,p2,p3 = phi_derivatives(x)
    t = (x/2).tanh()
    sech2 = 1/(x/2).cosh()**2
    r1,r2,r3 = p1/p0,p2/p0,p3/p0
    l1 = (r1-t/2)/2
    l2 = (r2-r1*r1-sech2/4)/2
    l3 = (r3-3*r1*r2+2*r1**3+sech2*t/4)/2
    s = (p0/(2*(x/2).cosh())).sqrt()
    values = [s,s*l1,s*(l1*l1+l2),s*(l1**3+3*l1*l2+l3)]
    for j,value in enumerate(values):
        if not value.is_finite():
            raise RuntimeError('Nonfinite derivative enclosure')
        bounds[j] += arb(2*(right-left))*abs(value).upper()**2
    if i%256 == 0:
        print(json.dumps({'box':i,'s_second_integral_upper':str(bounds[2].upper())}),flush=True)

uR = arb(2*R).exp()
tails = [(k*k*(-2*c*uR).exp()/(2*c*uR)).upper() for k in K]
norms = [(b.upper()+t).upper() for b,t in zip(bounds,tails)]
xi = arb(fmpq(N,2))
SYMBOL_TERMS = 1024
symbol = arb(0)
for k in range(SYMBOL_TERMS):
    ak = arb(fmpq(4*k+1,2))
    symbol += 2*xi**2/(ak*(ak**2+xi**2))
last = arb(fmpq(4*(SYMBOL_TERMS-1)+1,2))
symbol_upper = (symbol+xi**2/(2*last**2)).upper()
symbol_lower = symbol.lower()
mu_source = run/'deficit-result.json'
mu_bytes = mu_source.read_bytes()
mu = json.loads(mu_bytes)
man,exponent = map(int,mu['mu_upper']['dyadic'])
mu_upper = arb(man)*arb(2)**exponent
leakage_upper = (symbol_upper*arb(8)/(3*pi)*arb(N)**(-3)*norms[2]).upper()
passed_symbol = bool(symbol_lower>=mu_upper)
passed_leakage = bool(leakage_upper<=arb(fmpq(1,16)))


def endpoint(value):
    return {'display':str(value),'dyadic':[str(v) for v in value.man_exp()]}


result = {
 'scope':'Directed derivative norms and direct high-frequency conditions; no complete matrix or RH certificate; no new Lean certification',
 'runtime':{'python':sys.version.split()[0],'python_flint':flint.__version__,'precision_bits':ctx.prec},
 'mu_source':mu_source.name,'mu_source_sha256':hashlib.sha256(mu_bytes).hexdigest(),
 'original_theta_terms':TERMS,'radius':R,'grid_boxes':GRID,'epsilon':'1/4','bandwidth_N':N,
 'derivative_norm_squared_upper':[endpoint(v) for v in norms],
 'derivative_exterior_upper':[endpoint(v) for v in tails],
 'symbol_terms':SYMBOL_TERMS,'m_N_over_2_lower':endpoint(symbol_lower),'m_N_over_2_upper':endpoint(symbol_upper),
 'mu_upper_reused':endpoint(mu_upper.upper()),'leakage_product_upper':endpoint(leakage_upper),
 'passed_symbol':passed_symbol,'passed_leakage':passed_leakage,
}
(run/'derivative-bandwidth-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
if not passed_symbol or not passed_leakage:
    raise RuntimeError('Declared direct bandwidth certificate not obtained')
