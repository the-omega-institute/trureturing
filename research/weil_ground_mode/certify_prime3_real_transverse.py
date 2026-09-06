"""Real-structure, full-box Fourier transport for the existing prime-three candidate.

Uses only the CANDIDATE literal and four exact energy fields from previously
published repository sources. These semantic projections are hashed, not
misrepresented as complete upstream-file hashes. The upstream spectral verifier
is not run. No eigensolver, zero-position list, or numerical quadrature is used.

Pointwise tests solve the rank-two REAL least-energy cancellation problem.
The uniform certificate covers entire rational boxes, including y=0 through
the even entire sinhc series. It certifies Im(F(k+w)(x+iy))/y > 1/200 for all
real even L2 errors of norm <=1/100, x in [14,57/4], 0<abs(y)<=1/2, subject to
the explicitly stated analytic Fourier/domain identification.

This is an interval computation, not a Lean kernel replay. The exact real
Hilbert theorems and their integral-kernel adapter are paired Lean/Scribe sources.
"""
from __future__ import annotations
import argparse
import ast
from fractions import Fraction
import hashlib
import json
from math import factorial
from pathlib import Path
from typing import Any
import mpmath
from mpmath import iv

CANDIDATE_HASH = '0a56b05b79c741e7a5548a23dd2eb980b619e260dc10db23bdcfa44c38a467b1'
EXPECTED_E = Fraction(44669457, 489267186193)
ENERGY_KEYS = ('ground_lower','candidate_upper','orthogonal_threshold','projective_distance_sq_upper')
POINTS = (('14','1/4'), ('14','1/100'), ('113/8','1/4'), ('20','1/4'))


def require(value: Any, text: str) -> None:
    if not bool(value):
        raise ArithmeticError(text)


def canonical_hash(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',',':')).encode()).hexdigest()


def Q(value: Any) -> Any:
    q = Fraction(value)
    return iv.mpf(q.numerator) / q.denominator


def abs2(z: Any) -> Any:
    return z.real**2 + z.imag**2


def sinh(z: Any) -> Any:
    return (iv.exp(z)-iv.exp(-z))/2


def cosh(z: Any) -> Any:
    return (iv.exp(z)+iv.exp(-z))/2


def endpoint_integer(v: Any, upper: bool, places: int=18) -> int:
    """Outward decimal integer from the exact mpmath binary endpoint."""
    sign,mantissa,exponent,bits=v._mpi_[1 if upper else 0]
    require(bits>=0, 'Non-finite endpoint')
    exact=Fraction(-mantissa if sign else mantissa)
    exact=exact*(2**exponent) if exponent>=0 else exact/Fraction(2**(-exponent))
    exact*=10**places
    return -((-exact.numerator)//exact.denominator) if upper else exact.numerator//exact.denominator


def interval_record(v: Any) -> dict[str,str]:
    return {'lower':str(Fraction(endpoint_integer(v,False),10**18)),
            'upper':str(Fraction(endpoint_integer(v,True),10**18))}


def interval_box(left: Fraction, right: Fraction) -> Any:
    require(left <= right, 'Reversed rational box')
    return iv.mpf([Q(left).a, Q(right).b])


def literal_and_energy(source: Path, energy: Path) -> tuple[tuple[int,...], Fraction, dict]:
    assignments=[]
    for node in ast.parse(source.read_text(encoding='utf-8')).body:
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CANDIDATE' for t in node.targets):
            assignments.append(ast.literal_eval(node.value))
    require(len(assignments)==1, 'Expected exactly one literal CANDIDATE')
    p=tuple(assignments[0])
    require(len(p)==129 and all(type(x) is int for x in p), 'Invalid candidate coordinates')
    require(p==p[::-1], 'Candidate reflection symmetry failed')
    require(canonical_hash(p)==CANDIDATE_HASH, 'Changed mathematical candidate')
    raw=json.loads(energy.read_text(encoding='utf-8'))
    selected={key:str(Fraction(raw[key])) for key in ENERGY_KEYS}
    lo,up,gap=(Fraction(selected[key]) for key in ENERGY_KEYS[:3])
    require(lo<up<gap, 'Energy order failed')
    e=(up-lo)/(gap-lo)
    require(e==Fraction(selected['projective_distance_sq_upper'])==EXPECTED_E, 'Energy ratio mismatch')
    require(e<Fraction(1,10000), 'Real error radius is not below 1/100')
    return p,e,{'candidate_literal_sha256':canonical_hash(p),
                'energy_projection_sha256':canonical_hash(selected),
                'selected_energy_fields':selected,
                'scope':'Semantic projections only. Complete upstream files and spectral inequalities are not verified here.'}


def sinhc_enclosure(u: Any) -> Any:
    """Enclose sinh(u)/u with value 1 at zero, for the whole real interval u.

    Positive even series through u^22/23!; tail starts at u^24/25!.
    Every successive tail ratio is at most (1/3)^2/(26*27).
    The formula is valid across zero and for negative u as well.
    """
    require(abs(u)<=Q(Fraction(1,3)), 'sinhc input outside certified series range')
    poly=sum((u**(2*j)/factorial(2*j+1) for j in range(12)),iv.mpf(0))
    tail=Q(Fraction(1,3))**24/factorial(25)/(1-Q(Fraction(1,3))**2/(26*27))
    return poly+iv.mpf([0,tail.b])


def point_costs(k: list[Any], length: Any, e: Fraction, xr: str, yi: str) -> dict:
    x,y=Q(xr),Q(yi);z=iv.mpc(x,y);a=length/2
    coefficients=[]
    for n in range(-64,65):
        den=z-2*iv.pi*n/length
        require(abs2(den)>0, 'Point on unresolved sinc pole')
        coefficients.append(k[n+64]/den)
    f=2*iv.sin(a*z)/iv.sqrt(length)*sum(coefficients,iv.mpc(0))
    # Exact real/imaginary Gram integrals on the full interval, no truncation.
    total=sinh(length*y)/(2*y)+iv.sin(length*x)/(2*x)
    square=a+iv.sin(length*z)/(2*z)
    U=(total+square.real)/2-f.real**2
    V=(total-square.real)/2-f.imag**2
    C=square.imag/2-f.real*f.imag
    det=U*V-C**2
    require(U>0 and V>0 and det>0, 'Rank-two real Gram certificate failed')
    cost=(V*f.real**2-2*C*f.real*f.imag+U*f.imag**2)/det
    complex_cost=abs2(f)/(total-abs2(f))
    require(total-abs2(f)>0, 'Complex residual kernel energy failed')
    if (xr,yi)==('14','1/4'):
        require(cost>25*Q(e), 'Real-versus-complex separation missed')
        require(complex_cost<Q(e), 'Complex-ball comparison missed')
    if (xr,yi)==('20','1/4'):
        require(cost<Q(e), 'Required limitation example missing')
    if bool(cost>Q(e)): status='zero excluded for every allowed real error'
    elif bool(cost<Q(e)): status='zero is attainable in the real error ball; no eigenmode conclusion'
    else: status='undetermined'
    return {'z':[xr,yi], 'real_minimum_error_energy':interval_record(cost),
            'real_cost_over_error_budget':interval_record(cost/Q(e)),
            'complex_minimum_error_energy':interval_record(complex_cost),
            'real_gram_determinant':interval_record(det),'status':status}


def transverse_candidate(k: list[Any], length: Any, X: Any, Y: Any) -> Any:
    """Full interval evaluation on X times Y; Y may contain zero."""
    a=length/2;S1=iv.mpf(0);S2=iv.mpf(0)
    for n in range(-64,65):
        u=X-2*iv.pi*n/length
        den=u**2+Y**2
        require(den>0, 'Box intersects an unresolved rational Fourier pole')
        S1+=k[n+64]*u/den
        S2+=k[n+64]/den
    return 2/iv.sqrt(length)*(iv.cos(a*X)*a*sinhc_enclosure(a*Y)*S1
        -iv.sin(a*X)*cosh(a*Y)*S2)


def certify(source: Path, energy: Path, digits: int=70) -> dict:
    require(digits>=40,'Insufficient directed-interval precision')
    iv.dps=digits
    p,e,inputs=literal_and_energy(source,energy)
    integer_energy=sum(x*x for x in p)
    require(integer_energy==1208925819614761052253583,'Integer norm mismatch')
    length=iv.ln(3);a=length/2
    k=[iv.mpf(x)/iv.sqrt(integer_energy) for x in p]
    points=[point_costs(k,length,e,x,y) for x,y in POINTS]
    # This continuous kernel bound applies to all real L2 errors, not only
    # their first 129 coefficients: |sinh(yt)/y| <= |t| cosh(a/2).
    K=cosh(a/2)*iv.sqrt(2*a**3/3)
    K_upper=Fraction(173,500);radius=Fraction(1,100);floor=Fraction(43,5000)
    require(K<Q(K_upper),'Full-space transverse kernel norm budget failed')
    require(floor-K_upper*radius==Fraction(257,50000)>Fraction(1,200),'Rational sign budget failed')
    cells=[];nx=16;ny=4
    for i in range(nx):
        xlo=Fraction(14)+Fraction(i,4*nx);xhi=Fraction(14)+Fraction(i+1,4*nx)
        X=interval_box(xlo,xhi)
        for j in range(ny):
            ylo=Fraction(j,2*ny);yhi=Fraction(j+1,2*ny);Y=interval_box(ylo,yhi)
            val=transverse_candidate(k,length,X,Y)
            require(val>Q(floor),f'Transverse floor failed on box {i},{j}')
            cells.append({'x':[str(xlo),str(xhi)],'abs_y':[str(ylo),str(yhi)],
                          'candidate_divided_imaginary_floor_scaled_1e18':endpoint_integer(val,False)})
    # Exact coverage endpoints and adjacency, no floating-point grid gaps.
    require(Fraction(cells[0]['x'][0])==14 and Fraction(cells[-1]['x'][1])==Fraction(57,4),'x endpoints')
    for i in range(nx):
        rows=cells[i*ny:(i+1)*ny]
        require(Fraction(rows[0]['abs_y'][0])==0 and Fraction(rows[-1]['abs_y'][1])==Fraction(1,2),'y endpoints')
        for j in range(ny-1):require(rows[j]['abs_y'][1]==rows[j+1]['abs_y'][0],'y adjacency')
        if i:require(cells[(i-1)*ny]['x'][1]==rows[0]['x'][0],'x adjacency')
    return {'status':'all point and full-box directed-interval comparisons passed',
      'scale':'a=log(3)/2','mpmath':mpmath.__version__,'digits':digits,
      'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'inputs':inputs,'candidate_integer_energy':str(integer_energy),
      'projective_error_square_premise':str(e),'points':points,
      'uniform_certificate':{
        'x_interval':['14','57/4'],'ordinate_condition':'0 < abs(y) <= 1/2',
        'real_even_error_norm_upper':str(radius),'full_space_kernel_norm_upper':str(K_upper),
        'kernel_norm_interval':interval_record(K),'candidate_transverse_floor':str(floor),
        'rational_transverse_margin':str(floor-K_upper*radius),
        'conclusion':'abs(Im(F(k+w)(x+iy))) > abs(y)/200; hence no nonreal zero in this tube',
        'covers_arbitrarily_small_nonzero_ordinates':True,
        'grid_boxes':len(cells),'x_subdivisions':nx,'abs_y_subdivisions':ny,
        'cell_floor_encoding':'Rows [x_index,y_index,lower_integer]; the lower bound is lower_integer/10^18. Indices start at zero.',
        'cell_floors':[[i,j,cells[i*ny+j]['candidate_divided_imaginary_floor_scaled_1e18']] for i in range(nx) for j in range(ny)]},
      'analytic_inputs':[
        'Existing full-domain Weil energy enclosure and projective error estimate; upstream spectral verifier not replayed',
        'Reality/evenness from actual domain symmetries; abstract semilinear uniqueness is supplied by paired Lean source',
        'The finite candidate uses V_n(t)=(-1)^n exp(2*pi*i*n*t/L)/sqrt(L), with unit coefficient normalization',
        'Even Fourier integral and its continuous divided-imaginary kernel; the sinc formula and sinhc series are elementary paper identities',
        'The full error kernel norm is bounded by cosh(a/2)*sqrt(2*a^3/3), using Cauchy-Schwarz and the sinh mean-value bound'],
      'not_claimed':['Lean kernel acceptance','a new spectral enclosure or enlarged support window',
        'existence or position of a zero from this exclusion certificate','an actual eigenvector for every ball witness',
        'uniform control along unbounded scales','prolate-to-Weil convergence on an unbounded sequence','RH']}


def main() -> None:
    root=Path(__file__).resolve().parent
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=root/'certify_prime3_refined.py')
    p.add_argument('--energy',type=Path,default=root/'prime3_neumann_weighted_certificate.json')
    p.add_argument('--output',type=Path,default=root/'prime3_real_transverse_certificate.json')
    p.add_argument('--digits',type=int,default=70)
    a=p.parse_args();report=certify(a.source,a.energy,a.digits)
    a.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':report['status'],'boxes':report['uniform_certificate']['grid_boxes'],
      'margin':report['uniform_certificate']['rational_transverse_margin'],
      'inputs':report['inputs'],'checker_sha256':report['checker_sha256']},indent=2))

if __name__=='__main__':main()
