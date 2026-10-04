"""Uncertified common-matrix screen; periodic FFT is not a spectral proof."""
import argparse
import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path
import numpy as np
import scipy
from scipy.special import digamma, eval_legendre, roots_legendre
from threadpoolctl import threadpool_limits

parser = argparse.ArgumentParser()
parser.add_argument('--grid', type=int, default=16384)
parser.add_argument('--radius', type=float, default=32.0)
parser.add_argument('--quadrature', type=int, default=384)
parser.add_argument('--correctors', action='store_true')
parser.add_argument('--export-trials', type=Path,
                    help='Save exact rounded dyadic trial and correction-map coefficients')
args = parser.parse_args()
if args.export_trials is not None and not args.correctors:
    parser.error('--export-trials requires --correctors')
if args.grid < 256 or args.grid % 2 or args.radius < 4 or args.quadrature < 95:
    parser.error('Require an even grid >=256, radius >=4 and quadrature >=95')
threadpool_limits(limits=2)
started = time.monotonic()
N, count, c = 64.0, 95, 3/8
delta = 0.0383682545007734
size, radius = args.grid, args.radius
dx = 2*radius/size
x = -radius+dx*np.arange(size)
xi = 2*np.pi*np.fft.fftfreq(size, d=dx)
symbol = np.real(digamma(0.25+0.5j*xi))-digamma(0.25)
gamma_c = float(digamma(0.25)-np.log(np.pi))
alpha = 0.5-c
low = np.abs(xi)<N


def theta(z):
    a = np.abs(z)
    u = np.exp(2*a)
    out = np.zeros_like(a)
    for k in range(1, 7):
        out += (4*np.pi**2*k**4*np.exp(4.5*a)
                -6*np.pi*k*k*np.exp(2.5*a))*np.exp(-np.pi*k*k*u)
    return out


phi = theta(x)
s = np.sqrt(phi/(2*np.cosh(x/2)))
v0 = np.sqrt(2*phi*np.cosh(x/2))
local = np.flatnonzero(np.abs(x)<=3)
quadrature_x, quadrature_weight = roots_legendre(args.quadrature)
eta = N*(quadrature_x+1)/2
weight = N*quadrature_weight/2
polys = np.stack([np.sqrt((2*j+1)/N)*eval_legendre(j,quadrature_x)
                  for j in range(count)], axis=1)
weighted = weight[:,None]*polys/np.sqrt(np.pi)
cosine = np.cos(x[local,None]*eta[None,:])
sine = np.sin(x[local,None]*eta[None,:])
# The input functions are continuous-band integrals approximated on local x.
# Outside [-3,3] p is zeroed only in this screening program. alpha*I is exact
# in the coefficient coordinates, but omitted physical/FFT errors are unpaid.
p = np.zeros((size,count))
p[local] = cosine@weighted
sp = s[:,None]*p
hp = s[:,None]*np.fft.ifft(symbol[:,None]*np.fft.fft(sp,axis=0),axis=0).real
hp += gamma_c*s[:,None]**2*p
prime_terms=[]
for prime in range(2,65):
    if any(prime%d==0 for d in range(2,int(np.sqrt(prime))+1)):
        continue
    power = prime
    while power<=64:
        prime_terms.append((power,np.log(prime)/np.sqrt(power)))
        power *= prime
prime_terms.sort()
for n,w in prime_terms:
    t = np.log(n)
    cos_t,sin_t = np.cos(eta*t),np.sin(eta*t)
    plus = cosine@(weighted*cos_t[:,None])-sine@(weighted*sin_t[:,None])
    minus = cosine@(weighted*cos_t[:,None])+sine@(weighted*sin_t[:,None])
    s_plus=np.sqrt(theta(x[local]+t)/(2*np.cosh((x[local]+t)/2)))
    s_minus=np.sqrt(theta(x[local]-t)/(2*np.cosh((x[local]-t)/2)))
    hp[local] -= w*s[local,None]*(s_plus[:,None]*plus+s_minus[:,None]*minus)
mean = dx*(v0@p)
hp += c*v0[:,None]*mean[None,:]
raw_h = dx*p.T@hp
center = alpha*np.eye(count)+(raw_h+raw_h.T)/2
ph = (dx/np.sqrt(np.pi))*cosine.T@hp[local]
low_gram=ph.T@(weight[:,None]*ph)
hp_gram=dx*hp.T@hp
coupling_gram=(hp_gram-low_gram)
coupling_gram=(coupling_gram+coupling_gram.T)/2
fft_hp=np.fft.fft(hp,axis=0)
fft_hp[low]=0
z=np.fft.ifft(fft_hp,axis=0).real
fft_coupling_gram=dx*z.T@z
unit_mean=mean/np.linalg.norm(mean)
direction=unit_mean.copy()
direction[0]-=1
if np.linalg.norm(direction)==0:
    deflated=np.eye(count)[:,1:]
else:
    direction/=np.linalg.norm(direction)
    deflated=(np.eye(count)-2*np.outer(direction,direction))[:,1:]
q0=center-coupling_gram/delta


def symmetric(a):
    return (a+a.T)/2


def eig_min(a):
    return float(np.linalg.eigvalsh(symmetric(a))[0])


result={
 'scope':'Uncertified floating-point common matrix screen, not positivity evidence; continuous input quadrature, periodic FFT and approximate ground deflation have unpaid errors',
 'runtime':{'numpy':np.__version__,'scipy':scipy.__version__},
 'grid':size,'physical_radius':radius,'input_quadrature':args.quadrature,
 'polynomial_count':count,'bandwidth':N,'target_c':c,'delta_hypothesis':delta,
 'retained_prime_powers':[n for n,_ in prime_terms],
 'theta_mass':float(dx*(v0@v0)),
 'input_gram_error':float(np.linalg.norm(polys.T@(weight[:,None]*polys)-np.eye(count),2)),
 'raw_center_asymmetry':float(np.linalg.norm(raw_h-raw_h.T,2)),
 'mean_coefficient_norm':float(np.linalg.norm(mean)),
 'ground_center_residual_norm':float(np.linalg.norm(center@unit_mean)),
 'min_coupling_gram_eigenvalue':eig_min(coupling_gram),
 'continuous_vs_fft_coupling_gram_error':float(np.linalg.norm(coupling_gram-fft_coupling_gram,2)),
 'deflated_center_min':eig_min(deflated.T@center@deflated),
 'deflated_q0_lower_min':eig_min(deflated.T@q0@deflated),
 'deflated_fft_q0_lower_min':eig_min(deflated.T@(center-fft_coupling_gram/delta)@deflated),
 'certified':False,
}
if args.correctors:
    # Explicit trial family selected from the computed high images only.
    g=dx*z.T@z
    vals,vectors=np.linalg.eigh(symmetric(g))
    keep=vals>1e-8
    coefficients=vectors[:,keep]/np.sqrt(vals[keep])[None,:]
    zb=z@coefficients
    sz=s[:,None]*zb
    tz=alpha*zb+s[:,None]*np.fft.ifft(
        symbol[:,None]*np.fft.fft(sz,axis=0),axis=0).real
    tz+=gamma_c*s[:,None]**2*zb
    fft_zb=np.fft.fft(zb,axis=0)
    for n,w in prime_terms:
        t=np.log(n)
        plus=np.fft.ifft(fft_zb*np.exp(1j*xi*t)[:,None],axis=0).real
        minus=np.fft.ifft(fft_zb*np.exp(-1j*xi*t)[:,None],axis=0).real
        s_plus=np.sqrt(theta(x+t)/(2*np.cosh((x+t)/2)))
        s_minus=np.sqrt(theta(x-t)/(2*np.cosh((x-t)/2)))
        tz-=w*s[:,None]*(s_plus[:,None]*plus+s_minus[:,None]*minus)
    tz+=c*v0[:,None]*(dx*v0@zb)[None,:]
    fft_tz=np.fft.fft(tz,axis=0)
    fft_tz[low]=0
    cz=np.fft.ifft(fft_tz,axis=0).real
    d0=delta/2
    f=dx*zb.T@cz
    j=symmetric(dx*cz.T@cz-d0*f)
    h=dx*(cz-d0*zb).T@z
    j_min=eig_min(j)
    if j_min<=0:
        raise RuntimeError('Numerical corrector Gram is not positive')
    inverse_upper=symmetric((g-h.T@np.linalg.solve(j,h))/d0)
    corrected=center-inverse_upper
    result.update({
     'high_corrector_count':int(np.count_nonzero(keep)),
     'corrector_gram_min':j_min,
     'deflated_corrected_lower_min':eig_min(deflated.T@corrected@deflated),
     'inverse_upper_min':eig_min(inverse_upper),
     'corrector_ground_constraint':'Not imposed exactly; no matrix certificate'})
    if args.export_trials is not None:
        # Fix actual dyadic numbers, not eigenvectors of an unknown operator.
        # These are trial choices; neither quadrature nor their sign is certified.
        bits = 40
        correction_map = np.linalg.solve(j,h)

        def dyadic_matrix(matrix):
            if not np.all(np.isfinite(matrix)):
                raise RuntimeError('Nonfinite trial coefficient')
            return [[str(round(Fraction.from_float(float(v)) * (1 << bits)))
                     for v in row] for row in matrix]

        trial = {
            'scope': 'Exact dyadic trial choices selected by an uncertified periodic '
                     'screen; no directed Gram or matrix sign certificate',
            'coefficient_exponent': -bits,
            'input_basis': 'p_j(x)=pi^(-1/2) integral_0^64 cos(eta*x) '
                           'sqrt((2*j+1)/64) P_j(eta/32-1) d eta, j=0,...,94',
            'actual_high_trial_definition': 'z_a=Q (T_1024,64-alpha I) '
                                            'sum_j B[j,a] p_j on the whole real line',
            'actual_operator': 'Even minimal theta realization; '
                               'alpha=1/8, c=3/8, N=64; exact mean and multiplication',
            'selection_operator': 'Periodic FFT with full digamma symbol and primes '
                                  'through 64; differs from actual high trial definition',
            'trial_coefficients_B': dyadic_matrix(coefficients),
            'correction_map_A': dyadic_matrix(correction_map),
            'ground_lift': 'Y=-|Qv0><p0|/||p0||^2 + Z A E* (I-Pi_p0), '
                           'p0=Pv0; exact symbolic lift, not imposed in this screen',
            'selection_parameters': {'grid': size, 'physical_radius': radius,
                                     'input_quadrature': args.quadrature},
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'certified': False,
        }
        args.export_trials.write_text(json.dumps(trial, indent=2)+'\n')
        result['exported_trial_data'] = args.export_trials.name
        result['exported_trial_sha256'] = hashlib.sha256(
            args.export_trials.read_bytes()).hexdigest()
result['elapsed_seconds']=time.monotonic()-started
output=Path(__file__).with_name(
 f'common-matrix-screen-{size}-{int(radius)}-'+
 ('corrected' if args.correctors else 'q0')+'.json')
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
