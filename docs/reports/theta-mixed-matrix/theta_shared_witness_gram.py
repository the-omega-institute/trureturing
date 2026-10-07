"""Shared actual-metric critical/dual Gram for left J4 profiles."""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import flint
from flint import acb, arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('shared_profile', HERE/'theta_profile_residual_gram.py')
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)
m = p.module


def decode(v):
    def point(key):
        a, e = map(int, v[key])
        return arb(a)*arb(2)**e
    lo, hi = point('lower_dyadic'), point('upper_dyadic')
    if not lo.is_finite() or not hi.is_finite() or lo > hi:
        raise ValueError('Finite ordered supplied endpoints required')
    return arb((lo+hi)/2, ((hi-lo)/2).upper())


def tail(power, radius):
    return m.bounds.exponential_integral_upper(power, arb.pi(), (2*arb(radius)).exp())


def dual_action(denominator=16, zero_index=1):
    if denominator <= 0 or zero_index <= 0:
        raise ValueError('Positive dual denominator and zero index required')
    action = m.Action({'n_coefficients_exact_dyadic_rationals': [],
                       'w_coefficients_exact_dyadic_rationals': []})
    action.b = [fmpq(1, denominator)]
    action.gammas = [acb.zeta_zero(zero_index).imag]
    return action


def exact(v):
    mant, exp = map(int, v.man_exp())
    return Fraction(mant)*Fraction(2)**exp


def upper_gram(gram, exterior):
    count = len(gram)
    center = [[v.mid() for v in row] for row in gram]
    radii = [[max((gram[i][j].upper()-center[i][j]).upper(),
                  (center[i][j]-gram[i][j].lower()).upper())
              for j in range(count)] for i in range(count)]
    inflation = [sum(row, arb(0)).upper() for row in radii]
    tau = sum(exterior, arb(0)).upper()
    upper = [[(center[i][j]+inflation[i]+tau).upper() if i == j else center[i][j]
              for j in range(count)] for i in range(count)]
    pivots, factor = [], [[arb(0) for _ in range(count)] for _ in range(count)]
    for i in range(count):
        pivot = upper[i][i]-sum((factor[i][j]**2*pivots[j] for j in range(i)), arb(0))
        if not pivot > 0:
            raise ValueError('Positive upper-Gram LDL pivot required')
        pivots.append(pivot)
        for j in range(i+1, count):
            factor[j][i] = (upper[j][i]-sum((factor[j][k]*factor[i][k]*pivots[k]
                                           for k in range(i)), arb(0)))/pivot
    return center, inflation, tau, upper, pivots


def norm_upper(upper):
    if len(upper) == 2:
        a, b, c = upper[0][0], upper[0][1], upper[1][1]
        return ((a+c)/2+((a-c)**2/4+b*b).sqrt()).upper()
    return max((upper[i][i]+sum((abs(v).upper() for j, v in enumerate(row) if j != i),
                                arb(0))).upper() for i, row in enumerate(upper))


def read_profiles(path, precision):
    data = json.loads(path.read_text())
    if data['runtime']['precision_bits'] != precision:
        raise ValueError('Same declared precision as supplied profile rows required')
    for name, digest in data['supplier_sha256'].items():
        if hashlib.sha256((HERE/name).read_bytes()).hexdigest() != digest:
            raise ValueError('Supplied profile rows must match current supplier definitions')
    if hashlib.sha256((HERE/'theta_profile_residual_gram.py').read_bytes()).hexdigest() != data['producer_sha256']:
        raise ValueError('Current profile source contract required')
    count, boxes = len(data['centers_exact']), data['radial_boxes']
    radius = fmpq(data['spatial_radius_exact'])
    if count < 1 or len(data['cell_widths_exact']) != count or len(data['cells']) != boxes or not 0 < radius < 5:
        raise ValueError('Complete supplied profile family inside action cutoff required')
    for i, cell in enumerate(data['cells']):
        if cell['index'] != i or fmpq(cell['midpoint_exact']) != radius*fmpq(2*i+1, 2*boxes) or len(cell['columns']) != count:
            raise ValueError('Complete ordered same-source profile cells required')
    return data

class CriticalAction(m.Action):
    def __init__(self, denominator=64):
        if denominator <= 0:
            raise ValueError("Positive critical normalization denominator required")
        self.denominator = denominator
        super().__init__({'n_coefficients_exact_dyadic_rationals':[[-1,denominator]],
                          'w_coefficients_exact_dyadic_rationals':[]})
    def weighted_source(self,z):
        jets,factor=m.support.theta_jets(z,order=2)
        return factor*jets[0],factor*(jets[1]-jets[0]/4)/self.denominator
    def source(self,z):
        jets,_=m.support.theta_jets(z,order=2)
        return (jets[1]/jets[0]-acb(fmpq(1,4)))/self.denominator
    def source_derivative(self,r):
        return super().source_derivative(r)-2*r
    def action_tail(self,real_r,cap,f_at_r):
        start=(2*(arb(cap)-abs(real_r).upper())).exp()
        t2=m.bounds.exponential_integral_upper(2,arb.pi(),start)
        t4=m.bounds.exponential_integral_upper(4,arb.pi(),start)
        return (2*(abs(f_at_r).upper()*self.constants[0]*t2
                   +(self.constants[1]*t4+self.constants[0]*t2/4)/self.denominator)).upper()
    def source_l1(self,radius,cells):
        interior=arb(0)
        for i in range(cells):
            lo,hi=radius*i/cells,radius*(i+1)/cells
            r=arb((lo+hi)/2,arb((hi-lo)/2).upper())
            _,weighted=self.weighted_source(acb(r))
            interior+=4*arb(hi-lo)*abs(weighted).upper()*(r/2).cosh().upper()
        return (interior+4*(self.constants[1]*tail(4,radius)
                            +self.constants[0]*tail(2,radius)/4)/self.denominator).upper()
    def exterior_residual_squared(self,radius,l1):
        A=4*arb.pi()**2-6*arb.pi()
        assert A>0
        f_squared=8*self.constants[0]/(self.denominator**2)*((self.constants[1]/A)**2*tail(6,radius)
                                              +tail(2,radius)/16)
        mass=4*self.constants[0]*tail(2,radius)
        return (f_squared/2+l1*l1*mass/2).upper()


def produce(profiles_path, critical_denominator=64, dual_denominator=16, zero_index=1, coefficient_bits=20, precision=192):
    if precision<128 or coefficient_bits<1:
        raise ValueError('At least 128 bits and one coefficient bit required')
    ctx.prec=precision
    profiles=read_profiles(profiles_path,precision)
    critical=CriticalAction(critical_denominator)
    dual=dual_action(dual_denominator, zero_index)
    radius=fmpq(profiles['spatial_radius_exact']);boxes=profiles['radial_boxes'];count=len(profiles['centers_exact']);size=count+2
    l1=critical.source_l1(radius,boxes)
    exterior=[decode(v) for v in profiles['exterior_column_squared_upper']]
    exterior+=[critical.exterior_residual_squared(radius,l1),
               4*critical.constants[0]*tail(2,radius)/(dual_denominator**2)]
    gram=[[arb(0) for _ in range(size)] for _ in range(size)];rows=[]
    for i,cell in enumerate(profiles['cells']):
        midpoint=radius*fmpq(2*i+1,2*boxes);half=radius/(2*boxes)
        assert cell['index']==i and fmpq(cell['midpoint_exact'])==midpoint
        r=arb(midpoint,arb(half).upper())
        b=[decode(v['scaled_full_cell_residual']) for v in cell['columns']]
        point,action_tail=critical.value(acb(midpoint),tolerance='1e-12')
        gap=decode(cell['support_gap_lower']).lower();assert gap>0
        coth=gap.cosh()/gap.sinh()
        slope=(abs(critical.source_derivative(r)).upper()
               +coth*(abs(critical.source(acb(r))).upper()+l1))/2
        critical_cell=point+arb(0,(arb(half)*slope).upper())
        dual_cell=dual.witness(acb(r)).real
        b += [critical_cell,dual_cell]
        density=decode(cell['folded_density'])
        for j in range(size):
            for k in range(j,size):
                gram[j][k]+=arb(radius/boxes)*density*b[j]*b[k]
                assert gram[j][k].is_finite()
                gram[k][j]=gram[j][k]
        rows.append({'index':i,'midpoint_exact':str(midpoint),
                     'B_critical_point':m.endpoints(point),'action_tail_upper':m.endpoints(action_tail),
                     'critical_cell':m.endpoints(critical_cell),'dual_cell':m.endpoints(dual_cell),
                     'critical_lipschitz_upper':m.endpoints(slope.upper())})
        if i%16==0:print(json.dumps({'cell':i,'cells':boxes}),flush=True)
    A,row_inflation,tau,upper,pivots=upper_gram(gram,exterior)

    K=[[exact(v) for v in row] for row in upper]
    det=K[count][count]*K[count+1][count+1]-K[count][count+1]**2
    assert det>0
    coeff=[]
    for j in range(count):
        a=(K[count+1][count+1]*K[count][j]-K[count][count+1]*K[count+1][j])/det
        b=(K[count][count]*K[count+1][j]-K[count][count+1]*K[count][j])/det
        coeff.append([Fraction(round(a*2**coefficient_bits),2**coefficient_bits),Fraction(round(b*2**coefficient_bits),2**coefficient_bits)])
    T=[[Fraction(int(i==j)) for j in range(count)] for i in range(count)]
    T+=[[-row[0] for row in coeff],[-row[1] for row in coeff]]
    corrected=[[sum(T[a][i]*K[a][b]*T[b][j] for a in range(size) for b in range(size))
                for j in range(count)] for i in range(count)]
    C=[[arb(fmpq(v.numerator,v.denominator)) for v in row] for row in corrected]
    norm=norm_upper(C)
    result={'scope':'Conditional simultaneous whole-space shared critical/dual basis Gram for the supplied actual J4 profiles under numerical-supplier and certified-input-row premises; no complete growing family, cofinal sign, Lean, Robin or RH certificate',
            'runtime':{'python':sys.version.split()[0],'python_flint':flint.__version__,'precision_bits':ctx.prec},
            'critical_denominator':critical_denominator,'dual_denominator':dual_denominator,'zero_index':zero_index,
            'coefficient_bits':coefficient_bits,'radial_boxes':boxes,'spatial_radius_exact':str(radius),
            'centers_exact':profiles['centers_exact'],'cell_widths_exact':profiles['cell_widths_exact'],'source_l1_upper':m.endpoints(l1),
            'profile_rows_sha256':hashlib.sha256(profiles_path.read_bytes()).hexdigest(),
            'basis':['B e_'+r for r in profiles['centers_exact']]+['B(U v1/'+str(critical_denominator)+')','individual Xi dual/'+str(dual_denominator)],
            'primal_dual_coefficients_exact':[[[str(c.numerator),str(c.denominator)] for c in row] for row in coeff],
            'interior_cross_gram':[[m.endpoints(v) for v in row] for row in gram],
            'interior_center_matrix':[[m.endpoints(v) for v in row] for row in A],
            'row_inflation':list(map(m.endpoints,row_inflation)),
            'exterior_gram_norm_upper':m.endpoints(tau),
            'exterior_column_squared':list(map(m.endpoints,exterior)),
            'positive_upper_basis_gram':[[m.endpoints(v) for v in row] for row in upper],
            'corrected_upper_gram_exact_rationals':[[[str(v.numerator),str(v.denominator)] for v in row] for row in corrected],
            'corrected_upper_gram_norm_upper':m.endpoints(norm),
            'congruence_beats_supplied_zero_allowance':bool(norm<decode(profiles['upper_gram_norm_upper']).upper()),
            'individual_zero_ball':m.endpoints(dual.gammas[0]),'positive_ldl_pivots':list(map(m.endpoints,pivots)),
            'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'supplier_sha256':profiles['supplier_sha256'],'critical_callbacks':critical.calls,
            'critical_rejections':critical.rejections,'fresh_witness_rows':rows,
            'old_quadratic_rows_or_grid_producers_used':False}

    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profiles',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--critical-denominator',type=int,default=64)
    parser.add_argument('--dual-denominator',type=int,default=16)
    parser.add_argument('--zero-index',type=int,default=1)
    parser.add_argument('--coefficient-bits',type=int,default=20)
    parser.add_argument('--precision',type=int,default=192)
    args=parser.parse_args()
    result=produce(args.profiles,args.critical_denominator,args.dual_denominator,
                   args.zero_index,args.coefficient_bits,args.precision)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['primal_dual_coefficients_exact','corrected_upper_gram_norm_upper']},indent=2))


if __name__=='__main__':
    main()
