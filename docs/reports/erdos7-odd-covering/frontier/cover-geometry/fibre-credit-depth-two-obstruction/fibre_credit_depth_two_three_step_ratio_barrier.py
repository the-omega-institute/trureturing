"""Exact enclosures and witnesses for the31/37/41 scalar kernel budget.

The recurrence and continuous capacity are reused from Chapter08 and304;
the accompanying note applies them to the current paired seed. This checker
uses rational arithmetic and the existing integer-square-root routines;
it imports no solver and performs no threshold grid.
It does not claim impossibility of the actual measure or covering problem.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod
from hashlib import sha256
import argparse,importlib.util,json

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

BASE=Path(__file__).resolve().parent
SEED=BASE/'fibre_credit_depth_two_eight_head_tail.json'
CAPACITY=BASE.parent/'scalar19-capacity-star-obstruction/scalar19_capacity_star_obstruction.py'
SEED_PIN='7d36e5003e12630787184af423db7a29972fa446195aa70c9b4765fc0d6d86eb'
need(sha256(SEED.read_bytes()).hexdigest()==SEED_PIN,'pinned paired source result')
CAPACITY_PIN='497732070e50ee817f3c31364ec0c22e59dca962e18007c2800707c8d2b23c21'
need(sha256(CAPACITY.read_bytes()).hexdigest()==CAPACITY_PIN,'existing304 exact scalar-capacity implementation')
spec=importlib.util.spec_from_file_location('e7_existing_scalar_capacity',CAPACITY)
capacity=importlib.util.module_from_spec(spec);spec.loader.exec_module(capacity)
seed=json.loads(SEED.read_text())
M0=F(10237584019,168750000000);G0=F(26010182627,1040449536)
need(M0==F(seed['source_mass_lower']) and G0==F(seed['joint_query_seed_upper']),'paired inherited ordinary seed')
P=(3,5,7,13,17,19,23,29);caps=(F(3,2),F(3,2),F(4,3),F(9,5),F(11,7),F(7,4))
def a(p):return F(3*p-1,(p-1)**2)
def c(p):return F(1,4*(p-1)**2)
need((F(1,2)+a(3))*(F(3,4)+a(5))*prod(1+C*a(p) for C,p in zip(caps,P[2:]))==G0,'same conditional pair-factor Gamma')

def sqrt_bounds(x):
 need(x>=0,'nonnegative radicand')
 low,high=capacity.root_interval(x)
 need(low*low<=x<=high*high,'integer-square-root exact enclosure')
 return low,high
def rounded_bounds(low,high,scale=10**18):
 need(low<=high,'ordered interval')
 lower=F(low.numerator*scale//low.denominator,scale)
 upper=F((high.numerator*scale+high.denominator-1)//high.denominator,scale)
 need(lower<=low<=high<=upper,'outward rational rounding')
 return lower,upper
def inverse_interval(p,low,high):
 # Existing304 SC1, with H=1/t: B_p(t)=1/C_p(1/t).
 # The t=0 limit is the one-step positivity threshold4c.
 need(0<=low<=high,'nonnegative target-ratio interval')
 lo=4*c(p) if low==0 else 1/capacity.capacity_interval(p,1/low)[1]
 hi=4*c(p) if high==0 else 1/capacity.capacity_interval(p,1/high)[0]
 return rounded_bounds(lo,hi)
def optimal_interval(p,low,high):
 # V_p(R) is increasing; radical signs are accounted for at both endpoints.
 A=a(p);C=c(p);need(low>4*C,'positive-step regime')
 sl=sqrt_bounds(C*(C+low*A*(1+A)))[1]
 sh=sqrt_bounds(C*(C+high*A*(1+A)))[0]
 lo=(low*(1+A)-2*C-2*sl)/(1+A)**2
 hi=(high*(1+A)-2*C-2*sh)/(1+A)**2
 need(lo>0,'positive optimal-ratio enclosure')
 return rounded_bounds(lo,hi)
def delta_interval(p,low,high):
 A=a(p);C=c(p)
 sl=sqrt_bounds(1+low*A*(1+A)/C)[0]
 sh=sqrt_bounds(1+high*A*(1+A)/C)[1]
 lo=(1+A)/(1+sh);hi=(1+A)/(1+sl)
 need(0<lo<=hi<F(1,2),'unique interior maximizer enclosure')
 return rounded_bounds(lo,hi)
def interval_record(pair):
 low,high=pair
 return dict(lower=str(low),upper=str(high),decimal_low=float(low),decimal_high=float(high))

R0=M0/G0
low=high=F(0);backward=[]
for p in (41,37,31):
 low,high=inverse_interval(p,low,high)
 backward.append(dict(prime=p,required_prior_ratio=interval_record((low,high))))
critical=(low,high)
need(R0<critical[0],'current paired seed strictly below exact continuous threshold')
mass_target=rounded_bounds(G0*critical[0],G0*critical[1])
gamma_target=rounded_bounds(M0/critical[1],M0/critical[0])
forward=[];low=high=R0
for p in (31,37):
 best_delta=delta_interval(p,low,high)
 low,high=optimal_interval(p,low,high)
 forward.append(dict(prime=p,optimal_delta=interval_record(best_delta),best_next_ratio=interval_record((low,high))))
need(high<F(1,1600),'even continuous greedy-optimal first two steps fail the41 positivity gate')

# A coarser obstruction without square roots. These are bounds on the
# scalar certificate variables, not lower bounds on actual Gamma.
gamma_budget_floor=G0;unavoidable_budget_loss=F(0)
for p in (31,37,41):
 unavoidable_budget_loss+=gamma_budget_floor/F((p-1)**2)
 gamma_budget_floor*=1+a(p)
budget_upper=M0-unavoidable_budget_loss
need(budget_upper==F(-1857729195660261599,263363788800000000000)<0,'all-delta elementary budget obstruction')

def rational_witness(mass,gamma):
 rows=[]
 for p,delta in zip((31,37,41),(F(9,20),F(47,100),F(1,2))):
  need(0<delta<=F(1,2),'allowed rational clipping')
  loss=gamma/(4*delta*(1-delta)*(p-1)**2)
  mass-=loss;gamma*=1+a(p)/(1-delta)
  need(mass>0,'positive mass after every proposed improved-seed step')
  rows.append(dict(prime=p,delta=str(delta),mass_lower=str(mass),gamma_upper=str(gamma),ratio=str(mass/gamma)))
 return rows
improved_gamma=F(209,10);improved_mass=F(73,1000)
need(M0/improved_gamma>critical[1] and improved_mass/G0>critical[1],'both actionable improved paired seeds cross the exact threshold')
out=dict(scope=__doc__,inherited_seed_sha256=sha256(SEED.read_bytes()).hexdigest(),existing304_capacity_sha256=CAPACITY_PIN,generic_scalar_optimization_reused=True,seed_mass=str(M0),seed_gamma=str(G0),seed_ratio=str(R0),seed_ratio_decimal=float(R0),
         reference_extra_primes=[31,37,41],backward_thresholds=backward,critical_initial_ratio=interval_record(critical),
         required_mass_with_old_gamma=interval_record(mass_target),maximum_gamma_with_old_mass=interval_record(gamma_target),
         continuous_optimal_forward=forward,third_step_positive_ratio_gate='1/1600',
         elementary_total_budget_loss_lower=str(unavoidable_budget_loss),elementary_final_budget_upper=str(budget_upper),
         improved_gamma_seed=dict(mass=str(M0),gamma=str(improved_gamma),steps=rational_witness(M0,improved_gamma)),
         improved_mass_seed=dict(mass=str(improved_mass),gamma=str(G0),steps=rational_witness(improved_mass,G0)),
         actual_improved_seeds_constructed=False,improved_source_bounds_are_open_obligations=True,
         all_constant_delta_choices_covered_by_proof=True,no_finite_grid_or_solver=True,
         actual_measure_or_covering_obstruction=False,lean_verification=False)
if __name__=='__main__':
 parser=argparse.ArgumentParser()
 parser.add_argument('--write-result',type=Path)
 args=parser.parse_args()
 if args.write_result:
  args.write_result.write_text(json.dumps(out,indent=2)+'\n')
 else:
  retained=json.loads(Path(__file__).with_suffix('.json').read_text())
  need(out==retained,'retained result agrees with exact recomputation')
 print(json.dumps(out,indent=2))
