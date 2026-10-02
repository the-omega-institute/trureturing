"""Bound replay of the registered fixed-source common-centre experiment.

Default action replays and compares the deterministic result beside this script.
--write-result explicitly writes it. --validate-only binds the input interface.
No optimizers or upstream consumers run.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import prod
from time import perf_counter
import argparse
import hashlib
import importlib.util
import json
import signal
import sys

EXPECTED={
 'retained_factorial_hinge_certificate.json':'17557f86d60a40310275025219d893e28ba103b5f099cf53886a8eb8ef970aca',
 'retained_factorial_hinge.json':'1e76928fa5e63ca221913ad6cdd7ba0db4a54ab093a3a2c26086e1e08b1710e5',
 'selective_conditioning_hinge.json':'4c43fae0a6a6aa2b28e0fba7239cab2882c21da3337107501603ba0e296fd397'}
PRIMES=(5,7,11,13,17,19,23)
LEAVES=(4,7,2,5,8)
checks=0

def check(ok,message):
 global checks
 checks+=1
 if not ok:raise ValueError(message)

def sha(data):return hashlib.sha256(data).hexdigest()
def encode(value):
 if isinstance(value,F):return str(value)
 if isinstance(value,dict):return {str(k):encode(v) for k,v in value.items()}
 if isinstance(value,(tuple,list)):return [encode(v) for v in value]
 return value

def write(path,value):
 data=(json.dumps(encode(value),indent=2,sort_keys=True)+'\n').encode()
 Path(path).write_bytes(data)
 return {'sha256':sha(data),'bytes':len(data)}

def bind(directory):
 raw={name:(directory/name).read_bytes() for name in EXPECTED}
 # Every dependency is bound before any dependency JSON is parsed.
 for name,data in raw.items():check(sha(data)==EXPECTED[name],'immutable input '+name)
 inputs={name:json.loads(data) for name,data in raw.items()}
 cert=inputs['retained_factorial_hinge_certificate.json']
 old=inputs['retained_factorial_hinge.json']
 upper=inputs['selective_conditioning_hinge.json']
 check(cert['schema']=='e7-retained-factorial-hinge-fixed-candidate-v1','certificate schema')
 check(old['schema']=='e7-retained-factorial-hinge-result-v1','827 schema')
 check(upper['schema']=='e7-selective-conditioning-result-v1','830 schema')
 check(tuple(cert['primes'])==PRIMES and tuple(cert['leaves'])==LEAVES,'fixed source axes')
 check(all(x['phase45']==31 for x in (cert,old,upper)),'unchanged phase31')
 check([45,31] in cert['actual_family'],'certificate phase31 actual label')
 check(cert['weights']==old['weights']==upper['weights'],'unchanged weights')
 check(all(x['normalization']=='nu_u restricted to U / nu_u(U)' for x in (cert,old,upper)),
       'upstream certificate normalization; experiment explicitly uses its raw nu_u ingredient')
 patterns=tuple(product(range(3),*(range(2) for _ in PRIMES[1:])))
 check(len(patterns)==192,'fixed lexicographic categorical pattern index')
 expected_partitions=[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in PRIMES[1:]]
 check(cert['partitions']==expected_partitions,'exact declared colour partition')
 weights=tuple(F(v) for v in cert['weights'])
 check(sum(weights)==1 and all(v>=0 for v in weights),'retained envelope weights')
 table={}
 for row in cert['nonzero_u']:
  l,pid=row['leaf_index'],row['pattern_id']
  check(isinstance(l,int) and 0<=l<5 and isinstance(pid,int) and 0<=pid<192,'table coordinates')
  idx=(l,)+patterns[pid]
  check(idx not in table,'no repeated retained entry')
  u=F(row['u'])
  check(0<u<=weights[l],'retained u lies below its own leaf weight')
  table[idx]=u
 check(len(table)==106==old['nonzero_u']==upper['nonzero_u'],'unchanged106 retained entries')
 point=old['fixed_candidate_C']['point']
 check(point==upper['point'],'same C source point')
 check(point['name']=='C' and point['vertex5']==2 and point['other_mask']==63,'fixed C design')
 deltas=tuple(F(q-1,q-2) for q in PRIMES)
 probabilities=((deltas[0]/5,deltas[0]/5,1-2*deltas[0]/5),)+tuple((d/q,1-d/q) for q,d in zip(PRIMES[1:],deltas[1:]))
 check(tuple(tuple(F(v) for v in row) for row in point['probabilities'])==probabilities,'specified831 infinite pure-comb source law')
 exact=old['fixed_candidate_C']['exact']
 M,L,tail=(F(exact[k]) for k in ('M','L','tail'))
 for k,v in (('M',M),('L',L),('tail',tail)):check(v==F(upper['inherited_exact'][k]),'unchanged inherited '+k)
 check(M>0 and 0<=L<=M and tail>=0,'inherited mass/budget range')
 curve=upper['curve']
 check(len(curve)==29 and [row['h'] for row in curve]==list(range(29)),'830 complete integer grid')
 D=tuple(F(row['dp']) for row in curve)
 for h,row in enumerate(curve):
  check(F(row['dp'])==F(row['root_stop']),'830 root-stop identity')
  check(F(row['gate'])==(28-h)*L-tail-D[h],'830 unchanged budget identity')
 return table,deltas,probabilities,M,L,tail,D

def finite_query_tail_certificate():
 J,E=8,4
 mu=tuple(F(q-1,q-2) for q in PRIMES)
 tau=tuple(F(1,(q-2)*q**E) for q in PRIMES)
 tau3=F(1,2*3**(J-2))
 A=prod(mu);B=prod(m-t for m,t in zip(mu,tau))
 error=F(7,2)*A-(F(7,2)-tau3)*B
 labels=(J+1)*(E+1)**len(PRIMES)
 check(labels==703125,'fixed finite-query label count including unit')
 check(0<error<F(1,100),'uniform finite-query hinge error strictly below1/100')
 return {'schema':'e7-common-centre-finite-query-tail-v1',
  'source':'same infinite pure-comb C law, no finite-original-source claim',
  'ternary_depth':J,'nonternary_depths':{str(q):E for q in PRIMES},
  'query_labels_including_unit':labels,'mu_q':mu,'tau_q':tau,'tau3':tau3,
  'full_nonternary_mean_bound':A,'truncated_nonternary_mean':B,
  'uniform_hinge_truncation_error_bound':error,'error_display':float(error),
  'strict_error_upper':'1/100',
  'proof':'nu_u dominated by normalized leaf-envelope product source; mean difference m3(A-B)+w_centre*tau3*B <= (7/2)A-(7/2-tau3)B; hinge difference bounded by same nonnegative mean difference',
  'conditional_finite_zero_tail_gate_bound':'-9/500',
  'condition':'one fixed complete centre zero-tail gate strictly below -7/250 for all0<=h<28',
  'numerical_scope':'one predetermined seven-factor rational expression; no depth search, query enumeration or candidate optimization'}

def compare_results(expected,actual):
 check(expected==actual,'complete deterministic result comparison')

def timeout_handler(signum,frame):raise TimeoutError('registered600-second execution bound reached')

def main():
 parser=argparse.ArgumentParser()
 parser.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 parser.add_argument('--engine',type=Path,default=Path(__file__).with_name('common_center_engine.py'))
 parser.add_argument('--out',type=Path,default=Path(__file__).with_name('common_center_hinge.json'))
 parser.add_argument('--transient-laws',type=Path)
 parser.add_argument('--validate-only',action='store_true')
 parser.add_argument('--write-result',action='store_true')
 args=parser.parse_args()
 started=perf_counter()
 bindings={'inputs':EXPECTED,'engine_sha256':sha(args.engine.read_bytes()),
           'wrapper_sha256':sha(Path(__file__).read_bytes())}
 table,deltas,probabilities,M,L,tail,D=bind(args.input_dir)
 if args.validate_only:
  out={'schema':'e7-common-centre-wrapper-validation-v1','status':'pass',
       'bindings':bindings,'checks':checks,'research_menu_evaluated':False,
       'scope':'immutable-input/schema/phase/table/inherited-scalar validation only'}
  print(json.dumps(out,indent=2));return
 signal.signal(signal.SIGALRM,timeout_handler);signal.alarm(600)
 spec=importlib.util.spec_from_file_location('common_centre_exact_engine',args.engine)
 engine=importlib.util.module_from_spec(spec);sys.modules[spec.name]=engine;spec.loader.exec_module(engine)
 print('BOUND inputs; starting one fixed960-centre exact tensor',flush=True)
 begin=perf_counter()
 laws,stats=engine.centres(PRIMES,deltas,probabilities,LEAVES,table,27)
 tensor_seconds=perf_counter()-begin
 check(len(laws)==960,'exact960-centre menu')
 check(stats['atom_terms_considered']==1824000,'declared low-atom operation count')
 check(stats['scalar_product_terms']==38400,'declared scalar operation count')
 curves={}
 for centre,law in laws.items():
  check(law.mass==M,'each centre has inherited raw mass M')
  curve=tuple(engine.hinge(law,h) for h in range(29))
  for h,value in enumerate(curve):check(0<=value<=D[h],'nonnegative centre hinge bounded by830D')
  for a,b in zip(curve,curve[1:]):check(-M<=b-a<=0,'hinge monotonicity and mass slope bound')
  for a,b,c in zip(curve,curve[1:],curve[2:]):check(a-2*b+c>=0,'integer hinge convexity')
  curves[centre]=curve
 print('TENSOR complete; all centre masses/hinges/830bounds passed; building exact hull',flush=True)
 envelope=engine.centre_envelope(curves,28)
 for segment in envelope:
  c=segment['label']
  for h in (segment['left'],segment['right']):
   check(segment['alpha']+segment['beta']*h==engine.hinge(laws[c],h),'exact segment witness at its rational endpoints')
 primary=engine.affine_budget_max(envelope,28*L-tail,-L)
 zero_tail=engine.affine_budget_max(envelope,28*L,-L)
 def interpolate_upper(h):
  j=h.numerator//h.denominator
  return D[28] if j==28 else D[j]+(h-j)*(D[j+1]-D[j])
 def comparison(h):
  values={c:engine.hinge(law,h) for c,law in laws.items()}
  H=max(values.values());selected=min(c for c,v in values.items() if v==H)
  upper=interpolate_upper(h)
  check(H<=upper,'rational-threshold bracket')
  return {'h':h,'selected_centre':selected,'ties':sum(v==H for v in values.values()),
          'H_centres':H,'D_830':upper,'bracket_width_D_minus_Hcentres':upper-H,
          'primary_gate':(28-h)*L-tail-H,'zero_tail_gate':(28-h)*L-H,
          'display':{'H_centres':float(H),'D_830':float(upper),'primary_gate':float((28-h)*L-tail-H)}}
 best=primary['value']
 decision='strict_fixed_method_exclusion' if best<0 else ('nonpositive_fixed_method_exclusion' if best==0 else 'not_excluded')
 chosen=sorted(set(s['label'] for s in envelope))
 witnesses=[]
 for c in chosen:
  roots=tuple(((0,1,4) if i==0 else (0,3))[s] for i,s in enumerate(c[1:]))
  witnesses.append({'centre_index':c,'ternary_leaf_mod9':LEAVES[c[0]],
      'nonternary_roots_modq':roots,'higher_digits':'all zero','complete_mean':laws[c].mean,
      'unique_optimum_claimed':False})
 def compact_gate(result):
  return {'supremum_on_0_le_h_lt28':result['value'],'closed_domain_maximum':result['value'],
          'selected_maximizing_threshold':result['threshold'],
          'attained_in_half_open_domain':result['threshold']<28,
          'display':float(result['value'])}
 best_values={c:engine.hinge(law,primary['threshold']) for c,law in laws.items()}
 best_value=max(best_values.values())
 selected_at_best=min(c for c,v in best_values.items() if v==best_value)
 witness_curve=curves[selected_at_best]
 witness_gate=tuple((28-h)*L-tail-witness_curve[h] for h in range(29))
 witness_best=max(range(29),key=lambda h:(witness_gate[h],-h))
 single_witness={'centre':selected_at_best,'complete_mean':laws[selected_at_best].mean,
    'integer_hinges_0_to28':witness_curve,'maximum_primary_gate':witness_gate[witness_best],
    'maximum_zero_tail_gate':witness_gate[witness_best]+tail,'maximizing_threshold':witness_best,
    'integer_endpoints_suffice':'This is one fixed centre; its gate is affine on each unit interval.',
    'same_maximum_as_centre_menu':witness_gate[witness_best]==primary['value']}
 check(single_witness['same_maximum_as_centre_menu'],'selected one-centre obstruction matches menu maximum')
 check(single_witness['maximum_primary_gate']<F(-7,100),'strict primary fixed-method gap')
 check(single_witness['maximum_zero_tail_gate']<F(-7,250),'strict zero-tail fixed-method gap')
 transient=None
 if args.transient_laws:
  transient=write(args.transient_laws,{'schema':'e7-common-centre-transient-laws-v1',
      'bindings':bindings,'mass':M,'low_atom_indices':[1,27],
      'laws':[{'centre':c,'mean':law.mean,'atoms1to27':law.atoms[1:]} for c,law in laws.items()]})
 output={'schema':'e7-common-centre-result-v1','status':'pass','bindings':bindings,
  'scope':'Fixed831 infinite pure-comb raw retained nu_u, unchanged827 C/u/w; not a finite original covering family or a survivor-restricted lower witness.',
  'phases':'One common compatible p-adic centre supplies every distinct numerical-label phase, including unit.',
  'normalization':'raw nu_u; inherited M,L,tail unchanged; no extra leaf-weight or colour-probability factor',
  'inherited_exact':{'M':M,'L':L,'tail':tail},'centres':960,'complete_means_carried_separately':True,
  'positive_low_atom_indices':[1,27],'envelope':envelope,'envelope_witnesses':witnesses,
  'grid':[comparison(F(h)) for h in range(29)],'h16':comparison(F(16)),
  'best_primary':comparison(primary['threshold']),'best_zero_tail':comparison(zero_tail['threshold']),
  'primary_gate':compact_gate(primary),'zero_tail_algebraic_diagnostic':compact_gate(zero_tail),
  'decision':decision,'bracket':'H_centres <= H_all_layouts <= D_830; D_830-H_centres is bracket width, not proven true slack.',
  'restrictions':['The960 menu is complete for common centres under the specified clean-source relocation argument, not for independent per-label phases.',
      'No384-type maximum-mean layout was evaluated.',
      'A finite-query witness under this comb source does not establish a finite-original-source witness.',
      'No unrestricted Erdos7 or Lean claim.'],
  'single_centre_obstruction':single_witness,
  'finite_query_witness':finite_query_tail_certificate(),'statistics':stats}
 if args.write_result:write(args.out,output)
 else:compare_results(json.loads(args.out.read_text()),encode(output))
 signal.alarm(0)
 print(json.dumps(encode({'status':'pass','decision':decision,'primary_gate':output['primary_gate'],
      'zero_tail':output['zero_tail_algebraic_diagnostic'],'h16':output['h16'],
      'envelope_segments':len(envelope),'witness_centres':len(witnesses),
      'tensor_seconds':tensor_seconds,'elapsed_seconds':perf_counter()-started,'checks':checks,
      'result_action':'written' if args.write_result else 'compared',
      'transient_laws_binding':transient}),indent=2),flush=True)

if __name__=='__main__':main()
