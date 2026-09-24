#!/usr/bin/env python3
"""Exact subset-partition optimizer for arbitrary selected 3p/9p blocks.
All root/leaf partitions are dynamic-programming transitions, not original
phase or numerical-label enumeration.  The actual-supremum bridge is NB7
of report542.  A hard cap bounds the cumulative number of stored DP states.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import argparse,json,resource,time,hashlib,sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
parser.add_argument('--max-states',type=int,default=100000)
args=parser.parse_args()
Q=(5,7,11,13,17,19);n=len(Q);M=1<<n;ALL=M-1
D=prod(p*(p-2) for p in Q)
subsets=[tuple(s for s in range(M) if s&m==s) for m in range(M)]
started=time.perf_counter();stages=[];state_count=0;candidate_count=0
arrays={};choices={};metadata={}
def rss_bytes():
 value=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
 return value if sys.platform=='darwin' else value*1024
def reserve(name):
 global state_count
 requested=state_count+M*M
 if requested>args.max_states:
  stop={'complete':False,'reason':'state_limit','before_table':name,'stored_states':state_count,'requested_states':requested,'max_states':args.max_states,'stages':stages}
  args.output.write_text(json.dumps(stop,indent=2)+'\n')
  raise SystemExit(2)
 state_count=requested
 return time.perf_counter()
def finish(name,began,transitions):
 global candidate_count
 candidate_count+=transitions
 item={'table':name,'states':M*M,'cumulative_states':state_count,'candidate_transitions':transitions,'elapsed_seconds':time.perf_counter()-began,'peak_rss_bytes':rss_bytes()}
 stages.append(item)
 print(json.dumps(item),flush=True)

began=reserve('leaf_kernel')
kernel=[[prod(p*(p-2)-(p-1)*(((A>>i)&1)+((B>>i)&1)) for i,p in enumerate(Q)) for B in range(M)] for A in range(M)]
arrays['leaf_kernel']=kernel
finish('leaf_kernel',began,0)
began=reserve('normal1')
arrays['normal1']=[[2*kernel[A][B] for B in range(M)] for A in range(M)]
finish('normal1',began,0)

# A is the set of parent roles assigned to this root; B is the set of child
# roles assigned somewhere within it.  A and B MAY overlap.
def leaf_table(name,s,anchored):
 began=reserve(name);previous=arrays['normal'+str(s-1)]
 ans=[[0]*M for _ in range(M)];arg=[[0]*M for _ in range(M)]
 weight=1 if anchored else 2
 count=0
 for A in range(M):
  row=kernel[A];old=previous[A]
  for B in range(M):
   best=None;bestC=0
   for C in subsets[B]:
    value=weight*row[C]+old[B^C];count+=1
    if best is None or value<best:best=value;bestC=C
   ans[A][B]=best;arg[A][B]=bestC
 arrays[name]=ans;choices[name]=arg;metadata[name]=(s,anchored)
 finish(name,began,count)
leaf_table('normal2',2,False)
leaf_table('normal3',3,False)
leaf_table('anchor2',2,True)
leaf_table('anchor3',3,True)

# Append an ordinary root.  Parent-role masks and child-role masks are
# partitioned separately; an identity may have both roles in different roots.
def root_table(name,left,right):
 began=reserve(name);X=arrays[left];Y=arrays[right]
 ans=[[0]*M for _ in range(M)];arg=[[0]*M for _ in range(M)];count=0
 for A in range(M):
  for B in range(M):
   best=None;bestCD=0
   for C in subsets[A]:
    xrow=X[A^C];yrow=Y[C]
    for E in subsets[B]:
     value=xrow[B^E]+yrow[E];count+=1
     if best is None or value<best:best=value;bestCD=(C<<n)|E
   ans[A][B]=best;arg[A][B]=bestCD
 arrays[name]=ans;choices[name]=arg;metadata[name]=(left,right)
 finish(name,began,count)
root_table('N5_anchor2','anchor2','normal3')
root_table('N8_anchor2','N5_anchor2','normal3')
root_table('N6_anchor3','anchor3','normal3')
root_table('N9_anchor3','N6_anchor3','normal3')
root_table('N5_anchor3','anchor3','normal2')
root_table('N8_anchor3','N5_anchor3','normal3')

case_info={'N5_anchor2':5,'N8_anchor2':8,'N6_anchor3':6,'N9_anchor3':9,'N5_anchor3':5,'N8_anchor3':8}
def supremum(case,A,B):return 1-F(arrays[case][A][B],D*(2*case_info[case]-1))
# Root/leaf backtracking returns literal roles for each surviving root.
def leaves(name,A,B):
 if name=='normal1':return [B]
 s,anchored=metadata[name];C=choices[name][A][B]
 return [C]+leaves('normal'+str(s-1),A,B^C)
def layout(name,A,B):
 if name in ('anchor2','anchor3','normal2','normal3'):
  return [{'parent_mask':A,'child_masks':leaves(name,A,B),'anchor_leaf':0 if name.startswith('anchor') else None}]
 left,right=metadata[name];CD=choices[name][A][B];C=CD>>n;E=CD&ALL
 return layout(left,A^C,B^E)+layout(right,C,E)
checks={}
def req(k,b):
 checks[k]=bool(b)
 if not b:raise ValueError(k)
req('all_DP_states_below_cap',state_count==49152<=args.max_states)
req('transition_count_matches_closed_form',candidate_count==4*(2**n)*(3**n)+6*(3**(2*n)))
# Check each endpoint's actual incidence vector, including BOTH roles on a p
# and a unique deficient anchor.  These are certificate checks, not searches.
witnesses={}
for case,N in case_info.items():
 rows=layout(case,ALL,ALL);seenA=0;seenB=0;scaled=0;cellnum=[];anchor_num=None
 for row in rows:
  A=row['parent_mask'];req(case+'_parent_disjoint_'+str(seenA),not(A&seenA));seenA|=A
  for j,B in enumerate(row['child_masks']):
   req(case+'_child_disjoint_'+str(seenB),not(B&seenB));seenB|=B
   k=prod(p*(p-2)-(p-1)*(((A>>i)&1)+((B>>i)&1)) for i,p in enumerate(Q))
   anchored=j==row['anchor_leaf'];scaled+=(1 if anchored else 2)*k
   cellnum.append(k)
   if anchored:anchor_num=k
 req(case+'_all_parent_and_child_roles_once',seenA==seenB==ALL)
 req(case+'_row_sizes_and_total_cells',sum(len(r['child_masks']) for r in rows)==N)
 req(case+'_witness_cost',scaled==arrays[case][ALL][ALL])
 anchor_size=len(next(r for r in rows if r['anchor_leaf'] is not None)['child_masks'])
 orbit_cells=[kernel[row['parent_mask']][B] for row in rows if len(row['child_masks'])==anchor_size for B in row['child_masks']]
 req(case+'_anchor_is_max_in_its_orbit',anchor_num==max(orbit_cells))
 req(case+'_linearized_branch_below_full_Phi',supremum(case,ALL,ALL)<=1-F(2*sum(cellnum)-max(cellnum),D*(2*N-1)))
 witnesses[case]={'rows':rows,'avoidance_numerators':cellnum,'common_denominator':D,'scaled_minimum':scaled,'fixed_anchor_linearized_response':str(supremum(case,ALL,ALL)),'layout_full_Phi':str(1-F(2*sum(cellnum)-max(cellnum),D*(2*N-1)))}
# Existing541 exact one-depth-star supremum, independently evaluated by its
# two-root bipartition formula, must agree for EVERY selected parent subset.
c=[F(p-1,p*(p-2)) for p in Q]
def union(mask):return 1-prod(1-c[i] for i in range(n) if mask>>i&1)
star_tests=0
for A in range(M):
 known=max(F(2,3)*union(C)+F(1,3)*union(A^C) for C in subsets[A])
 computed=max(supremum(case,A,0) for case in case_info)
 req('report541_all_subsets_'+str(A),computed==known);star_tests+=1
for i,p in enumerate(Q):
 bit=1<<i
 req('single_child_'+str(p),max(supremum(case,0,bit) for case in case_info)==F(2,9)*c[i])
 req('same_prime_both_roles_'+str(p),max(supremum(case,bit,bit) for case in case_info)==F(8,9)*c[i])
req('empty_block',all(supremum(case,0,0)==0 and arrays[case][0][0]==D*(2*N-1) for case,N in case_info.items()))
req('empty_leaf_kernel',kernel[0][0]==D)
req('empty_child_roles_retain_parent_response',all(arrays['normal3'][A][0]==6*kernel[A][0] and arrays['anchor2'][A][0]==3*kernel[A][0] for A in range(M)))
# The entire4096 selected-inventory table is naturally present, not produced
# by4096 independent runs.  Its all-mask maximum is another exact readout.
best_case=[[max(case_info,key=lambda case:supremum(case,A,B)) for B in range(M)] for A in range(M)]
full_case=best_case[ALL][ALL];full=supremum(full_case,ALL,ALL)
# Every naturally produced terminal is checked by a complete incidence
# certificate from the winning anchor orbit, independently of its recurrence.
terminal_certificate_count=0;N5_dominance_count=0
for A in range(M):
 for B in range(M):
  case=best_case[A][B];N=case_info[case];rows=layout(case,A,B)
  usedA=0;usedB=0;nums=[];scaled=0;anchor_num=None
  for row in rows:
   C=row['parent_mask']
   if usedA&C:raise ValueError('terminal duplicate parent role')
   usedA|=C
   for j,E in enumerate(row['child_masks']):
    if usedB&E:raise ValueError('terminal duplicate child role')
    usedB|=E
    # Direct literal incidences, multiplied across the six independent
    # outside coordinates.  No DP transition values enter this calculation.
    k=1
    for i,pprime in enumerate(Q):
     multiplicity=int(bool(C&(1<<i)))+int(bool(E&(1<<i)))
     k*=pprime*(pprime-2)-(pprime-1)*multiplicity
    nums.append(k)
    if j==row['anchor_leaf']:
     scaled+=k;anchor_num=k
    else:scaled+=2*k
  if usedA!=A or usedB!=B or len(nums)!=N:raise ValueError('terminal role allocation')
  if scaled!=arrays[case][A][B]:raise ValueError('terminal literal linear cost')
  if anchor_num!=max(nums):raise ValueError('globally best anchor is not largest avoidance')
  Phi=1-F(2*sum(nums)-max(nums),D*(2*N-1))
  if Phi!=supremum(case,A,B):raise ValueError('terminal full Phi mismatch')
  terminal_certificate_count+=1
  best5=max(supremum('N5_anchor2',A,B),supremum('N5_anchor3',A,B))
  if best5!=Phi:raise ValueError('analytic five-cell dominance failed')
  N5_dominance_count+=1
req('every_selected_inventory_has_literal_optimum_certificate',terminal_certificate_count==M*M)
req('five_cell_mask_dominates_every_selected_inventory',N5_dominance_count==M*M)

result={'complete':True,'scope':'exact subset-partition DP for every selected I,K on six outside primes; sharp actual all-height block supremum via report542 NB7',
 'prime_order':Q,'mask_bits':'bit i selects prime_order[i]; first mask is3p parent role, second is9p child role',
 'common_denominator':D,'integer_normalization':'stored minimum W represents sum_j 2*lambda_j*avoidance_numerator; supremum=1-W/[D*(2*N-1)]',
 'max_states':args.max_states,'state_count_scope':'objective scalar cells, excluding backpointer payload cells, Python containers, and output tables','stored_DP_states':state_count,'backpointer_payload_cells':len(choices)*M*M,'candidate_transitions':candidate_count,'stages':[{k:v for k,v in stage.items() if k not in ('elapsed_seconds','peak_rss_bytes')} for stage in stages],
 'cases':{case:{'allowed_cell_count':N,'scope':'fixed anchor root-size orbit; minimize across same-mask orbits before claiming full Phi optimum','minimum_integer_matrix':arrays[case],'full_block_witness':witnesses[case]} for case,N in case_info.items()},
 'all_mask_best_case_matrix':best_case,
 'full_twelve_slot_best_case':full_case,'full_twelve_slot_actual_supremum':str(full),'full_twelve_slot_decimal_display':float(full),
 'checks':checks,'passed_count':len(checks),'reused_single_depth_patterns_checked':star_tests,'literal_terminal_certificates_checked':terminal_certificate_count,'five_cell_dominance_terminal_checks':N5_dominance_count,
 'verification_arithmetic':'unbounded Python integers and exact fractions; timing and RSS are emitted only to stdout'}
measured_stats={'total_elapsed_seconds':time.perf_counter()-started,'peak_rss_bytes':rss_bytes()}
args.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({'complete':True,'states':state_count,'candidate_transitions':candidate_count,'passed_count':len(checks),'full_case':full_case,'full_supremum':str(full),'full_display':float(full),'seconds':measured_stats['total_elapsed_seconds'],'peak_rss_bytes':measured_stats['peak_rss_bytes'],'result':str(args.output),'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()},indent=2))
