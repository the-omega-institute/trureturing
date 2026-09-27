#!/usr/bin/env python3
"""Complete J selected heads with one raw source and marked actual deletion."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from types import SimpleNamespace, MethodType
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_face_joint_selected_heads.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_coupled_seven_heads.py': '78b6846a4eaa01ed568eb96e8c49dca67d0a19df094bc1e28ba5214100dc70a0', 'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json': 'ecdd57e17e466435943a0fff4d63da9841e72ef2631651d5ecc451dcac586449', 'frontier/source-budgets/joint_selected_source_comparison.py': '849ecfdffec509678ace0ab6e059450a72959a44641a46715bcb489a5d376db8', 'frontier/retained-transport/retained_deletion_heavy_comparison.py': '553c281d5de5a9bcd9098ea933f6cccf046b587132e6fa49ec4aa8b44b4ec86f', 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8', 'profile-notes/193-256/211-all-four-selected-labels-can-be-retained-above-the-first-hinge.md': 'a57b7a5e6d531412b5cebc11d42c1ce2617cc8d3f19651887447b30fe0f13781', 'profile-notes/193-256/219-one-late-source-split-controls-complete-saturated-j-heads.md': 'd0f78950c8ca3040b2a90c5b5d470655cd53e68f39b54d531f793915490ff73d', 'profile-notes/193-256/222-deep-five-deletion-retains-the-selected-observation-masks.md': '75f2e13689ba09637307ef2eea60d055d8bd4312dd2ebe7062d6fef8664f123c'}

def require(ok,message):
    if not ok: raise ValueError(message)

def module(name,path):
    s=importlib.util.spec_from_file_location(name,path)
    require(s is not None and s.loader is not None,'Loadable original source')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {str(k):encode(x)for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [encode(x)for x in v]
    return v

def make_lp(j,rawmod,ret):
 p,a,e,w=j.source_tables(j.LO)
 class Bridge:
  ROOT=j.ROOT
  GROUPS=[list(range(5)),list(range(5,10)),list(range(10,25))]
  GROUP_MASSES=[F(1,24),F(1,12),F(1,8)]
  @staticmethod
  def source_tables(_):return p,a,w,e
 raw=rawmod.RawSelectedLP(Bridge())
 lp=SimpleNamespace(nvars=876,rows=[dict(r)for r in raw.rows],rhs=list(raw.rhs),equalities=[dict(r)for r in raw.equalities],erhs=[F(1)]*4,lambda_groups=raw.lambda_groups)
 lp.rows[17][875]=j.HI-j.LO
 lp.rows[22][875]=-(j.HI-j.LO)
 def add(row,rhs):lp.rows.append(row);lp.rhs.append(rhs);return len(lp.rows)-1
 lp.theta_upper=add({875:F(1)},F(1));lp.y_link=[]
 flatw=[v for r in w for v in r]
 for cell in range(25):
  for mask in range(16):
   k=16*cell+mask;lp.y_link.append(add({425+k:F(1),k:-flatw[cell]},F(0)))
 lp.equalities +=[{425+k:F(1)for k in range(400)},{k:F(1)for k in range(400)}];lp.erhs +=[F(3,20),F(1,4)]
 for bit,cap in enumerate((F(13,750),F(11,540),F(1,75),F(11,1620))):
  add({425+16*cell+mask:F(1)for cell in range(25)for mask in range(16)if mask>>bit&1},cap)
 lp.e3_zero={}
 for cell in range(25):
  row={825+cell:F(1),850+cell:F(1)}
  for mask in range(16):row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
  add(row,F(0))
  if cell//5>=2:lp.e3_zero[825+cell]=add({825+cell:F(1)},F(0))
 for s in range(5):lp.equalities.append({825+s:F(1),830+s:F(1)});lp.erhs.append(j.QSLOTS[s]/90)
 for c in range(5):lp.equalities.append({850+5*c+s:F(1)for s in range(5)});lp.erhs.append(j.ETA[c]*(1+int(c>=2))/100)
 # Necessary selected-event residuals from the same E5/E3 deletions.
 for bit,div in ((1,3),(3,9)):
  for c in range(1,5):
   row={lp.lambda_groups[bit][c]:j.ETA[c]*(1+int(c>=2))/(100*div)}
   for slot in range(5):
    cell=5*c+slot
    for mask in range(16):
     if mask>>bit&1:row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
   add(row,F(0))
 for bit in (0,2):
  row={lp.lambda_groups[bit][slot]:F(1,2250)for slot in (1,2,4)}
  for cell in range(25):
   for mask in range(16):
    if mask>>bit&1:row[16*cell+mask]=-flatw[cell];row[425+16*cell+mask]=F(1)
  add(row,F(0))
 lp.columns=[[]for _ in range(lp.nvars)];lp.eqcolumns=[[]for _ in range(lp.nvars)]
 for i,r in enumerate(lp.rows):
  for k,v in r.items():lp.columns[k].append((i,v))
 for i,r in enumerate(lp.equalities):
  for k,v in r.items():lp.eqcolumns[k].append((i,v))
 lp.check_dual=MethodType(ret.RetainedDeletionLP.check_dual,lp)
 require(len(lp.rows)==587 and len(lp.equalities)==16 and len(lp.columns)==876,
         'The complete J model has876 nonnegative variables,587 inequalities and16 equalities')
 require(raw.nvars==425 and len(raw.rows)==132 and len(raw.equalities)==4,
         'The original raw selected model supplies all profiles and intersections')
 require(lp.rows[17][875]==F(1,270) and lp.rows[22][875]==-F(1,270),
         'The two common late-split caps have opposite signed movement')
 require(all(0<=k<876 and isinstance(v,F) for row in lp.rows+lp.equalities for k,v in row.items()),
         'Every model coefficient is exact and every column is included')
 lp.raw_specification=raw.specification()
 return lp

def objective(j,head,coeffs,layout,projection):
 B=head.bridge.head_load(layout);r,s,c63,r105,s105=projection
 extras=[int(j.ROOT[c]==r)+int(k==s)+int(c==c63)+int(j.ROOT[c]==r105 and k==s105)for c,k in product(range(5),repeat=2)]
 raw=[];sur=[]
 for i,b in enumerate(B):
  for mask in range(16):
   raw.append(sum(a*head.bridge.seven_increment(t,b+(mask.bit_count()if t>=2 else 0),extras[i])for t,a in coeffs.items()))
   sur.append(sum(a*max(b+(mask.bit_count()if t>=2 else 0)-t,0)for t,a in coeffs.items()))
 const=sum(a*((j.REMAINDERS[0]if t==1 else j.REMAINDERS[4])+j.Z4)for t,a in coeffs.items())
 return raw+[F(0)]*25+sur+[F(0)]*51,const


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique JSON key: '+key)
        result[key] = value
    return result


def model_specification(lp, j):
    body = encode([lp.rows, lp.rhs, lp.equalities, lp.erhs])
    return encode({'variables': lp.nvars, 'raw_mass_variables': 400,
        'projection_mixture_variables': 25, 'survivor_variables': 400,
        'coarse_deletion_variables': 50, 'normalized_late_variables': 1,
        'inequalities': len(lp.rows), 'equalities': len(lp.equalities),
        'raw_model': lp.raw_specification, 'late_split_interval': [j.LO, j.HI],
        'selected_moduli': [25, 27, 75, 81],
        'selected_survivor_caps': [F(13,750), F(11,540), F(1,75), F(11,1620)],
        'actual_source_mass': F(1,4), 'actual_survivor_mass': F(3,20),
        'deep3_slot_marginals': [q/90 for q in j.QSLOTS],
        'deep5_cell_marginals': [a*(1+int(c>=2))/100 for c,a in enumerate(j.ETA)],
        'marked_residual_rows': list(range(len(lp.rows)-10, len(lp.rows))),
        'null_event_projection_conventions': {'25': 'slot P', '75': 'root0,slot P',
                                             '27': 'cell0', '81': 'cell0'},
        'rows_sha256': sha256(json.dumps(body, sort_keys=True, separators=(',',':')).encode()).hexdigest()})


class JointSelectedJHead:
    def __init__(self, base, j, bank=None, proposer=None):
        self.j = j
        self.head = j.SaturatedJCoupledSevenHead(base)
        raw = module('j_joint_raw', base/'frontier/source-budgets/joint_selected_source_comparison.py')
        retained = module('j_joint_retained', base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
        self.lp = make_lp(j, raw, retained)
        self.specification = model_specification(self.lp, j)
        self.bank = {} if bank is None else bank
        self.proposer = proposer
        self.used, self.verified = set(), {}

    def dual_upper(self, coefficients, layout, projection):
        obj, constant = objective(self.j, self.head, coefficients, layout, projection)
        require(len(obj)==876 and min(obj)>=0 and all(v==0 for v in obj[400:425]+obj[825:]),
                'Every raw and survivor objective term is included; auxiliary columns cost zero')
        key = sha256(json.dumps([self.specification['rows_sha256'], encode(obj)],
                                separators=(',',':')).encode()).hexdigest()
        if key not in self.verified:
            if key not in self.bank:
                require(self.proposer is not None, 'Missing feasible rational J dual '+key)
                self.bank[key] = self.proposer(self.lp, obj)
            self.verified[key] = self.lp.check_dual(obj, self.bank[key])
        self.used.add(key)
        return self.verified[key]+constant, key, constant

    def scan(self, row):
        j, head = self.j, self.head
        coefficients = {int(t):F(v) for t,v in row['scan']['coefficients'].items()}
        prepared = head.prepare(coefficients)
        scale = prepared['factor']/j.TOTAL
        independent_checks = head.check_compiler(prepared)
        original = row['scan']['maximizing_witness']
        seed_layout = tuple(original['layout'])
        seed_projection = tuple(original[k] for k in
            ('seven21_root','seven35_slot','seven63_cell','seven105_root','seven105_slot'))
        digest = sha256()
        counts = {'two_projection_branches':0, 'two_bounded':0,
                  'four_projection_branches':0, 'four_bounded':0,
                  'joint_dual_branches':0, 'strict_affine_crossings':0}
        used_before = set(self.used)
        start = perf_counter()

        def old_bounds(layout, projection):
            B = head.bridge.head_load(layout)
            correction = head.correction(prepared, B)
            r,s,c,rr,ss = projection
            extra = tuple(int(j.ROOT[a]==r)+int(b==s) for a,b in product(range(5),repeat=2))
            first = tuple(v+int(a==c)+int(j.ROOT[a]==rr and b==ss)
                          for v,(a,b) in zip(extra,product(range(5),repeat=2)))
            two = head.objective(prepared,B,extra,correction,False)
            four = head.objective(prepared,B,first,correction,True)
            value,x,crossed = j.max_min_affines(two,four)
            return scale*value,x,crossed,two,four

        seed_old,x,crossed,two,four = old_bounds(seed_layout,seed_projection)
        seed_joint,key,constant = self.dual_upper(coefficients,seed_layout,seed_projection)
        best = min(seed_old,seed_joint)
        witness = {'layout':seed_layout,'projection21_35_63_105':seed_projection,
                   'old_complete_upper':seed_old,'old_maximizing_late_coordinate':x,
                   'joint_complete_upper':seed_joint,'adopted_complete_upper':best,'dual_key':key,
                   'complete_tail_constant':constant}
        seed_record = dict(witness)
        require(best>=0,'Nonnegative complete seed bound')
        max_pruned_two = max_pruned_four = F(-1)
        for il,layout in enumerate(j.layouts()):
            B = head.bridge.head_load(layout)
            correction = head.correction(prepared,B)
            for r,s,extra in head.extras:
                two = head.objective(prepared,B,extra,correction,False)
                counts['two_projection_branches'] += 1
                two_upper = scale*max(two)
                if two_upper<=best:
                    counts['two_bounded'] += 1
                    max_pruned_two = max(max_pruned_two,two_upper)
                    digest.update(repr(('two',layout,r,s,two)).encode())
                    continue
                for c,rr,ss,added in head.added:
                    first = tuple(a+b for a,b in zip(extra,added))
                    four = head.objective(prepared,B,first,correction,True)
                    value,x,crossed = j.max_min_affines(two,four)
                    old_upper = scale*value
                    counts['four_projection_branches'] += 1
                    counts['strict_affine_crossings'] += int(crossed)
                    if old_upper<=best:
                        counts['four_bounded'] += 1
                        max_pruned_four = max(max_pruned_four,old_upper)
                        digest.update(repr(('four',layout,r,s,c,rr,ss,two,four)).encode())
                        continue
                    projection = (r,s,c,rr,ss)
                    joint,key,constant = self.dual_upper(coefficients,layout,projection)
                    adopted = min(old_upper,joint)
                    counts['joint_dual_branches'] += 1
                    digest.update(repr(('joint',layout,projection,two,four,key,str(joint))).encode())
                    if adopted>best:
                        best = adopted
                        witness = {'layout':layout,'projection21_35_63_105':projection,
                                   'old_complete_upper':old_upper,'old_maximizing_late_coordinate':x,
                                   'joint_complete_upper':joint,'adopted_complete_upper':adopted,
                                   'dual_key':key,'complete_tail_constant':constant}
            if il%2500==0:
                print('J joint '+str(row['index'])+': layouts='+str(il)+', LP branches='
                      +str(counts['joint_dual_branches'])+', seconds='+str(round(perf_counter()-start,2)),flush=True)
        require(counts['two_projection_branches']==125000
                and counts['four_projection_branches']==50*(125000-counts['two_bounded'])
                and counts['joint_dual_branches']+counts['four_bounded']==counts['four_projection_branches']
                and 50*counts['two_bounded']+counts['four_projection_branches']==6250000
                and max_pruned_two<=best and max_pruned_four<=best,
                'All6250000 containing choices are included by full evaluation or valid uniform pruning')
        old,x,crossed,two,four = old_bounds(witness['layout'],witness['projection21_35_63_105'])
        raw,key,constant = self.dual_upper(coefficients,witness['layout'],witness['projection21_35_63_105'])
        require(old==witness['old_complete_upper'] and raw==witness['joint_complete_upper']
                and key==witness['dual_key'] and min(old,raw)==best,
                'The maximizing certificate branch reconstructs exactly; no primal attainment is claimed')
        r,s,c,rr,ss = witness['projection21_35_63_105']
        for theta in (j.LO,j.HI,j.LO+(j.HI-j.LO)*x):
            old_pair = [head.rational_objective(coefficients,witness['layout'],p,theta)
                        for p in ((r,s,None,None,None),(r,s,c,rr,ss))]
            t = (theta-j.LO)/(j.HI-j.LO)
            require(old_pair==[scale*(v[0]+(v[1]-v[0])*t) for v in (two,four)],
                    'Independent unscaled maximizing-branch bounds at both endpoints and exact common crossing')
            independent_checks += 2
        return {'coefficients':coefficients,'complete_hinge_upper':best,
                'counts':counts,'covered_containing_choices':6250000,
                'seed':seed_record,'maximizing_certificate_branch':witness,
                'complete_tail_constant':constant,'independent_affine_checks':independent_checks,
                'maximum_two_pruned':max_pruned_two,'maximum_four_pruned':max_pruned_four,
                'new_distinct_duals':len(self.used-used_before),
                'all_branch_decisions_sha256':digest.hexdigest()}


def calculate(base, bank=None, proposer=None):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest()==PINS['certificate_io.py'],
            'Pinned canonical reader')
    io = module('j_joint_input',base/'certificate_io.py')
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json'),object_pairs_hook=unique)
    pins = dict(PINS)
    for path,pin in previous['source_sha256'].items():
        require(path not in pins or pins[path]==pin,'Consistent preceding J mathematical source '+path)
        pins[path] = pin
    for path,pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical input '+path)
    j = module('j_joint_original',base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    problem = JointSelectedJHead(base,j,bank,proposer)
    face = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_alignment.json'),object_pairs_hook=unique)
    geometry = j.geometry_checks(problem.head,face)
    require(encode(geometry)==previous['geometry'],'The identical complete219 actual J geometry')
    require([str(r['index']) for r in previous['results']]==['AP13','0','16'],
            'Exactly the three original independent targets')
    rows = []
    for original in previous['results']:
        scan = problem.scan(original)
        at_one = F(original['at_one'])
        value = at_one*F(3,20)+scan['complete_hinge_upper']
        prior = F(original['adopted_upper'])
        mean = at_one*F(3,20)+sum(scan['coefficients'].values())*F(49,100)
        require(at_one>=0 and value<prior<=mean,'Each complete new J bound strictly improves its original219 target')
        rows.append({'index':original['index'],'at_one':at_one,'scan':scan,
                     'complete_head_upper':value,'previous_adopted_upper':prior,
                     'complete_mean_only_upper':mean,'adopted_upper':min(value,prior,mean),
                     'improvement_over_previous':prior-min(value,prior,mean)})
        print('Complete J joint '+str(original['index'])+' <= '+str(float(value))
              +'; distinct duals='+str(scan['new_distinct_duals']),flush=True)
    require(problem.used==set(problem.bank),'Every retained dual is consumed and every requested dual is present')
    return encode({'schema':'erdos7-j-face-joint-selected-heads-v1','source_sha256':pins,
        'geometry':geometry,'source_mass':F(1,4),'survivor_mass':F(3,20),
        'complete_mean_upper':F(16,25),'hinge1_upper':F(49,100),
        'model':problem.specification,'results':rows,
        'rational_duals':{k:problem.bank[k] for k in sorted(problem.used)},
        'distinct_dual_count':len(problem.used),'rational_column_checks':876*len(problem.used),
        'total_containing_choices':sum(r['scan']['covered_containing_choices'] for r in rows),
        'scope':'Three complete original AP13/heavy0/heavy16 bounds on both saturated actual J faces. One common876-variable raw/source/survivor/deletion LP retains the whole theta interval, all independent selected25/27/75/81 profiles, all four CRT intersections, ten necessary marked-deletion inequalities and the complete exponent tails. Every target covers all6250000 original containing choices using219 complete affine pruning with both endpoints and any exact common-theta crossing. Every retained rational dual checks all876 columns. Null event projections remain25=P,75=(root0,P),27/81=cell0. No K forced27 rule or K numerical bound, actual LP attainment, off-face extension, complete52-cost/global comparison, Lean verification or unrestricted Erdos7 result is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest()==PINS['certificate_io.py'],
            'Pinned canonical reader')
    io = module('j_joint_check_io',args.base/'certificate_io.py')
    stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=unique)
    result = calculate(args.base,bank=stored['rational_duals'])
    require(result==stored,'Every rational joint-head certificate field recomputes exactly')
    print('PASS:3 complete J heads,18750000 containing choices,'+str(result['distinct_dual_count'])
          +' feasible rational duals and all complete tails.',flush=True)


if __name__=='__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
