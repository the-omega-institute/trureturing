#!/usr/bin/env python3
"""Exact same-law consumers of the shared-cell square observation.

The SQ proof supplies the improved AP13 observations. This program
reuses the complete SP scalar-cost formulas and KC finite-core errors.
All original tails remain paid. No unrestricted or Lean claim is made.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import runpy

HERE=Path(__file__).resolve().parent
PINS={
 'certificates/killed_core_continuity_certificate.json':'0ca9ec61d1d1104b6bf84d7daa2b6e3fd026aa44363e392a2fdbf41a957ffcbe',
 'certificates/shared_cell_square_certificate.json':'df746d03d242d44a1cfe85d6ee6d283b3495af155320e970140f69912479fe0d',
 'certificates/supported13_hinges_certificate.json':'d484812af981dc55ee0c766f69dcdb0eb3301c18d1f0886b00e9cc726d514e7f',
 'verify_supported13_hinges.py':'f49eae70cb59162d27d18f91d7cc47a7cc61419bb885f976f905753061b2d2d7',
 'verify_pg1_scalar_schedule.py':'9f7be4b430abbf631a0958e96eaf860f56948d680078fe842c90c308e663289b',
}

def require(ok,message):
 if not ok:raise ArithmeticError(message)

def unique(pairs):
 out={}
 for k,v in pairs:
  require(k not in out,'duplicate JSON key: '+k);out[k]=v
 return out

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--source-directory',type=Path,default=HERE)
 parser.add_argument('--certificate',type=Path,default=HERE/'certificates/shared_square_continuation_certificate.json')
 parser.add_argument('--write',action='store_true')
 args=parser.parse_args();sources={}
 for name,pin in PINS.items():
  raw=read_artifact_bytes(args.source_directory/name)
  require(sha256(raw).hexdigest()==pin,'source SHA-256: '+name)
  if name.endswith('.json'):sources[name]=json.loads(raw,object_pairs_hook=unique)
 sq=sources['certificates/shared_cell_square_certificate.json']
 sp=sources['certificates/supported13_hinges_certificate.json']
 profile=sp['supported13_profile']
 require(F(profile['survival_lower'])==F(sq['same_actual_law_inputs']['rho13']),
         'same actual AP(4,6) normalization')
 require(F(profile['source_square'])==F(sq['same_actual_law_inputs']['previous_Gamma13']),
         'same previous AP13 square observation')
 G=F(next(r for r in sq['targets'] if r['tau']==16)['shift_square'])
 T81=F(next(r for r in sq['targets'] if r['tau']==81)['supported_hinge'])
 require(G<F(profile['source_square']),'strict source-square improvement')
 old={int(h):F(v) for h,v in profile['hinge_upper'].items()}
 hinges={h:min(v,(G-1)*F(h,4*h*h-1)) for h,v in old.items()}
 mean=min(F(profile['mean_upper']),1+hinges[1])
 helper=runpy.run_path(str(args.source_directory/'verify_pg1_scalar_schedule.py'))
 transfer=runpy.run_path(str(args.source_directory/'verify_supported13_hinges.py'))
 row=transfer['schedule_row']
 single=[row([(17,t)],hinges,mean,G,helper) for t in range(1,16)]
 restart=[row([(17,a),(19,b)],hinges,mean,G,helper)
          for a,b in product(range(1,16),range(1,18))]
 best17=min((r for r in single if r['Gamma_upper'] is not None),key=lambda r:r['Gamma_upper'])
 best19=min((r for r in restart if r['Gamma_upper'] is not None),key=lambda r:r['Gamma_upper'])
 defect=min(restart,key=lambda r:r['residual_at483'])
 require(best17['schedule']==[(17,8)] and best17['Gamma_upper']==F(
    9720067404606638015016317,25298087377147529307792),'same single17 bound')
 require(best19['schedule']==[(17,8),(19,8)] and best19['Gamma_upper']==F(
    1947596368885525589065961707,873442090069958182244328),'same physical17/19 continuation')
 require(len(restart)==255 and all(r['residual_at483']>0 for r in restart),
         'all stated255 W483 scalar defects remain positive')
 require(defect['schedule']==[(17,6),(19,8)],'least-defect integer schedule')
 budgets=[]
 kc=sources['certificates/killed_core_continuity_certificate.json']
 for box,current,safe,threshold in [
   ([20]*7,[8,8],F(667,1000000),F(299660,1000)),
   ([17,10,8,7,6,6,6],[6,6],F(263,1000),F(299398,1000))]:
  prior=next(r for r in kc['rows'] if [h for p,h in r['box']]==box and r['current']==current)
  require(F(prior['safe_allowance'])==safe and F(prior['total'])<safe,
          'same complete KC error allowance')
  available=403-T81-safe
  require(threshold<available,'strict finite killed-frontier budget')
  budgets.append(dict(box=box,current=current,previous_KC_safe_error=safe,
    tau=81,W=403,source_square_hinge=T81,available_frontier=available,
    sufficient_frontier_bound=threshold,slack=available-threshold))
 result=transfer['encode'](dict(schema='erdos7-shared-square-continuation-v1',source_sha256=PINS,
  source=dict(Gamma13=G,T81=T81,mean=mean,hinges=hinges),
  single17=dict(outcomes=single,best=best17),
  restart17_19=dict(outcomes=restart,best=best19,least_W483_defect=defect,
     finite_sufficient_count=sum(r['Gamma_upper'] is not None for r in restart)),
  killed_frontier_budgets=budgets,
  scope='Same supported AP13 input throughout. Single17 conditioned output is separate from the two-step physical17/19 chain. Complete auxiliary tails are those of the pinned SP helper; no PG1 loader is invoked. KC safe errors remain valid with the unchanged actual law.',
  open_mathematical_obligations='The two finite killed-frontier inequalities are unproved. The255 positive W483 defects concern only the fixed scalar upper functional, not a lower bound on actual squares. Unrestricted Erdos7 and later-prime continuation remain open.'))
 if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
 else:require(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)==result,'entire certificate equality')
 print('PASS same-law single17 '+str(float(best17['Gamma_upper']))+
  '; two-step19 '+str(float(best19['Gamma_upper']))+
  '; least W483 defect '+str(float(defect['residual_at483']))+
  '; finite frontier targets '+str([float(r['sufficient_frontier_bound']) for r in budgets]))

if __name__=='__main__':main()
