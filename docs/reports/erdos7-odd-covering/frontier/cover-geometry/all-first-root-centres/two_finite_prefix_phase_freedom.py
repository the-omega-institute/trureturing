"""Exact finite-prefix phase freedom from the all-first-root survivor bound.

Report490. The ordinary set comparison keeps every original full numerical
label and bounds the discrepancy of two families on one common Haar carrier.
This consumer checks the inherited bound, exact cylinder charge and tail.
It does not rerun report489's pair certificates or claim new Lean verification.
"""
from fractions import Fraction as F
from math import factorial,prod
from pathlib import Path
import argparse,hashlib,json

PRIMES=(3,5,7,11,13,17,19)
HEIGHTS=(23,16,13,11,10,9,9)
SOURCE='all_first_root_centres.json'
SOURCE_SHA='f0152794e624e017ad9e1fc49be33c405992ae2e402df2661c1e89579ecd5680'

def need(ok,message):
 if not ok:raise ValueError(message)

def verify(input_dir):
 raw=(input_dir/SOURCE).read_bytes()
 need(hashlib.sha256(raw).hexdigest()==SOURCE_SHA,'inherited exact result identity')
 source=json.loads(raw)
 a=(F(source['source_mass_lower'])-F(source['uniform_exact_upper']))/49896
 need(a==F(source['uniform_original_Haar_lower']),'inherited same-source Haar conversion')
 need(F(1,400000)>a>F(11,10000000000),'all source types share the stronger bound')
 need(len(PRIMES)==len(HEIGHTS)==7 and all(h>=1 for h in HEIGHTS),'positive prefix heights')
 charges=[F(2,p**h) for p,h in zip(PRIMES,HEIGHTS)]
 union_upper=sum(charges);delta=1-prod(1-c for c in charges)
 need(0<delta<=union_upper<F(1,10000000000),'small common cylinder discrepancy')
 remaining=a-delta
 need(remaining>F(1,1000000000),'arbitrary deeper phases retain the original Haar floor')
 B=100000000000;ell=23;c=F(2*ell*ell+1,2*ell*ell-1)
 need(B>=286 and ell>=4 and 3**ell<=B,'Chapter33 tail applicability')
 M2=prod(F(p*(p+1),(p-1)**2) for p in PRIMES+(23,29))
 series=sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 loss=M2*c**7/F(B)*F(B,B-3)**2*series
 tail=F(1,1000000000)-loss
 inherited=source['unrestricted_large_prime_tail']
 need(loss==F(inherited['loss_upper']) and tail==F(inherited['remaining_distorted_lower']),
      'same Haar seed floor and tail calculation')
 need(tail>F(1,2000000000),'positive unrestricted large-prime continuation')
 return {'scope':__doc__,'source_inputs':{SOURCE:SOURCE_SHA},
         'primes':list(PRIMES),'prefix_heights':list(HEIGHTS),
         'prefix_modulus':str(prod(p**h for p,h in zip(PRIMES,HEIGHTS))),
         'coordinate_cylinder_charges':[str(v) for v in charges],
         'inherited_uniform_Haar_lower':str(a),
         'union_charge_upper':str(union_upper),'union_charge_upper_float':float(union_upper),
         'exact_discrepancy_charge':str(delta),'exact_discrepancy_charge_float':float(delta),
         'original_Haar_lower':str(remaining),'original_Haar_lower_float':float(remaining),
         'original_Haar_strict_lower':'1/1000000000',
         'large_prime_tail':{'B':B,'ell':ell,'c':str(c),'M2':str(M2),
                             'loss_upper':str(loss),'distorted_lower':str(tail),
                             'distorted_lower_float':float(tail),
                             'distorted_strict_lower':'1/2000000000'},
         'prior_certificates_rerun':False,'Lean_rerun':False,
         'boundary':'Every original later full label fixes one of two finite old prefixes; all deeper old digits and new-coordinate phases are arbitrary. The centres differ at all seven first digits. The common-carrier set identity, report489 theorem and Chapter33 analytic continuation are ordinary inputs. Arbitrary shallow phases and unrestricted Erdos7 are not settled.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--output',type=Path);args=ap.parse_args();result=verify(args.input_dir)
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained result differs')
 print(json.dumps({k:result[k] for k in ('prefix_heights','exact_discrepancy_charge_float',
       'original_Haar_lower_float','original_Haar_strict_lower')},indent=2))

if __name__=='__main__':main()
