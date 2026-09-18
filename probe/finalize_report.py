"""Write the probe's judgement data, without asserting repository admission."""
import json
from pathlib import Path

root=Path('probe')
judgement=[]
for theorem in ['PerrierProbe.result','PerrierNoEliminationMutant.result']:
 judgement.append({
  'theorem':theorem,
  'proof_shape':'bind-only',
  'frozen_deps':[],
  'escape_witness':'none; the preregistered induction-on-j elimination lemma is absent and unnecessary. No replacement content witness is asserted. The second theorem is a probe-only mutant, not proposed delivery surface.',
  'four_tests':{
   'i':'Fails: no such elimination declaration occurs in the elaborated closure. Main closure checked: 7,334 constants, zero D5 dependencies.',
   'ii':'Not established: no non-normalization fact is required. The actual calculation instantiates Fin.sum_univ_succ and Fin.sum_univ_castSucc, distributes sums, and normalizes the recurrence equations.',
   'iii':'The proposed general-j identity differs from the final two-formula conjunction, but no corresponding declaration was elaborated; no kernel definitional-inequality test is claimed.',
   'iv_mutant_compiled':True},
  'admission_basis':'open-problem-resolution'
 })
(root/'judgement.json').write_text(json.dumps(judgement,indent=2)+'\n')
fidelity={
 'verdict':'faithful quantified strengthening; no binder, exponent, shift, or domain defect found',
 'dimension':'Source k>=2 becomes d>=1 with k=d+1; d=0 is the explicitly preregistered extension.',
 'domain':'Arbitrary K [Field K] and m,a:Fin d->K include the source real initial values and integer recurrence parameters; no positivity or eigenvector assumption is needed for the recurrence implication.',
 'time_origin':'r n j equals source r_(j+1)^(n-1); r 0 is source time -1.',
 'initial_values':'r 0 0=1; r 0 j.succ=a j, matching source p.14.',
 'recurrence':'r(n+1,0)=r(n,last d); r(n+1,j.succ)=r(n,j.castSucc)+m(j)*r(n,last d), matching p.15.',
 'generating_function':'R r j=PowerSeries.mk(fun n=>r n j); the shift is explicit on pp.8 and 12 and extended contextually to general k as disclosed in #8627.',
 'D':'1-sum_j C(m j)*X^(d-j)-X^(d+1), matching reversed coefficients and degrees on p.15.',
 'P':'1+sum_j C(a j-m j)*X^(d-j), matching R_1 numerator on p.15.',
 'Q':'X^d+sum_j C(a j)*X^(d-1-j), matching R_k numerator on p.15.',
 'inverse':'D has constant coefficient 1; proved in Lean, including d=0.',
 'locator_correction':'The issue/brief says printed p.7 for the 2x2 shifted definition; it is on printed p.8. This does not change the preregistered mathematical statement.',
 'scope':'Only the two displayed rational formulas; the subsequent equation-(7) conjecture and classification question are excluded.'}
(root/'statement-fidelity.json').write_text(json.dumps(fidelity,indent=2)+'\n')
report=(root/'REPORT.md').read_text()
report+='''
## Judgement-form report

Verdict: **propose** — the complete preregistered conjunction and its witness-bypass mutant compile without sorry or new axioms, with only propext, Classical.choice, Quot.sound. This is a probe recommendation, not a freeze, admission, review consensus, or merge.

Both public test declarations (PerrierProbe.result and the probe-only PerrierNoEliminationMutant.result) have proof_shape **bind-only**, direct frozen dependencies **none**, escape_witness **none**, and admission_basis **open-problem-resolution** (issue #8627). Only the main result is proposed for delivery.

Four witness tests, applied to the preregistered induction-on-j elimination lemma:

1. In elaborated dependency closure: **fails**. No such declaration occurs; the complete main closure was traversed.
2. Not obtainable by upstream instantiation/projection/normalization: **not established**. Actual proof intermediates come from existing finite-sum boundary decompositions and normalization of the recurrence hypotheses. No non-normalization fact is claimed.
3. Not definitionally the conclusion: the proposed general-j statement differs from the final conjunction, but no such declaration was elaborated, so no kernel definitional-inequality result is claimed.
4. Live/necessary path: **fails**. The independently compiled witness-bypass mutant proves the same conjunction. iv_mutant_compiled = true.

The observation is a successful bind-only approach, not a different escape witness. There is therefore no retrospectively relabelled content witness. The issue already preregisters open-problem-resolution if the content-witness assessment fails.

Utility kind=none: the theorem quantifies over arbitrary dimension, field, parameters, and recurrence solutions. It is not bounded enumeration, a checker, numeric reduction, or a certified finite instance. The finite Python computations are probe evidence only.

### Boundaries and reasoning discipline

The reference frame is the literal shifted recurrence and the source formulas, fixed before computation. The known-good shapes are PowerSeries coefficient shifts and Fin's two decompositions of the same finite sum. 美不美: the matrix/charpoly route is structurally elegant but its searched APIs do not discharge these formulas; coordinate induction mirrors the source but introduces an unnecessary intermediate; weighted-sum cancellation is concise and fully instantiated from upstream identities. Aesthetic preference is not evidence: compilation, dependency traversal, and exact coefficient comparisons are the verified readings.

ASSUMED-UNVERIFIED: comprehensive novelty/open status outside the inspected source and bounded pinned-library/repository search. The issue's independent literature-search claims were read, not independently reproduced. In particular its named WSU 2023 dissertation gap remains unverified. General-k use of the earlier shifted R definition is a contextual interpretation disclosed in the preregistration, not an explicit repeated definition on p.15.

Depth-bound stop: complete main conjunction plus one successful witness-bypass mutant; no further claim about equation (7), classification of periodic continued fractions, or the unread dissertation. The dependency traversal bound was 100,000 constants and it completed at 7,334. No required CI gates, deposit, emission, preflight, PR, or other-seat review was run or claimed.

Visible inputs: this brief + GoalArtifact + issue #8627 + source PDF; inherited prior: repo-prior-exposed (CLAUDE.md/AGENTS.md). Pinned Mathlib and repository sources were read for the requested search; no other probe seat output was accessed or requested.
'''
(root/'REPORT.md').write_text(report)
