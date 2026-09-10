---
bibkey: pntplus2026mertens
authors: Harold G. Diamond and Janos Pintz
year: 2009
title: Oscillation of Mertens' product formula
doi: 10.5802/jtnb.687
claim: Mertens' third theorem (1874) is stated by Diamond and Pintz (2009), equation (1.1); the pinned PrimeNumberTheoremAnd Lean source formalizes this asymptotic with the standard axiom closure.
strata_touched:
  - D5/S3/Weil/Mertens/Estimates
  - D5/S3/Weil/Mertens/LogZeta
  - D5/S3/Weil/Mertens/Gamma
  - D5/S3/Weil/Mertens/Third
license: citation-only
triage: anchor
---

# Oscillation of Mertens' product formula

Harold G. Diamond and Janos Pintz, *Journal de Theorie des Nombres de Bordeaux*
21 (2009), no. 3, pp. 523-533. Mertens (1874); literature attestation via
Diamond and Pintz (2009), equation (1.1), p. 523:
`(product over primes p <= x of (1 - 1/p)) * log(x) -> exp(-gamma)`.
This is the classical asymptotic formalized by the pinned upstream Lean port
recorded below. The citation attests that formula; the port's exact error
bounds and Lean axiom closures are supported by the recorded code measurements,
not by this paper's separate oscillation theorem.

## DOI verification and route

On 2026-09-07, <https://doi.org/10.5802/jtnb.687> resolved with HTTP 200 to
<https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.687/>. The publisher's
metadata confirms the authors, title, publication year 2009, volume 21, issue 3,
pages 523-533 and DOI. Its linked PDF was opened and equation (1.1) checked
on printed page 523. The online publication date is 2010-03-22; the journal
volume and article are dated 2009.

Route A retains this single note at the address cited by the four frozen
modules' NOTICE comments. Their `anchors: []` fields and comments cannot be
edited in this repair. Reusing `apostol1976introduction` by deleting this note,
or moving the NOTICE out of L, would require changing those frozen links.
The existing Apostol DOI was independently resolved to its Springer book page;
it is not duplicated here. This note instead cites the distinct paper above.
The citation-only license metadata concerns that paper. The upstream port's
Apache-2.0 notice and complete license remain below with its measurements.

## Mertens III Compatibility Measurement

Provenance: codex-cli implementation seat `mertens3-0907/attempt-1`,
dispatched by the consensus-rnd runner. No additional skill or review seat was
used by this worker; all measurements below are this worker's direct readings.
This is a literature port for the user-selected third-tier Robin/Gronwall
research line, not a new mathematical result.

## Source and Route

- Repository: <https://github.com/kimihiro64/PrimeNumberTheoremAnd>.
- Immutable commit: `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`.
- File: `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`.
- The downloaded bytes equal the previous probe's `UpstreamMertens.lean`
  (`cmp`, exit 0). That probe recorded the AlexKontorovich repository name;
  both citations identify the same commit and source bytes in this reading.
- Reused `mertens-probe-0907/attempt-1/MertensCompat.lean`, its `runmake.mjs`,
  and its additive `probe.mk`. The normal root `lean` recipe is retained.
- Route `PrimeNumberTheoremAnd.EulerMaclaurin` to the existing
  `D5.S3.Weil.ZetaPntBase.EulerMaclaurin`; remove Architect blueprint metadata
  and one redundant `rfl`, as already done by the previous probe.

## Q1 Reading

Repository HEAD at measurement: `c32b86362c4bf8d27c07ffbfe23bca128f90b070`.
Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

Command: `make -f Makefile -f <attempt>/probe.mk lean PROBE=<attempt>/Q1.lean`.
Exit: 0. Wall time: 160.490721292 seconds, including the root project build.
The initial cache receipt reported both Mathlib and project layers warm;
this is not a cold-build timing or a prediction for CI.

The three task signatures were independently written as `example` types and
closed by the corresponding upstream constants, with no additional hypotheses.
All three type checks passed. The exact axiom output is:

```text
'Mertens.E₃.abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.E₃.bound''' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mertens.E₃.bound'''' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final quote in each line closes Lean's quoted declaration name.
There is no `sorryAx` or custom axiom in any of these three closures.
One deprecation warning names `Set.mem_setOf_eq`; it is not an analytic gap.

Artifacts: `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/mertens3-0907/attempt-1/`.
The exact source, signatures and build output are `Q1.lean`, `q1.make.log`,
`q1.source.lean` and `q1.receipt.json` in that directory.

## Repository Search

At the measured HEAD, `git grep -n -P '\b(Mertens|Gronwall|ChebyshevMertens)\b'
-- D5` found weak product estimates in `PrimeGaps/EulerProducts`, hypotheses
in `Weil/ZetaCore/Hypotheses`, and provenance in the Euler-Maclaurin port.
These are not the sharp product asymptotic. The same word-boundary feature
was checked by `git grep -l -P '\btheorem\b' -- 'D5/**/*.lean'`: 3613 files.
These are lexical search readings, not a proof of global nonexistence.

Q1 establishes compatibility of the external source. It does not by itself
freeze a repository theorem or establish the Gronwall upper envelope.

## Port Selection and Scope

Form A: source port. `Lean.parseImports'` recursively measured the routed
non-Mathlib closure: 2 files, 2557 lines. Of these, the 102-line Euler-Maclaurin
module is already frozen in D5; the external source is 1 file, 2455 lines.
Architect is metadata only and was removed by the previous successful port.
The dependency traversal stops at the pinned Mathlib boundary.

The three endpoints' elaborated constant dependency graph was then traversed
through both declaration types and proof values. `findDeclarationRanges?`
located 111 source declarations covering 1731 lines. Only these declarations
were selected, preserving proof bodies and source order. The result is four
modules: Estimates, LogZeta, Gamma and Third. The five private helpers used
across those boundaries are now public. One deprecated Set lemma name was
updated; the prior probe's redundant-rfl correction is retained.

This is a small, buildable import closure. Splitting at the analytic interfaces
keeps each module below the repository's 800-line hard limit. It introduces
no package dependency and no new analytic hypothesis. Import closure and
declaration-selection receipts are `closure.make.log`, `declaration-closure.json`
and `port-transform.json` in the attempt directory.

Final parsed closure after declaration pruning: 4 new files, 2014 lines
(Estimates 587, LogZeta 360, Gamma 699, Third 368). The Euler-Maclaurin
import is no longer required by this smaller declaration set and was removed.
The original routed whole-source Q1 measurement remains unchanged.
The four formal-unit modules plus this source/license note total 5 paths.
Canonical freezing adds four event files and four state files: the complete
change is 13 paths, equal to the user-supplied PR p75. These four modules form
one endpoint's proof closure; no unrelated theorem family is included.

`make lean` on the split port: exit 0, 35.4733835 seconds. After removing the
unused import: exit 0, 78.079721041 seconds. `PortCheck.lean` then independently
imported Third, rechecked all three exact task signatures and printed all three
standard axiom closures: make exit 0, 14.9107345 seconds. Its import parser
produced the final counts above. These are warm local timings including the
root build; upstream formatting warnings remain nonblocking.

Canonical `make lean-report` exited 0 in 335.633129708 seconds, with both
cache layers warm and `mode=full-fallback`. The report SHA-256 is
`c174d6f10e7cfeedd2ee67b1c85302185fc6035ca2f6766acee16833d28ebf99`.
`ledger-align` then exited 0 with
`selectors_considered=5 changed=0 added=4 unchanged=1 conflicts=0`.
The existing Euler-Maclaurin module was the unchanged selector used to limit
the command's scope; it is not an import of the final port. All eight generated
ledger paths belong to the four Mertens modules. No Gronwall atom is covered.

Before opening the PR, `origin/dev` at
`03b70412c96c6c35768a194dfe1f865b93c59596` was searched again using the same
word-boundary query. It added only a Robin padding comment to the earlier
nearby hits; no sharp Mertens III declaration was found in that searched scope.
The matching-feature positive control returned 3617 D5 Lean files.
`git merge-tree --write-tree origin/dev HEAD` exited 0; the changed-path
intersection with paths deleted on dev since the initial base was empty.

`proof_shape: bind-only`; `admission_basis: rule-11-upstream-wrapper`.
The named upstream declarations are `Mertens.E₃.abs_le`,
`Mertens.E₃.bound''` and `Mertens.E₃.bound'''`. The concrete API requirement
is the sharp prime-product estimate needed by the Gronwall upper-envelope
consumer on the user-selected Robin line. Every retained helper is in the
elaborated dependency closure of at least one of those endpoints, in the
consumer-to-prerequisite direction. `computational_content.kind: none`:
these are general analytic estimates, not finite certificates or numerical
reductions. This port does not establish Robin's inequality or Gronwall.

## Gronwall Upper-Envelope Gap

Let `E(y) = product (p prime, p <= y), (1 - 1/p)^(-1)` and
`R(n) = sigma(n)/(exp(gamma) * n * log(log(n)))`. The following is a
consumer-to-prerequisite plan, not a claim that the unmeasured steps compile.
`self` means a repository proof is still needed, not a novel mathematical result.

| Sublemma | Status | Evidence or remaining obligation |
| --- | --- | --- |
| `product (1-1/p) ~ exp(-gamma)/log(y)` | upstream | The three E3 endpoints above, now ported and checked. |
| Reciprocate asymptotic equivalence | mathlib | `Asymptotics.IsEquivalent.inv`; rewrite the comparison as `exp(gamma)*log(y)`, then extract an eventual upper bound. This specialization is not measured here. |
| Exact sigma prime-factor product | mathlib | `ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`, compiler-checked in the leaf log. |
| `sigma(p^a)/p^a <= (1-1/p)^(-1)` | self | Closed by the measured leaf below, using the pinned prime-power and geometric-sum identities. |
| Extend the product over small prime divisors to all primes at most `y` | self | Factors are at least one; still needs the finite-set and floor interfaces. |
| Count prime divisors greater than `y`: `card <= log(n)/log(y)` | self | Use `Nat.prod_primeFactors_dvd` and sum/product logarithms; the specialized inequality is not measured. |
| Bound the large-prime product by `exp(2*log(n)/(y*log(y)))` | self | For `p > y >= 2`, `-log(1-1/p) <= 1/(p-1) <= 2/p`; sum the preceding count estimate. |
| SigmaSplit: `sigma(n)/n <= E(y)*exp(2*log(n)/(y*log(y)))` | self | Combine the exact factors, small-prime padding, and large-prime estimate. |
| Gronwall upper envelope | self | Substitute `y=log(n)`; the tail is `exp(2/log(log(n))) -> 1`. Combine with sharp Mertens and denominator positivity to get every requested epsilon bound. |

No PNT or RH premise enters this upper-envelope route. Mertens removes the
sharp-constant analytic dependency; it does not supply SigmaSplit. The equality
`limsup sigma(n)/(n*log(log(n))) = exp(gamma)` additionally needs the lower
limsup construction, for example integers with sufficiently saturated small
prime powers. That lower half is separate and was not proved in this attempt.

Measured leaf, in `GronwallLeaf.lean` (external probe, not an independent deposit):

```lean
theorem sigma_prime_pow_ratio_le {p : Nat} (hp : p.Prime) (a : Nat) :
    (ArithmeticFunction.sigma 1 (p ^ a) : Real) / (p : Real) ^ a <=
      (1 - 1 / (p : Real))⁻¹ := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : Real) < p := lt_trans zero_lt_one hp1
  have hpow : (0 : Real) < (p : Real) ^ a := pow_pos hp0 a
  have hfactor : (ArithmeticFunction.sigma 1 (p ^ a) : Real) =
      ∑ i ∈ Finset.range (a + 1), (p : Real) ^ i := by
    exact_mod_cast ArithmeticFunction.sigma_one_apply_prime_pow hp (i := a)
  rw [hfactor, geom_sum_eq (ne_of_gt hp1)]
  calc
    ((p : Real) ^ (a + 1) - 1) / (p - 1) / p ^ a <=
        (p : Real) ^ (a + 1) / (p - 1) / p ^ a := by
      gcongr
      linarith
    _ = (1 - 1 / (p : Real))⁻¹ := by
      rw [pow_succ]
      field_simp
      <;> ring
```

Command: `make -f Makefile -f <attempt>/probe.mk lean PROBE=<attempt>/GronwallLeaf.lean`.
Exit: 0. Wall time: 56.590490625 seconds, warm local tree, root build included.
Stuck at: none in this leaf; SigmaSplit remains unmeasured. The optional final
`ring` generated an unused-tactic warning because `field_simp` already closed
the goal; the measured source is retained unchanged.

```text
'GronwallLeaf.sigma_prime_pow_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Search scope: D5 sigma/prime-factor/product candidates, pinned
`ArithmeticFunction/Misc.lean`, `Algebra/Field/GeomSum.lean`,
`Algebra/Order/Field/GeomSum.lean`, and the inspected upstream Mertens source.
The exact sigma bound was not found in those searched candidates. The proof
reuses the two exact identities found in Mathlib, rather than re-proving them.

Retirement condition: once this repository's own pinned Mathlib contains
equivalent declarations, replace the matching source port with imports and
applications of those declarations. Upstream acceptance alone is not the trigger.

## Errata 2026-09-08: the upper-envelope gap table is closed

The `Gronwall Upper-Envelope Gap` table above was written before the two
assembly modules landed. Every row it marks `self` is now a public theorem in
`origin/dev`, and both modules carry a frozen state pin
(`Golden/Frozen/state/D5/S3/Weil/GronwallUpperEnvelope.lean.json` and
`GronwallLowerEnvelope.lean.json`). This section is an addition, not a rewrite:
the table is retained as the record of the route as it was planned.

| Table row | Landed declaration |
| --- | --- |
| Extend the product over small prime divisors to all primes at most `y` | `D5/S3/Weil/GronwallUpperEnvelope.small_prime_product_le` |
| Count prime divisors greater than `y` | `GronwallUpperEnvelope.large_prime_count_le` |
| Bound the large-prime product by `exp(2*log(n)/(y*log(y)))` | `GronwallUpperEnvelope.large_prime_product_le` |
| SigmaSplit | `GronwallUpperEnvelope.sigma_split` |
| Gronwall upper envelope | `GronwallUpperEnvelope.gronwall_upper_envelope` |
| `sigma(p^a)/p^a <= (1-1/p)^(-1)` | absorbed into the `sigma_split` proof; no separate public declaration |

The module's own header records the companion edges
`sigma_split -> small_prime_product_le`,
`large_prime_product_le -> large_prime_count_le`,
`sigma_split -> large_prime_product_le`, and
`gronwall_upper_envelope -> sigma_split`, and states that the finite estimates
reuse the `gronwall-step1-0907/attempt-1` and `gronwall-step2-0907/attempt-1`
measurements. The `GronwallLeaf.lean` probe recorded above therefore has no
remaining consumer; it is kept as the measurement that produced the estimate.

The paragraph above the leaf says the lower half "is separate and was not proved
in this attempt". That remains true of that attempt, and it has since been
proved elsewhere: `D5/S3/Weil/GronwallLowerEnvelope` supplies
`gronwall_lower_envelope`, `gronwall_envelopes`, and `robin_log_margin_liminf`.

Why this erratum exists: a standing dispatch loop reads this table to pick the
leaf-most unproved sublemma. Left as written, it names six targets that are all
already frozen, so each pass would spend a seat re-proving library theorems.
The reading that produced this section was taken against `origin/dev` at
`45e7b20dd95dd8b2d7b8784392c1814193b80515`; the declaration list came from
`git show origin/dev:D5/S3/Weil/GronwallUpperEnvelope.lean` and the frozen pins
from `ls Golden/Frozen/state/D5/S3/Weil/`. No mathematical claim of this note is
changed, and no upstream port or license text is touched.

## NOTICE

This distribution contains portions of PrimeNumberTheoremAnd,
copyright its contributors, licensed under the Apache License, Version 2.0.
Source commit: `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`;
source file: `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`.
The upstream tree contains `LICENSE` and no separate NOTICE file
(recursive GitHub tree, `truncated=false`, inspected by its structured entries).

Modified by trureturing on 2026-09-07: repository import routing, removal of
Architect metadata, restriction to the E3 proof dependency closure, module
splitting, visibility of five cross-module helpers, removal of one redundant
`rfl`, and replacement of `Set.mem_setOf_eq` by `Set.mem_ofPred_eq`.
The preliminary routing and tactic correction reuse the earlier
`mertens-probe-0907/attempt-1` worker's compatibility source.

The upstream exposition attributes the mathematical arguments to Leo Goldmakher,
*A quick proof of Mertens' theorem*:
<https://web.williams.edu/Mathematics/lg5/mertens.pdf>.
It also cites Arend Mellendijk's earlier unfinished formalization:
<https://github.com/FLDutchmann/Analytic/blob/main/Analytic/Mertens.lean>.
These attributions do not claim that either author reviewed this port.

The complete upstream license follows verbatim.

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```
