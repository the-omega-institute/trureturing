/- GID: D5/S3/Weil/ZetaCore/Defs
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the Zeta23 explicit-formula core definitions. -/

/- Ported from anthropics/zeta-23-lean commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
   Modified by trureturing on 2026-08-14: repository routing and Lean v4.31.0 adaptation. -/

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
## Retained Apache License 2.0 text

The following is the complete license text shipped with upstream Zeta23.

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

## Retained upstream NOTICE

The following NOTICE is retained verbatim. Its reference to `LICENSE` resolves
to the complete Apache License 2.0 text immediately above.

Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems
Copyright 2026 Anthropic, PBC

This product is licensed under the Apache License, Version 2.0 (see LICENSE).

This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
(source file, upstream commit, original copyright line) and a description of the local modifications.
Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.

This product depends on, but does not include, Lean 4 (https://github.com/leanprover/lean4) and
mathlib4 with its standard dependency set — fetched by the build tool from their public repositories at the
revisions pinned in lake-manifest.json: batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient and
plausible are released under the Apache License, Version 2.0; Cli (leanprover/lean4-cli) is released under the
MIT License (Copyright (c) 2021 Marc Huisinga). None of these dependencies is included in this repository.
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic

open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

/-! ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/

/-- Paper Fourier transform / h_f :  paperFT f z = ∫ u, f u * exp (I * z * u)  for complex z
([Notation]; [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u)e^{izu} du"). -/
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))

/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-- l := log(T/2π)  [Notation]. -/
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

/-- ℓ₁ := l + 2 log 2 − 1, "so that N(T,2T) = Tℓ₁/2π + O(l)"  [Notation]. -/
def ell1 (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1

/-- H(λ) := 2 − 1/λ − λ/3  [eq:Fdef]; H(1) = 2/3. -/
def Hfun (x : ℝ) : ℝ := 2 - 1 / x - x / 3

/-- F(λ) := λ / (1 + λ²/3)  [eq:Fdef]; F(1) = 3/4. -/
def Ffun (x : ℝ) : ℝ := x / (1 + x ^ 2 / 3)

/-- D₀ := T^{1/2}  [eq:D0]. -/
def D0 (T : ℝ) : ℝ := Real.sqrt T

/-- I := [T, 2T]  [Notation]. -/
def Iwin (T : ℝ) : Set ℝ := Icc T (2 * T)

/-- I' := (T − D₀, 2T + D₀]  [eq:D0]. -/
def Iprime (T : ℝ) : Set ℝ := Ioc (T - D0 T) (2 * T + D0 T)

lemma Hfun_one : Hfun 1 = 2 / 3 := by norm_num [Hfun]
lemma Ffun_one : Ffun 1 = 3 / 4 := by norm_num [Ffun]

/-! ## 2. The densities μ, Π_X, P_X, ν_X  [eq:mudef]–[eq:nudef]

Paper, verbatim: "Define, for τ ∈ ℝ and X = e^L > 1, s := 1/2 + iτ,
  μ(τ)   := (1/2π) Re Γ'/Γ(1/4 + iτ/2) − (log π)/(2π),                      [eq:mudef]
  Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π) Re (X^s − 1)/s,                           [eq:Pidef]
  P_X(τ) := −(1/π) Σ_{n≤X} Λ(n)/√n · cos(τ log n),                           [eq:Pdef]
  ν_X    := μ + Π_X + P_X."                                                   [eq:nudef]
-/

/-- μ(τ) := (1/2π)·Re (Γ'/Γ)(1/4 + iτ/2) − log π /(2π)   [eq:mudef].
Complex.digamma = logDeriv Gamma = Γ'/Γ (Mathlib Gamma/Digamma.lean). -/
def mu (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)

/-- Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π)·Re((X^s − 1)/s),  s = 1/2 + iτ  [eq:Pidef]
("the terms h_k(±i/2) coming from the pole of ζ … rewritten as the density Π_X"). -/
def PiX (X : ℝ) (τ : ℝ) : ℝ :=
  let s : ℂ := 1 / 2 + Complex.I * τ
  1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re

/-- P_X(τ) := −(1/π) Σ_{n ≤ X} Λ(n) n^{−1/2} cos(τ log n)  [eq:Pdef]. Sum over n ∈ Finset.Ioc 0 ⌊X⌋₊
(same indexing as Mathlib's Chebyshev.psi; Λ vanishes off prime powers; the n = 1 term is 0). -/
def PX (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n) / Real.sqrt n * Real.cos (τ * Real.log n)

/-- ν_X := μ + Π_X + P_X  [eq:nudef]. -/
def nuX (X : ℝ) (τ : ℝ) : ℝ := mu τ + PiX X τ + PX X τ

/-! ## 3. Abstract zero configurations  [Results], [subsec:weil], §4 closing paragraph -/

/-- γ_ρ := (ρ − 1/2)/i = γ − i(β − 1/2), "so that ρ = 1/2 + iγ_ρ, |Im γ_ρ| < 1/2, and γ_ρ ∈ ℝ iff
β = 1/2"  [Notation]. -/
def gammaOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

/-- The reflection ρ ↦ 1 − ρ̄ (same ordinate γ, mirrored β)  [subsec:weil]. -/
def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

/-- An abstract zero configuration: a set (carrier) of DISTINCT points ρ = β+iγ in the closed
strip 0 ≤ β ≤ 1 (the instances built from the zeros of ζ and of L(s,χ) lie in the open strip) with
multiplicities mult ρ ≥ 1, locally finite in the ordinate, and
invariant under ρ ↦ 1−ρ̄ with equal multiplicity. Paper §4 (after prop:zeroside), verbatim:
"Inequalities (eq:zeroside) hold for every locally finite multiset of points in the strip 0<β<1
that is invariant under ρ ↦ 1−ρ̄ and satisfies N(t+1)−N(t) ≪ log(t+3); they contain no
arithmetic."  [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄;
multiplicities agree …)".  The quantitative local count N(t+1)−N(t) ≤ A₀ log(t+3) is not part of
this structure; it is a field of PaperInputs (H-RvM) in Zeta23/Hypotheses.lean.
Distinct points (the set) and multiplicities (the function) are deliberately separate objects. -/
structure ZeroConfig where
  /-- the set 𝒵 of distinct zeros -/
  carrier : Set ℂ
  /-- multiplicity m_ρ (value irrelevant off carrier) -/
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  /-- local finiteness in the ordinate: finitely many zeros with T₁ < γ ≤ T₂ -/
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace ZeroConfig

variable (Z : ZeroConfig)

/-- {ρ ∈ 𝒵 : T₁ < γ ≤ T₂}, γ = Im ρ (positive-ordinate window convention of [Results]; NOT |γ|). -/
def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- on-line points: β = 1/2. -/
def onLine : Set ℂ := {ρ | ρ.re = 1 / 2}

/-- simple points: m_ρ = 1. -/
def simple : Set ℂ := {ρ | Z.mult ρ = 1}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} counted WITH multiplicity  [Results]. -/
def N (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ

/-- N_d(T₁,T₂) := same, each distinct point counted once  [Results]. -/
def Nd (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂).ncard

/-- N₀(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITH multiplicity  [Results]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ onLine, Z.mult ρ

/-- N₀*(T₁,T₂) := zeros on the critical line with T₁ < γ ≤ T₂, WITHOUT multiplicity  [Results]. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}  [Results]. -/
def N0s (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ onLine ∩ Z.simple).ncard

/-- Nˢ(T₁,T₂) := number of simple zeros (any β) with T₁ < γ ≤ T₂  [Results]. -/
def Ns (T₁ T₂ : ℝ) : ℕ := (Z.window T₁ T₂ ∩ Z.simple).ncard

/-- Summand of Weil's form: m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))  [eq:Wdef]. -/
def Wsummand (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT g ((starRingEnd ℂ) (gammaOf ρ)))

/-- W(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)), "Σ_ρ runs over the DISTINCT nontrivial zeros (of
either sign of γ) and the multiplicity is written explicitly"  [eq:Wdef]. As a tsum over the
subtype of carrier; absolute convergence is part of hypothesis H-EF. -/
def W (f g : ℝ → ℂ) : ℂ := ∑' ρ : Z.carrier, Z.Wsummand f g ρ

end ZeroConfig

/-! ## 4. The test family  [subsec:family] -/

/-- "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)"  [subsec:family]. -/
structure TaperProfile (ϱ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 ϱ
  monotone : Monotone ϱ
  eq_zero : ∀ x ≤ 0, ϱ x = 0
  eq_one : ∀ x ≥ 1, ϱ x = 1

/-- Fixed (T-independent) parameters: the profile ϱ, the exponent λ (lam; X = (T/2π)^λ), and the
ramp width w ([eq:wrange]: 1 ≤ w ≤ L/8; §6 takes w := 1). T is always a separate argument. -/
structure Params where
  ϱ : ℝ → ℝ
  lam : ℝ
  w : ℝ

/-- Standing assumptions on the fixed parameters: ϱ a taper profile, 0 < λ ≤ 1, w ≥ 1.
(The upper bound w ≤ L/8 of [eq:wrange] depends on T and is stated where used.) -/
structure Params.Valid (P : Params) : Prop where
  taper : TaperProfile P.ϱ
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w

namespace Params

variable (P : Params) (T : ℝ)

/-- L := λ·l  [Notation]. -/
def L : ℝ := P.lam * l T

/-- X := e^L = (T/2π)^λ  [Notation]. -/
def X : ℝ := Real.exp (P.L T)

/-- λ₁ := L/ℓ₁ = λ + O(1/l)  [Notation], [eq:ratio]. Not the same as λ. -/
def lam1 : ℝ := P.L T / ell1 T

/-- grid step h := 2π/L  [eq:fk]. -/
def hgrid : ℝ := 2 * Real.pi / P.L T

/-- d := ⌊T/h⌋ = ⌊LT/2π⌋  [eq:fk]. -/
def d : ℕ := ⌊P.L T * T / (2 * Real.pi)⌋₊

/-- τ_k := T + k h (k ∈ ℤ)  [eq:fk]. -/
def tau (k : ℤ) : ℝ := T + k * P.hgrid T

/-- the taper φ(u) := ϱ((L/2 − |u|)/w)  [eq:phidef]; supp φ = [−L/2, L/2] exactly. -/
def phi (u : ℝ) : ℝ := P.ϱ ((P.L T / 2 - |u|) / P.w)

/-- a := L⁻¹ ∫ φ²  [eq:abdef]. -/
def a : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 2

/-- b := L⁻¹ ∫ φ⁴  [eq:abdef]. -/
def b : ℝ := (P.L T)⁻¹ * ∫ u : ℝ, (P.phi T u) ^ 4

/-- φ̂(z) for complex z (paper convention, = h_φ(z)). -/
def phiHat (z : ℂ) : ℂ := paperFT (fun u => (P.phi T u : ℂ)) z

/-- φ̂ on the real line as a real number ("φ̂ and Φ are real, even, entire"); = Re of phiHat.
That the imaginary part vanishes is proved in Taper.lean, not assumed. -/
def phiHatR (r : ℝ) : ℝ := (P.phiHat T (r : ℂ)).re

/-- Φ := (φ²)^  [eq:PhigA], complex argument. -/
def Phi (z : ℂ) : ℂ := paperFT (fun u => (((P.phi T u) ^ 2 : ℝ) : ℂ)) z

/-- Φ on the real line as a real number; Φ(0) = aL. -/
def PhiR (r : ℝ) : ℝ := (P.Phi T (r : ℂ)).re

/-- (v ⋆ v)(y) := ∫ v(u) v(u+y) du  [eq:PhigA]. -/
def autocorr (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, v u * v (u + y)

/-- g := φ² ⋆ φ²  [eq:PhigA]; Φ² = ĝ on ℝ, g(0) = bL. -/
def g (y : ℝ) : ℝ := autocorr (fun u => (P.phi T u) ^ 2) y

/-- A_φ := φ ⋆ φ  [eq:PhigA]; φ̂² = (A_φ)^. -/
def Aphi (y : ℝ) : ℝ := autocorr (P.phi T) y

/-- c_ϱ := 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ (≥ 4)  [eq:phinorms]. -/
def crho : ℝ :=
  4 * (⨆ x : ℝ, |deriv P.ϱ x|) + 4 * ∫ x : ℝ, |deriv (deriv P.ϱ) x|

/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))  [eq:psidef]; at r = 0 the paper's value is L (2/0 = ∞), which
Lean's 2/0 = 0 would get wrong, hence the explicit case. -/
def psi (r : ℝ) : ℝ := if r = 0 then P.L T else min (P.L T) (min (2 / |r|) (P.crho / (P.w * r ^ 2)))

/-- f_k(u) := φ(u) e^{−iτ_k u}  [eq:fk]; h_{f_k}(z) = φ̂(z − τ_k). -/
def fk (k : ℤ) (u : ℝ) : ℂ := (P.phi T u : ℂ) * Complex.exp (-(Complex.I * P.tau T k * u))

/-- ℰ_T := w/L + (l² + X) log l /(T l) + T^{λ/2 − 1}  [thm:traces]. -/
def calE : ℝ :=
  P.w / P.L T + (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) + T ^ (P.lam / 2 - 1)

/-! ### The prime-side matrix (second expression in [eq:Gdef]) -/

/-- G_{kl} via the PRIME side: ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ, X = e^L  [eq:Gdef, 2nd expression],
for arbitrary integer indices k, l. Real-valued. -/
def Gentry (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ - P.tau T l) * nuX (P.X T) τ

/-- The d×d prime-side matrix G = (G_{kl})_{0≤k,l<d} as a complex matrix (entries are real;
complex so that RHLinalg's RCLike lemmas and the zero-side matrix share one type). -/
def Gp : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => (P.Gentry T (k : ℤ) (l : ℤ) : ℂ)

/-- tr G̃ as the real number L⁻¹ Σ_{k<d} G_{kk} (what §5 computes)  [prop:trace]. -/
def trGtilde : ℝ := (P.L T)⁻¹ * ∑ k : Fin (P.d T), P.Gentry T k k

/-- tr G̃² = Σ_{k,l<d} G̃_{kl}² (= ‖G̃‖_F², G real symmetric)  [sec:prime intro]. -/
def trGtildeSq : ℝ := (P.L T)⁻¹ ^ 2 * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), P.Gentry T k l ^ 2

/-- scaling to tilde units M ↦ M/L  [eq:Gdef], [eq:AE]  (G̃, Ã, Ẽ). -/
def tilde {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.L T)⁻¹ : ℂ) • M

/-- scaling to hat units M ↦ M/(aL²)  [eq:hatunits]  (Ĝ, Â, Ê). Not to be mixed with tilde
units. -/
def hat {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ := ((P.a T * P.L T ^ 2)⁻¹ : ℂ) • M

end Params

/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/

namespace ZeroConfig

/-- zero-side summand m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l). -/
def Gsummand (Z : ZeroConfig) (P : Params) (T : ℝ) (k l : ℤ) (ρ : ℂ) : ℂ :=
  (Z.mult ρ : ℂ) * P.phiHat T (gammaOf ρ - P.tau T k) * P.phiHat T (gammaOf ρ - P.tau T l)

/-- G_{kl} := W(f_k,f_l) = Σ_ρ m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:Gdef, 1st expression] (zero side;
tsum over all distinct zeros). H-EF gives Z.Gz P T = P.Gp T. -/
def Gz (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑' ρ : Z.carrier, Z.Gsummand P T k l ρ

/-- 𝒵(I') := distinct zeros with ordinate γ ∈ I' = (T−D₀, 2T+D₀]  [§4 Block structure]. -/
def ZIprime (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.window (T - D0 T) (2 * T + D0 T)

/-- A_{kl} := Σ_{ρ : γ ∈ I'} m_ρ φ̂(γ_ρ−τ_k) φ̂(γ_ρ−τ_l)  [eq:AE] (a FINITE sum, finsum). -/
def Az (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand P T k l ρ

/-- E := G − A  [eq:AE] (the tail: zeros with γ ∉ I', INCLUDING negative ordinates). -/
def Ez (Z : ZeroConfig) (P : Params) (T : ℝ) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  Z.Gz P T - Z.Az P T

/-- 𝒮₁: β = 1/2 and m_ρ = 1, within 𝒵(I'). s₁ := #𝒮₁  [§4 Block structure]. -/
def S1 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ Z.simple
/-- 𝒮₂: β = 1/2 and m_ρ ≥ 2, within 𝒵(I'). s₂ := #𝒮₂. -/
def S2 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}
/-- off-line points of 𝒵(I') (β ≠ 1/2); 𝒫 = unordered pairs {ρ, 1−ρ̄} of these, #offLine = 2p. -/
def offLine (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ {ρ | ρ.re ≠ 1 / 2}

/-- s₁ := #𝒮₁. -/
def s1 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S1 T).ncard
/-- s₂ := #𝒮₂. -/
def s2 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S2 T).ncard
/-- p := number of unordered off-line pairs {ρ,1−ρ̄} in 𝒵(I'); #offLine = 2p. -/
def p (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.offLine T).ncard / 2

/-- N(I') := N(T−D₀, 2T+D₀)  [eq:Ncount]. -/
def NIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N (T - D0 T) (2 * T + D0 T)
/-- N_on(I') := Σ_{ρ ∈ 𝒮₁ ∪ 𝒮₂} m_ρ  [§4]. -/
def NonIprime (Z : ZeroConfig) (T : ℝ) : ℕ := Z.N0 (T - D0 T) (2 * T + D0 T)

end ZeroConfig

end Zeta23
