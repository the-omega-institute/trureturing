/- GID: D5/S3/Analytic/ConvexBarrier/PrimalDikin
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/PrimalDikin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.Basic
import D5.S3.Analytic.ConvexBarrier.DikinOneDimensional
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Monotone

/-!
Genuine primal Dikin containment from `Basic.IsLHSCB`, with no Dikin,
conjugacy, convexity, or line-integral assumption. Finite boundary blowup
must cover the actual frontier of the open domain. For `D = interior K`,
`B = frontier K`, this follows from `frontier_interior_subset` for any K.

The line is the actual affine line `x + t • h`. Positive Hessian and C3
are inherited from F by differentiating its actual Frechet derivative
tensors, not from an abstract line-function existence premise.

This standard SC foundation supplies the primal half of (2.2) and Lemma
3.2 of Zhang--Fu--Dai, arXiv:2611.06404v1. It does not establish their
conjugate-barrier facts (2.4)--(2.5), or their scalar parameter theorem.

SOURCE ONLY. No Lean elaboration or kernel execution has been performed.
-/

open Set Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.ConvexBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordinary Frechet derivatives evaluated repeatedly on the actual line
direction. Order zero is definitionally the actual value of F. -/
noncomputable def lineJet (n : ℕ) (F : E → ℝ) (x h : E) (t : ℝ) : ℝ :=
  iteratedFDeriv ℝ n F (x + t • h) (fun _ : Fin n => h)

theorem IsLHSCB.lineJet_eq_diagonal {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x h : E} {t : ℝ}
    (ht : x+t • h ∈ D) {n : ℕ} (hn : (n : ℕ∞ω) ≤ 3) :
    lineJet n F x h t = diagonal n D F (x+t • h) h := by
  unfold lineJet diagonal
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hF.domain_open.uniqueDiffOn
    ((hF.smooth.contDiffAt (hF.domain_open.mem_nhds ht)).of_le hn) ht]

/-- The actual successive line-derivative identities, through order three.
This is the affine chain rule, evaluated on the same fixed direction. -/
theorem IsLHSCB.lineJet_hasDerivAt {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x h : E} {t : ℝ}
    (ht : x+t • h ∈ D) {n : ℕ} (hn : (n : ℕ∞ω) < 3) :
    HasDerivAt (lineJet n F x h) (lineJet (n+1) F x h t) t := by
  have hd := (hF.smooth.contDiffAt (hF.domain_open.mem_nhds ht)).differentiableAt_iteratedFDeriv hn
  have hl : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h) using 1
    · funext s
      simp [add_comm]
    · simpa
  exact (hd.hasFDerivAt.continuousMultilinear_apply_const
    (fun _ : Fin n => h)).comp_hasDerivAt t hl

/-- A concrete sequence in `[0,T)` converging to T, including a valid first
term t_0=0. No chosen boundary sequence or endpoint regularity is assumed. -/
noncomputable def approachEndpoint (T : ℝ) (n : ℕ) : ℝ :=
  T * (1 - 1 / ((n : ℝ)+1))

theorem approachEndpoint_mem {T : ℝ} (hT : 0 < T) (n : ℕ) :
    approachEndpoint T n ∈ Ico 0 T := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : 0 < (n : ℝ)+1 := by positivity
  have hrec : 1 / ((n : ℝ)+1) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hrecpos : 0 < 1 / ((n : ℝ)+1) := by positivity
  constructor
  · exact mul_nonneg hT.le (sub_nonneg.mpr hrec)
  · dsimp [approachEndpoint]
    nlinarith [mul_pos hT hrecpos]

theorem approachEndpoint_tendsto (T : ℝ) :
    Tendsto (approachEndpoint T) atTop (𝓝 T) := by
  have hh : Tendsto (fun n : ℕ => T*(1-1/((n : ℝ)+1))) atTop
      (𝓝 (T*(1-0))) := (tendsto_const_nhds (x := T)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  change Tendsto (fun n : ℕ => T * (1 - 1 / ((n : ℝ)+1))) atTop (𝓝 T)
  simpa only [sub_zero, mul_one] using hh

/-- First exit along an actual affine line. No convexity or maximal-interval
assumption is needed: the infimum of the closed exit set is attained. -/
theorem exists_first_line_exit {D : Set E} (hD : IsOpen D)
    {x h : E} (hx : x ∈ D) (houtside : x+h ∉ D) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ x+T • h ∉ D ∧
      (∀ t ∈ Ico 0 T, x+t • h ∈ D) := by
  let S : Set ℝ := {t | 0 ≤ t ∧ x+t • h ∉ D}
  have hcont : Continuous (fun t : ℝ => x+t • h) := by fun_prop
  have hSclosed : IsClosed S :=
    isClosed_Ici.inter (hD.isClosed_compl.preimage hcont)
  have h1 : (1 : ℝ) ∈ S := by simpa [S] using houtside
  have hSne : S.Nonempty := ⟨1, h1⟩
  have hSb : BddBelow S := ⟨0, fun _ ht => ht.1⟩
  let T : ℝ := sInf S
  have hTm : T ∈ S := hSclosed.csInf_mem hSne hSb
  have hT1 : T ≤ 1 := csInf_le hSb h1
  have hT0 : 0 < T := by
    have hne : T ≠ 0 := by
      intro he
      have hh := hTm.2
      rw [he, zero_smul, add_zero] at hh
      exact hh hx
    exact lt_of_le_of_ne hTm.1 (Ne.symm hne)
  refine ⟨T, hT0, hT1, hTm.2, ?_⟩
  intro t ht
  by_contra hn
  have hh : T ≤ t := csInf_le hSb (show t ∈ S from ⟨ht.1, hn⟩)
  exact (not_le_of_gt ht.2) hh

/-- Primal Dikin containment at arbitrary x and arbitrary displacement h.
The strict radius is essential. The boundary hypothesis only identifies
where the *given* all-sequences blowup condition applies. -/
theorem IsLHSCB.primal_dikin {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hboundary : frontier D ⊆ B)
    {x : E} (hx : x ∈ D) (h : E)
    (hradius : diagonal 2 D F x h < 1) : x+h ∈ D := by
  by_cases hh : h = 0
  · simpa [hh] using hx
  by_contra hout
  obtain ⟨T, hT, hT1, hTout, hsegment⟩ :=
    exists_first_line_exit hF.domain_open hx hout
  let f := lineJet 0 F x h
  let g := lineJet 1 F x h
  let q := lineJet 2 F x h
  let c := lineJet 3 F x h
  have hjet (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (t : ℝ) (ht : t ∈ Ico 0 T) :
      lineJet n F x h t = diagonal n D F (x+t • h) h :=
    hF.lineJet_eq_diagonal (hsegment t ht) hn
  have hqpos : ∀ t ∈ Ico 0 T, 0 < q t := by
    intro t ht
    rw [show q t = diagonal 2 D F (x+t • h) h from hjet 2 (by norm_num) t ht]
    exact hF.hessian_pos _ (hsegment t ht) h hh
  have hsc : ∀ t ∈ Ico 0 T,
      |c t| ≤ 2*q t*Real.sqrt (q t) := by
    intro t ht
    dsimp [c, q]
    rw [hjet 3 (by norm_num) t ht, hjet 2 (by norm_num) t ht]
    exact hF.self_concordant _ (hsegment t ht) h
  have hzero : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hq0 : 0 < q 0 := hqpos 0 hzero
  have hq0lt : q 0 < 1 := by
    change lineJet 2 F x h 0 < 1
    rw [hjet 2 (by norm_num) 0 hzero]
    simpa only [zero_smul, add_zero] using hradius
  have hs0 : 0 < Real.sqrt (q 0) := Real.sqrt_pos.mpr hq0
  have hslt : Real.sqrt (q 0) < 1 := by
    nlinarith [Real.sq_sqrt hq0.le]
  have hrad : T < (Real.sqrt (q 0))⁻¹ := by
    have hh1 : 1 < (Real.sqrt (q 0))⁻¹ := by
      rw [inv_eq_one_div]
      exact (lt_div_iff₀ hs0).mpr (by simpa using hslt)
    exact lt_of_le_of_lt hT1 hh1
  have hupper := selfConcordant_finite_segment_upper (f := f) (g := g)
    (q := q) (c := c) hT
    (fun t ht => hF.lineJet_hasDerivAt (hsegment t ht) (by norm_num))
    (fun t ht => hF.lineJet_hasDerivAt (hsegment t ht) (by norm_num))
    (fun t ht => hF.lineJet_hasDerivAt (hsegment t ht) (by norm_num))
    hqpos hsc hrad
  let u : ℕ → E := fun n => x + approachEndpoint T n • h
  have hu : ∀ n, u n ∈ D := fun n =>
    hsegment _ (approachEndpoint_mem hT n)
  have hulim : Tendsto u atTop (𝓝 (x+T • h)) := by
    exact tendsto_const_nhds.add ((approachEndpoint_tendsto T).smul tendsto_const_nhds)
  have hfront : x+T • h ∈ frontier D := by
    rw [frontier, hF.domain_open.interior_eq]
    exact ⟨mem_closure_of_tendsto hulim (Eventually.of_forall hu), hTout⟩
  have hblow := hF.boundary_blowup _ (hboundary hfront) u hu hulim
  let U : ℝ := f 0 + (|g 0| + ((Real.sqrt (q 0))⁻¹-T)⁻¹ ^ 2*T)*T
  have hUb : ∀ n, F (u n) ≤ U := fun n =>
    hupper _ (approachEndpoint_mem hT n)
  have hev : ∀ᶠ n in atTop, U+1 ≤ F (u n) :=
    (tendsto_atTop.mp hblow) (U+1)
  obtain ⟨n, hn⟩ := hev.exists
  have hn' := hUb n
  linarith

/-- The concrete topological cone formulation. No regularity, homogeneity,
or enlarged-cone replacement is hidden in the geometric premise. -/
theorem IsLHSCB.primal_dikin_interior {ν : ℝ} {K : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν (interior K) (frontier K) F)
    {x : E} (hx : x ∈ interior K) (h : E)
    (hradius : diagonal 2 (interior K) F x h < 1) : x+h ∈ interior K :=
  hF.primal_dikin frontier_interior_subset hx h hradius

/-- Every actual outside point is excluded from the open unit ellipsoid.
The Hessian norm is squared throughout; no square-root sign conversion is
needed to feed the scalar quadratic algebra. -/
theorem IsLHSCB.primal_exclusion {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hboundary : frontier D ⊆ B)
    {x y : E} (hx : x ∈ D) (hy : y ∉ D) :
    1 ≤ diagonal 2 D F x (y-x) := by
  by_contra hn
  have hh := hF.primal_dikin hboundary hx (y-x) (lt_of_not_ge hn)
  exact hy (by simpa only [add_sub_cancel] using hh)

/-- Both chord directions, with arbitrary outside endpoints on their rays.
This is stated on the original domain and actual Hessian. -/
theorem IsLHSCB.primal_chord_exclusions {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hboundary : frontier D ⊆ B)
    {x h : E} (hx : x ∈ D) (δminus δplus : ℝ)
    (hminus : ∀ t : ℝ, 0 < t → t • (x-δminus • h) ∉ D)
    (hplus : ∀ t : ℝ, 0 < t → t • (x+δplus • h) ∉ D) :
    (∀ t : ℝ, 0 < t →
      1 ≤ diagonal 2 D F x (t • (x-δminus • h)-x)) ∧
    (∀ t : ℝ, 0 < t →
      1 ≤ diagonal 2 D F x (t • (x+δplus • h)-x)) := by
  exact ⟨fun t ht => hF.primal_exclusion hboundary hx (hminus t ht),
    fun t ht => hF.primal_exclusion hboundary hx (hplus t ht)⟩

end D5.S3.Analytic.ConvexBarrier
