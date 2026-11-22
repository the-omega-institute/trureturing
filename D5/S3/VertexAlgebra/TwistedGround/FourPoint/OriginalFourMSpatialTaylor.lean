/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor extraction through the marked Wick recurrence and normally convergent sums. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
import D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient
import Mathlib.Analysis.Complex.Liouville

/-! Taylor extraction on a common coordinate polydisk. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology ContDiff Matrix
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick

open OriginalGaussianSewnAnalytic (coefficient)
open NativeAffineExternalCoefficient (coordinateDerivative coordinateJet)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Ordinary Taylor extraction in one coordinate, with the others left as
parameters. The expansion point for the selected coordinate is always zero. -/
private def take (n : X → ℕ) (i : X) (f : (X → ℂ) → ℂ) (u : X → ℂ) : ℂ :=
  coefficient (n i) fun t => f (Function.update u i t)

/-- Spatial Taylor coefficient with the indicated coordinates and degrees. -/
def spatialCoefficient (n : X → ℕ) : List X → ((X → ℂ) → ℂ) → (X → ℂ) → ℂ
  | [], f => f
  | i :: l, f => spatialCoefficient n l (take n i f)

private def inserts (i : X) (t : ℂ) (u : X → ℂ) : X → ℂ :=
  Function.update u i t

private theorem take_analytic (n : X → ℕ) (i : X) (f : (X → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) : AnalyticAt ℂ (take n i f) 0 := by
  let L : ℂ →L[ℂ] (X → ℂ) := ContinuousLinearMap.single (R := ℂ) (φ := fun _ : X => ℂ) i
  let Q : (X → ℂ) →L[ℂ] (X → ℂ) :=
    ContinuousLinearMap.id ℂ _ - L.comp (ContinuousLinearMap.proj i)
  let M := ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n i) => X → ℂ) ℂ
    (fun _ => L 1)
  let g : (X → ℂ) → ℂ := fun u => M (iteratedFDeriv ℂ (n i) f (Q u)) / ((n i).factorial : ℂ)
  have hD : AnalyticAt ℂ (iteratedFDeriv ℂ (n i) f) 0 :=
    (AnalyticOnNhd.iteratedFDeriv (s := {u | AnalyticAt ℂ f u}) (fun _ hu => hu) _) _ hf
  have hg : AnalyticAt ℂ g 0 := by
    exact ((M.analyticAt _).comp (hD.comp_of_eq (Q.analyticAt _) (map_zero Q))).div_const
  apply hg.congr
  have he : ∀ᶠ u : X → ℂ in 𝓝 0, AnalyticAt ℂ f (Q u) :=
    (Q.continuous.continuousAt.tendsto).eventually (by simpa using hf.eventually_analyticAt)
  filter_upwards [he] with u hu
  let F := fun v : X → ℂ => f (v + Q u)
  have hF : AnalyticAt ℂ F 0 := hu.comp_of_eq
    (analyticAt_id.add analyticAt_const) (by simp)
  have hd : ContDiffAt ℂ (n i) F 0 := hF.contDiffAt
  obtain ⟨s, hsOpen, hs, hFs⟩ := hd.contDiffWithinAt.contDiffOn' (s := Set.univ)
    (m := n i) le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hFs
  have hL : L 0 ∈ s := by simpa using hs
  have hLs := (hsOpen.preimage L.continuous).uniqueDiffOn (𝕜 := ℂ)
  have hcomp : ContDiffAt ℂ (n i) (F ∘ L) 0 :=
    ContDiffAt.comp 0 (by simpa using hd) L.contDiff.contDiffAt
  have h := L.iteratedFDerivWithin_comp_right hFs hsOpen.uniqueDiffOn hLs hL le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hLs hcomp hL, map_zero,
    iteratedFDerivWithin_eq_iteratedFDeriv hsOpen.uniqueDiffOn hd hs] at h
  have hEq : F ∘ L = fun t => f (inserts i t u) := by
    funext t
    change f (L t + Q u) = f (inserts i t u)
    congr 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [L, Q, inserts]
    · simp [L, Q, inserts, hj]
  have hm := congrArg (fun p : ContinuousMultilinearMap ℂ (fun _ : Fin (n i) => ℂ) ℂ =>
    p (fun _ => 1)) h
  rw [hEq, ← iteratedDeriv_eq_iteratedFDeriv] at hm
  change _ = iteratedFDeriv ℂ (n i) F 0 (fun _ => L 1) at hm
  have htrans : iteratedFDeriv ℂ (n i) F 0 = iteratedFDeriv ℂ (n i) f (Q u) := by
    simpa [F] using (iteratedFDeriv_comp_add_right (𝕜 := ℂ) (f := f) (n i) (Q u) 0)
  rw [htrans] at hm
  exact congrArg (fun a : ℂ => a / ((n i).factorial : ℂ)) hm.symm

omit [Fintype X] in
private theorem take_congr (n : X → ℕ) (i : X) {f g : (X → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 0] g) : take n i f =ᶠ[𝓝 0] take n i g := by
  obtain ⟨s, hs, hopen, hzero⟩ := mem_nhds_iff.mp h
  have hzeroUpdate : Continuous (inserts i 0 : (X → ℂ) → (X → ℂ)) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [inserts, Function.update_self] using
        (continuous_const : Continuous (fun _ : X → ℂ => (0 : ℂ)))
    · simpa only [inserts, Function.update_of_ne hji] using continuous_apply j
  have hmem : ∀ᶠ u : X → ℂ in 𝓝 0, inserts i 0 u ∈ s :=
    hzeroUpdate.continuousAt.tendsto.eventually (by
      simpa [inserts] using hopen.mem_nhds hzero)
  filter_upwards [hmem] with u hu
  have hupdate : Continuous (fun t => inserts i t u) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      rw [show (fun t : ℂ => inserts i t u i) = id from
        by funext t; simp [inserts]]
      exact continuous_id
    · simpa only [inserts, Function.update_of_ne hji] using
        (continuous_const : Continuous (fun _ : ℂ => u j))
  have hslice : (fun t => f (inserts i t u)) =ᶠ[𝓝 0] (fun t => g (inserts i t u)) :=
    (hupdate.continuousAt.tendsto.eventually (hopen.mem_nhds hu)).mono (fun _ h => hs h)
  exact congrArg (fun a : ℂ => a / ((n i).factorial : ℂ)) (hslice.iteratedDeriv_eq _)

omit [Fintype X] in
theorem spatialCoefficient_congr (n : X → ℕ) (l : List X) {f g : (X → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 0] g) : spatialCoefficient n l f =ᶠ[𝓝 0] spatialCoefficient n l g := by
  induction l generalizing f g with
  | nil => exact h
  | cons i l ih => exact ih (take_congr n i h)

private theorem update_mem_ball (i : X) {u : X → ℂ} {t : ℂ} {r : ℝ}
    (hu : u ∈ Metric.ball 0 r) (ht : t ∈ Metric.ball 0 r) :
    inserts i t u ∈ Metric.ball 0 r := by
  rw [mem_ball_zero_iff] at hu ht ⊢
  apply lt_of_le_of_lt _ (max_lt hu ht)
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg u))).2
  intro j
  by_cases hj : j = i
  · subst j
    simp [inserts]
  · exact (by simpa only [inserts, Function.update_of_ne hj] using
      (norm_le_pi_norm u j).trans (le_max_left ‖u‖ ‖t‖))

private theorem take_analyticOnNhd (n : X → ℕ) (i : X) {f : (X → ℂ) → ℂ}
    {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (take n i f) (Metric.ball 0 r) := by
  intro u hu
  let G : (X → ℂ) → ℂ := fun z => f (z + inserts i 0 u)
  have h0 : inserts i 0 u ∈ Metric.ball 0 r := update_mem_ball i hu (Metric.mem_ball_self hr)
  have hg : AnalyticAt ℂ G 0 := (hf _ h0).comp_of_eq
    (analyticAt_id.add analyticAt_const) (zero_add _)
  have he : (fun z => take n i G (z - u)) = take n i f := by
    funext z
    simp only [take, G]
    congr 1
    funext t
    change f (inserts i t (z - u) + inserts i 0 u) = f (inserts i t z)
    congr 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [inserts]
    · simp [inserts, Function.update_of_ne hj]
  rw [← he]
  exact (take_analytic n i G hg).comp_of_eq
    (analyticAt_id.sub analyticAt_const) (sub_self u)

private theorem locallyUniform_iteratedDeriv {Y : Type*} {p : Filter Y}
    {F : Y → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f p U)
    (hF : ∀ y, AnalyticOnNhd ℂ (F y) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun j => iteratedDeriv k (F j)) (iteratedDeriv k f) p U := by
  have hA (j : Y) (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n (F j)) U := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hF j
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ih.deriv (Eventually.of_forall fun j => (hA j k).differentiableOn) hU

private theorem take_hasSum {Y : Type*} {f : Y → (X → ℂ) → ℂ} {b : Y → ℝ}
    (hb : Summable b) {r : ℝ} (hf : ∀ j, AnalyticOnNhd ℂ (f j) (Metric.ball 0 r))
    (hbound : ∀ j u, u ∈ Metric.ball 0 r → ‖f j u‖ ≤ b j)
    (n : X → ℕ) (i : X) {u : X → ℂ} (hu : u ∈ Metric.ball 0 r) (hr : 0 < r) :
    HasSum (fun j => take n i (f j) u) (take n i (fun z => ∑' j, f j z) u) := by
  let F (j : Y) (t : ℂ) := f j (inserts i t u)
  have hA : ∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 r) := by
    intro j t ht
    refine (hf j _ (update_mem_ball i hu ht)).comp_of_eq
      (f := fun t => inserts i t u) ?_ rfl
    rw [analyticAt_pi_iff]
    intro k
    by_cases hk : k = i
    · subst k
      simp only [inserts, Function.update_self]
      exact analyticAt_id
    · simp [inserts, Function.update_of_ne hk, analyticAt_const]
  have hFin (s : Finset Y) : AnalyticOnNhd ℂ (fun t => ∑ j ∈ s, F j t) (Metric.ball 0 r) :=
    fun t ht => Finset.analyticAt_fun_sum s (fun j _ => hA j t ht)
  have h := (tendstoUniformlyOn_tsum (f := F) hb
    (fun j t ht => hbound j _ (update_mem_ball i hu ht))).tendstoLocallyUniformlyOn
  have hd := (locallyUniform_iteratedDeriv h hFin Metric.isOpen_ball (n i)).tendsto_at
    (Metric.mem_ball_self hr : (0 : ℂ) ∈ Metric.ball 0 r)
  have hEq (s : Finset Y) : iteratedDeriv (n i) (fun t => ∑ j ∈ s, F j t) 0 =
      ∑ j ∈ s, iteratedDeriv (n i) (F j) 0 :=
    iteratedDeriv_fun_sum (fun j _ => (hA j _ (Metric.mem_ball_self hr)).contDiffAt)
  have hs : HasSum (fun j => iteratedDeriv (n i) (F j) 0)
      (iteratedDeriv (n i) (fun t => ∑' j, F j t) 0) := by
    simpa only [hEq, HasSum, SummationFilter.unconditional_filter] using hd
  simpa only [take, coefficient, F, inserts, div_eq_mul_inv] using
    hs.mul_right (((n i).factorial : ℂ)⁻¹)

private theorem take_bound {f : (X → ℂ) → ℂ} {r B : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hB : ∀ u ∈ Metric.ball 0 r, ‖f u‖ ≤ B) (n : X → ℕ) (i : X)
    {u : X → ℂ} (hu : u ∈ Metric.ball 0 r) :
    ‖take n i f u‖ ≤ B / (r / 2) ^ n i := by
  have hr2 : 0 < r / 2 := by positivity
  have hslice : DifferentiableOn ℂ (fun t => f (inserts i t u)) (Metric.ball 0 r) := by
    intro t ht
    apply DifferentiableAt.differentiableWithinAt
    refine (hf _ (update_mem_ball i hu ht)).differentiableAt.comp t ?_
    rw [differentiableAt_pi]
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj, differentiableAt_const]
  have hclosed : Metric.closedBall (0 : ℂ) (r / 2) ⊆ Metric.ball 0 r := by
    exact Metric.closedBall_subset_ball (by linarith)
  have hdiff := hslice.diffContOnCl_ball hclosed
  have hs : ∀ t ∈ Metric.sphere (0 : ℂ) (r / 2), ‖f (inserts i t u)‖ ≤ B :=
    fun t ht => hB _ (update_mem_ball i hu (hclosed (Metric.sphere_subset_closedBall ht)))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n i) hr2 hdiff hs
  simp only [take, coefficient, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : 0 < ((n i).factorial : ℝ))).2
  rw [show B / (r / 2) ^ n i * ((n i).factorial : ℝ) =
    ((n i).factorial : ℝ) * B / (r / 2) ^ n i by ring]
  exact h

/-- The spatial coefficient of a normally convergent series at the origin is
the sum of its spatial coefficients. The majorant is on one common polydisk. -/
theorem spatialCoefficient_hasSum {Y : Type*} {f : Y → (X → ℂ) → ℂ}
    {b : Y → ℝ} (hb : Summable b) {r : ℝ} (hr : 0 < r)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) (Metric.ball 0 r))
    (hbound : ∀ j u, u ∈ Metric.ball 0 r → ‖f j u‖ ≤ b j)
    (n : X → ℕ) (l : List X) :
    HasSum (fun j => spatialCoefficient n l (f j) 0)
      (spatialCoefficient n l (fun z => ∑' j, f j z) 0) := by
  induction l generalizing f b with
  | nil =>
    exact (hb.of_norm_bounded fun j => hbound j 0 (Metric.mem_ball_self hr)).hasSum
  | cons i l ih =>
    have he : take n i (fun z => ∑' j, f j z) =ᶠ[𝓝 0]
        (fun z => ∑' j, take n i (f j) z) := by
      filter_upwards [Metric.ball_mem_nhds (0 : X → ℂ) hr] with u hu
      exact (take_hasSum hb hf hbound n i hu hr).tsum_eq.symm
    have hh := ih (hb.div_const ((r / 2) ^ n i)) (fun j => take_analyticOnNhd n i hr (hf j))
      (fun j u hu => take_bound hr (hf j) (hbound j) n i hu)
    simp only [spatialCoefficient]
    rw [(spatialCoefficient_congr n l he).eq_of_nhds]
    exact hh

omit [Fintype X] in
/-- Fixed scalars commute with every spatial coefficient. -/
theorem spatialCoefficient_const_mul (n : X → ℕ) (l : List X) (c : ℂ)
    (f : (X → ℂ) → ℂ) :
    spatialCoefficient n l (fun u => c * f u) = fun u => c * spatialCoefficient n l f u := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    have he : take n i (fun u => c * f u) = fun u => c * take n i f u := by
      funext u
      simp only [take, coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]
    simp only [spatialCoefficient, he]
    exact ih _

omit [Fintype X] in
private theorem restriction_take_inl (n : X ⊕ X → ℕ) (i : X)
    (f : ((X ⊕ X) → ℂ) → ℂ) (u v : X → ℂ) :
    take n (.inl i) f (Sum.elim u v) =
      take (n ∘ Sum.inl) i (fun u' => f (Sum.elim u' v)) u := by
  unfold take
  refine congrArg (coefficient _) (funext fun t => congrArg f ?_)
  funext j
  cases j with
  | inl j => by_cases h : j = i <;> simp [h]
  | inr j => by_cases h : j = i <;> simp [h]

omit [Fintype X] in
private theorem restriction_take_inr (n : X ⊕ X → ℕ) (i : X)
    (f : ((X ⊕ X) → ℂ) → ℂ) (u v : X → ℂ) :
    take n (.inr i) f (Sum.elim u v) =
      take (n ∘ Sum.inr) i (fun v' => f (Sum.elim u v')) v := by
  unfold take
  refine congrArg (coefficient _) (funext fun t => congrArg f ?_)
  funext j
  cases j with
  | inl j => by_cases h : j = i <;> simp [h]
  | inr j => by_cases h : j = i <;> simp [h]

omit [Fintype X] in
private theorem restriction_spatial_inl (n : X ⊕ X → ℕ) (l : List X)
    (f : ((X ⊕ X) → ℂ) → ℂ) (u v : X → ℂ) :
    spatialCoefficient n (l.map Sum.inl) f (Sum.elim u v) =
      spatialCoefficient (n ∘ Sum.inl) l (fun u' => f (Sum.elim u' v)) u := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, spatialCoefficient]
    rw [ih, show (fun u' => take n (.inl i) f (Sum.elim u' v)) =
      take (n ∘ Sum.inl) i (fun u' => f (Sum.elim u' v)) from
        funext fun u' => restriction_take_inl n i f u' v]

omit [Fintype X] in
private theorem restriction_spatial_inr (n : X ⊕ X → ℕ) (l : List X)
    (f : ((X ⊕ X) → ℂ) → ℂ) (u v : X → ℂ) :
    spatialCoefficient n (l.map Sum.inr) f (Sum.elim u v) =
      spatialCoefficient (n ∘ Sum.inr) l (fun v' => f (Sum.elim u v')) v := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, spatialCoefficient]
    rw [ih, show (fun v' => take n (.inr i) f (Sum.elim u v')) =
      take (n ∘ Sum.inr) i (fun v' => f (Sum.elim u v')) from
        funext fun v' => restriction_take_inr n i f u v']

omit [Fintype X] in
private theorem split_spatial (n : X → ℕ) (l : List X)
    (f : ((X ⊕ X) → ℂ) → ℂ) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl) f 0 =
      spatialCoefficient n l (fun u => spatialCoefficient (fun _ => 1) l
        (fun v => f (Sum.elim u v)) 0) 0 := by
  have happ (k m : List (X ⊕ X)) (g : ((X ⊕ X) → ℂ) → ℂ) :
      spatialCoefficient (Sum.elim n (fun _ => 1)) (k ++ m) g =
        spatialCoefficient (Sum.elim n (fun _ => 1)) m
          (spatialCoefficient (Sum.elim n (fun _ => 1)) k g) := by
    induction k generalizing g with
    | nil => rfl
    | cons i k ih => exact ih _
  rw [happ]
  have h0 : (0 : (X ⊕ X) → ℂ) = Sum.elim (0 : X → ℂ) (0 : X → ℂ) := by
    ext i
    cases i <;> rfl
  conv_lhs => rw [h0, restriction_spatial_inl]
  change spatialCoefficient n l _ 0 = _
  exact congrArg (fun g => spatialCoefficient n l g 0)
    (funext fun u => restriction_spatial_inr _ l f u 0)

omit [Fintype X] in
private theorem mark_coefficient_eq_jet (l : List X) (hl : l.Nodup)
    (f : (X → ℂ) → ℂ) (u : X → ℂ) (hu : ∀ i ∈ l, u i = 0) :
    spatialCoefficient (fun _ => 1) l f u = coordinateJet l f u := by
  induction l generalizing f u with
  | nil => rfl
  | cons i l ih =>
    simp only [spatialCoefficient, coordinateJet]
    have hi := (List.nodup_cons.mp hl).1
    rw [ih (List.nodup_cons.mp hl).2 _ _ (fun j hj => hu j (List.mem_cons_of_mem _ hj))]
    let updateZero := fun v : X → ℂ => Function.update v i 0
    have hc (g : (X → ℂ) → ℂ) (j : X) (hj : j ≠ i) :
        coordinateDerivative j (g ∘ updateZero) = coordinateDerivative j g ∘ updateZero := by
      ext v
      simp only [coordinateDerivative, Function.comp_apply, updateZero, Function.update_of_ne hj]
      congr 1
      funext t
      rw [Function.update_comm hj]
    have hcomm (g : (X → ℂ) → ℂ) :
        coordinateJet l (g ∘ updateZero) = coordinateJet l g ∘ updateZero := by
      clear ih hl hu
      induction l generalizing g with
      | nil => rfl
      | cons j l ih =>
        have hj : j ≠ i := fun hj => hi (hj ▸ List.mem_cons_self)
        rw [coordinateJet, coordinateJet, hc g j hj, ih (fun ht => hi (List.mem_cons_of_mem _ ht))]
    have he : take (fun _ => 1) i f = coordinateDerivative i f ∘ updateZero := by
      ext v
      simp only [take, coefficient, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one,
        Function.comp_apply, coordinateDerivative, updateZero, Function.update_self,
        Function.update_idem]
    rw [he, hcomm]
    simp only [Function.comp_apply]
    rw [show updateZero u = u by
      simp only [updateZero, ← hu i List.mem_cons_self, Function.update_eq_self]]

omit [Fintype X] in
/-- With independent, distinct marks, degree one in each selected weight is
the native ordered mark derivative, followed by spatial Taylor extraction. -/
theorem spatialCoefficient_split_marks (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (f : ((X ⊕ X) → ℂ) → ℂ) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl) f 0 =
      spatialCoefficient n l (fun u => coordinateJet l (fun v => f (Sum.elim u v)) 0) 0 := by
  rw [split_spatial]
  congr 1
  funext u
  exact mark_coefficient_eq_jet l hl _ 0 (fun _ _ => rfl)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick
