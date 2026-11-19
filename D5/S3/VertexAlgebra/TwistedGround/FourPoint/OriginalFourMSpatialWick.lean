/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spatial Taylor extraction for simultaneous marked Gaussian products. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick

/-! Each term of the marked Wick recurrence uses the head coordinate in
one singleton or one pair. Spatial Taylor extraction distributes over this
recurrence and applies to the singleton and pair sources separately. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology ContDiff Matrix
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick

open NativeAffineExternalCoefficient OriginalChargedRowSource
open OriginalGaussianSewnAnalytic (coefficient)
open private occupation_erase occupation_count_sum from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private coefficient_add coefficient_mul_scalar from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor

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

private theorem inserts_analytic (i : X) (u : X → ℂ) :
    AnalyticAt ℂ (fun t : ℂ => inserts i t u) 0 := by
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases h : j = i
  · subst j
    simp only [inserts, Function.update_self]
    exact analyticAt_id
  · simp [inserts, Function.update_of_ne h, analyticAt_const]

private theorem inserts_zero_analytic (i : X) :
    AnalyticAt ℂ (inserts i 0) 0 := by
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases h : j = i
  · simp [h, inserts, analyticAt_const]
  · simp [inserts, Function.update_of_ne h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) j).analyticAt _

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
      simp [F, L, Q, inserts]
    · simp [F, L, Q, inserts, hj, Pi.single_eq_of_ne hj]
  have hm := congrArg (fun p : ContinuousMultilinearMap ℂ (fun _ : Fin (n i) => ℂ) ℂ =>
    p (fun _ => 1)) h
  rw [hEq, ← iteratedDeriv_eq_iteratedFDeriv] at hm
  change _ = iteratedFDeriv ℂ (n i) F 0 (fun _ => L 1) at hm
  have htrans : iteratedFDeriv ℂ (n i) F 0 = iteratedFDeriv ℂ (n i) f (Q u) := by
    simpa [F] using (iteratedFDeriv_comp_add_right (𝕜 := ℂ) (f := f) (n i) (Q u) 0)
  rw [htrans] at hm
  exact congrArg (fun a : ℂ => a / ((n i).factorial : ℂ)) hm.symm

private theorem take_congr (n : X → ℕ) (i : X) {f g : (X → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 0] g) : take n i f =ᶠ[𝓝 0] take n i g := by
  obtain ⟨s, hs, hopen, hzero⟩ := mem_nhds_iff.mp h
  have hmem : ∀ᶠ u : X → ℂ in 𝓝 0, inserts i 0 u ∈ s :=
    (inserts_zero_analytic i).continuousAt.tendsto.eventually (by
      simpa [inserts] using hopen.mem_nhds hzero)
  filter_upwards [hmem] with u hu
  have hslice : (fun t => f (inserts i t u)) =ᶠ[𝓝 0] (fun t => g (inserts i t u)) :=
    ((inserts_analytic i u).continuousAt.tendsto.eventually (hopen.mem_nhds hu)).mono
      (fun _ h => hs h)
  exact congrArg (fun a : ℂ => a / ((n i).factorial : ℂ)) (hslice.iteratedDeriv_eq _)

theorem spatialCoefficient_congr (n : X → ℕ) (l : List X) {f g : (X → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 0] g) : spatialCoefficient n l f =ᶠ[𝓝 0] spatialCoefficient n l g := by
  induction l generalizing f g with
  | nil => exact h
  | cons i l ih => exact ih (take_congr n i h)

private theorem take_add (n : X → ℕ) (i : X) {f g : (X → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    take n i (f + g) =ᶠ[𝓝 0] take n i f + take n i g := by
  have ht := (inserts_zero_analytic i).continuousAt.tendsto
  have hzero : inserts i 0 (0 : X → ℂ) = 0 := by simp [inserts]
  rw [hzero] at ht
  filter_upwards [ht.eventually hf.eventually_analyticAt, ht.eventually hg.eventually_analyticAt]
    with u hu hv
  exact coefficient_add (hu.comp_of_eq (inserts_analytic i u) rfl)
    (hv.comp_of_eq (inserts_analytic i u) rfl) (n i)

private theorem spatialCoefficient_add (n : X → ℕ) (l : List X) {f g : (X → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    spatialCoefficient n l (f + g) =ᶠ[𝓝 0] spatialCoefficient n l f +
      spatialCoefficient n l g := by
  induction l generalizing f g with
  | nil => rfl
  | cons i l ih =>
    exact (spatialCoefficient_congr n l (take_add n i hf hg)).trans
      (ih (take_analytic n i f hf) (take_analytic n i g hg))

private theorem spatialCoefficient_sum (n : X → ℕ) (l : List X)
    {Y : Type*} (s : Finset Y) (f : Y → (X → ℂ) → ℂ)
    (h : ∀ j ∈ s, AnalyticAt ℂ (f j) 0) :
    spatialCoefficient n l (∑ j ∈ s, f j) =ᶠ[𝓝 0]
      ∑ j ∈ s, spatialCoefficient n l (f j) := by
  classical
  have hzero : spatialCoefficient n l (fun _ => 0) = 0 := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      have he : take n i (fun _ => 0) = fun _ => 0 := by
        ext u
        simp [take, coefficient]
      simpa only [spatialCoefficient, he] using ih
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Filter.EventuallyEq.of_eq (show spatialCoefficient n l 0 = 0 from hzero)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : ∀ j ∈ s, AnalyticAt ℂ (f j) 0 :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hA : AnalyticAt ℂ (∑ j ∈ s, f j) 0 := by
      exact Finset.analyticAt_sum s hs
    exact (spatialCoefficient_add n l (h i (Finset.mem_insert_self i s)) hA).trans
      (Filter.EventuallyEq.rfl.add (ih hs))

private def ignores (f : (X → ℂ) → ℂ) (i : X) : Prop :=
  ∀ u t, f (Function.update u i t) = f u

private theorem take_ignores (n : X → ℕ) (i j : X) {f : (X → ℂ) → ℂ}
    (h : ignores f j) : ignores (take n i f) j := by
  intro u t
  unfold take
  congr 1
  funext v
  by_cases he : i = j
  · subst j
    rw [Function.update_idem]
  · rw [← Function.update_comm he, h]

private theorem take_mul_left (n : X → ℕ) (i : X) {f g : (X → ℂ) → ℂ}
    (h : ignores f i) : take n i (f * g) = f * take n i g := by
  funext u
  simp only [take, Pi.mul_apply, (show ∀ u t, f (Function.update u i t) = f u from h), coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem take_mul_right (n : X → ℕ) (i : X) {f g : (X → ℂ) → ℂ}
    (h : ignores g i) : take n i (f * g) = take n i f * g := by
  rw [mul_comm f, take_mul_left n i h, mul_comm]

private theorem spatialCoefficient_const_mul (n : X → ℕ) (l : List X) (c : ℂ)
    (f : (X → ℂ) → ℂ) :
    spatialCoefficient n l (fun u => c * f u) = fun u => c * spatialCoefficient n l f u := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    change spatialCoefficient n l (take n i ((fun _ => c) * f)) = _
    rw [take_mul_left n i (show ignores (fun _ => c) i from fun _ _ => rfl)]
    exact ih _

/-- A factor supported at a single occurrence travels through every other
selection unchanged. This also applies to the surviving variable of a pair. -/
private theorem spatialCoefficient_singleton (n : X → ℕ) (l : List X)
    (k : Fin l.length) (hnd : l.Nodup) (f : ℂ → ℂ) (g : (X → ℂ) → ℂ)
    (hg : ignores g (l.get k)) :
    spatialCoefficient n l ((fun u => f (u (l.get k))) * g) =
      (fun _ => coefficient (n (l.get k)) f) *
        spatialCoefficient n (l.eraseIdx k) g := by
  induction l generalizing g with
  | nil => exact Fin.elim0 k
  | cons i l ih =>
    revert hg
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hg
      simp only [List.get_cons_zero, List.eraseIdx_zero, List.tail_cons, Fin.val_zero, spatialCoefficient] at hg ⊢
      rw [take_mul_right n i hg]
      have h : take n i (fun u => f (u i)) = fun _ => coefficient (n i) f := by
        ext u
        simp [take]
      rw [h]
      exact spatialCoefficient_const_mul n l (coefficient (n i) f) g
    · intro hg
      have hne : i ≠ l.get j := fun h =>
        (List.nodup_cons.mp hnd).1 (h ▸ List.get_mem l j)
      simp only [List.get_cons_succ', List.eraseIdx, Fin.val_succ, spatialCoefficient] at hg ⊢
      have hf : ignores (fun u => f (u (l.get j))) i := fun u t => by
        dsimp only
        rw [Function.update_of_ne hne.symm]
      rw [take_mul_left n i hf]
      exact ih j (List.nodup_cons.mp hnd).2 _ (take_ignores n i _ hg)


private theorem affineMoment_marks (A : Matrix X X ℂ) (mu : X → ℂ)
    (hs : ∀ i j, A i j = A j i) (i : X) (l : List X) :
    affineMoment A mu (jetOccupation (i :: l)) =
      mu i * affineMoment A mu (jetOccupation l) +
        ∑ k : Fin l.length, A i (l.get k) * affineMoment A mu (jetOccupation (l.eraseIdx k)) := by
  rw [jetOccupation, affineMoment_step A mu hs]
  congr 1
  simp_rw [mul_assoc]
  rw [occupation_count_sum]
  apply Finset.sum_congr rfl
  intro k _
  conv_lhs => rw [← occupation_erase l k, add_tsub_cancel_right]

private def wick (K : X → X → ℂ → ℂ → ℂ) (m : X → ℂ → ℂ)
    (l : List X) (u : X → ℂ) : ℂ :=
  affineMoment (fun i j => K i j (u i) (u j)) (fun i => m i (u i)) (jetOccupation l)

private theorem wick_step (K : X → X → ℂ → ℂ → ℂ) (m : X → ℂ → ℂ)
    (hK : ∀ u : X → ℂ, ∀ i j, K i j (u i) (u j) = K j i (u j) (u i))
    (i : X) (l : List X) :
    wick K m (i :: l) = (fun u => m i (u i)) * wick K m l +
      ∑ k : Fin l.length, (fun u => K i (l.get k) (u i) (u (l.get k))) *
        wick K m (l.eraseIdx k) := by
  funext u
  simp only [wick, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  exact affineMoment_marks _ _ (hK u) _ _

private theorem wick_ignores (K : X → X → ℂ → ℂ → ℂ) (m : X → ℂ → ℂ)
    (hs : ∀ u : X → ℂ, ∀ i j, K i j (u i) (u j) = K j i (u j) (u i))
    (l : List X) (i : X) (hi : i ∉ l) : ignores (wick K m l) i := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h N ih =>
    cases l with
    | nil =>
      intro u t
      unfold wick
      rw [jetOccupation]
      exact (affineMoment_zero (fun i₁ j => K i₁ j (Function.update u i t i₁) (Function.update u i t j))
        (fun i₁ => m i₁ (Function.update u i t i₁))).trans (affineMoment_zero _ _).symm
    | cons j l =>
      obtain ⟨hij, hi⟩ : i ≠ j ∧ i ∉ l := by simpa [List.mem_cons, eq_comm] using hi
      have hs₁ : l.length < N := by simp at hn; omega
      intro u t
      rw [wick_step K m hs]
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Function.update_of_ne hij.symm]
      rw [ih _ hs₁ l hi rfl u t]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have hn : l.get k ≠ i := fun h => hi (h ▸ List.get_mem l k)
      rw [Function.update_of_ne hn, ih _ ((List.length_eraseIdx_le ..).trans_lt hs₁) _
        (fun h => hi (List.eraseIdx_subset h)) rfl u t]

private theorem wick_analytic (K : X → X → ℂ → ℂ → ℂ) (m : X → ℂ → ℂ)
    (hs : ∀ u : X → ℂ, ∀ i j, K i j (u i) (u j) = K j i (u j) (u i))
    (hK : ∀ i j, AnalyticAt ℂ (fun uv : ℂ × ℂ => K i j uv.1 uv.2) (0, 0))
    (hm : ∀ i, AnalyticAt ℂ (m i) 0) (l : List X) : AnalyticAt ℂ (wick K m l) 0 := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h N ih =>
    cases l with
    | nil =>
      have he : wick K m [] = fun _ => 1 := by
        funext u
        unfold wick
        rw [jetOccupation]
        exact affineMoment_zero _ _
      rw [he]
      exact analyticAt_const
    | cons i l =>
      have hs₁ : l.length < N := by simp at hn; omega
      have hp (i : X) : AnalyticAt ℂ (fun u : X → ℂ => u i) 0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) i).analyticAt _
      rw [wick_step K m hs]
      apply AnalyticAt.add
      · exact ((hm i).comp_of_eq (hp i) rfl).mul (ih _ hs₁ l rfl)
      · rw [show (∑ k : Fin l.length, (fun u => K i (l.get k) (u i) (u (l.get k))) *
            wick K m (l.eraseIdx k)) =
          fun u => ∑ k : Fin l.length, K i (l.get k) (u i) (u (l.get k)) *
            wick K m (l.eraseIdx k) u by ext u; simp [Finset.sum_apply]]
        apply Finset.analyticAt_fun_sum
        intro k _
        exact ((hK i (l.get k)).comp_of_eq ((hp i).prod (hp (l.get k))) rfl).mul
          (ih _ ((List.length_eraseIdx_le ..).trans_lt hs₁) _ rfl)

private theorem take_sum (n : X → ℕ) (i : X) {Y : Type*}
    (s : Finset Y) (f : Y → (X → ℂ) → ℂ) (h : ∀ j ∈ s, AnalyticAt ℂ (f j) 0) :
    take n i (∑ j ∈ s, f j) =ᶠ[𝓝 0] ∑ j ∈ s, take n i (f j) := by
  have he := spatialCoefficient_sum n [i] s f h
  simpa only [spatialCoefficient] using he

private theorem analytic_projection (i : X) :
    AnalyticAt ℂ (fun u : X → ℂ => u i) 0 :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) i).analyticAt _

/-- Wick contraction commutes with the simultaneous ordinary spatial Taylor
coefficient. Every marked position is independent, including occurrences
bearing equal puncture, colour, or mode data. -/
theorem spatial_marked_gaussian (K : X → X → ℂ → ℂ → ℂ) (m : X → ℂ → ℂ)
    (hs : ∀ u : X → ℂ, ∀ i j, K i j (u i) (u j) = K j i (u j) (u i))
    (hK : ∀ i j, AnalyticAt ℂ (fun uv : ℂ × ℂ => K i j uv.1 uv.2) (0, 0))
    (hm : ∀ i, AnalyticAt ℂ (m i) 0)
    (n : X → ℕ)
    (hsym : ∀ i j, (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
      (coefficient (n i) fun u => coefficient (n j) fun v => K j i v u))
    (l : List X) (hl : l.Nodup) :
    let mark := fun (u : X → ℂ) => coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) +
        ∑ i, m i (u i) * v i)) 0
    let A : Matrix X X ℂ := fun i j =>
      coefficient (n j) fun v => coefficient (n i) fun u => K i j u v
    let mu := fun i => coefficient (n i) (m i)
    spatialCoefficient n l mark 0 = affineMoment A mu (jetOccupation l) := by
  classical
  dsimp only
  have hmark : (fun (u : X → ℂ) => coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) +
        ∑ i, m i (u i) * v i)) 0) = wick K m l := by
    funext u
    have hj := OriginalFourMPhysicalCovariance.marked_gaussian_jet (id : X → X) l
      (fun i j => K i j (u i) (u j)) (fun i => m i (u i)) (hs u)
    simp only [id_eq, List.map_id] at hj
    exact hj.trans (affineMoment_coefficient _ _ _).symm
  rw [hmark]
  clear hmark
  let A : Matrix X X ℂ := fun i j =>
    coefficient (n j) fun v => coefficient (n i) fun u => K i j u v
  let mu := fun i => coefficient (n i) (m i)
  change spatialCoefficient n l (wick K m l) 0 = affineMoment A mu (jetOccupation l)
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h N ih =>
    cases l with
    | nil =>
      rw [spatialCoefficient, wick, jetOccupation]
      exact (affineMoment_zero _ _).trans (affineMoment_zero _ _).symm
    | cons i l =>
      obtain ⟨hin, htail⟩ := List.nodup_cons.mp hl
      have hs₁ : l.length < N := by simp at hn; omega
      let F : (X → ℂ) → ℂ := (fun u => m i (u i)) * wick K m l
      let G (k : Fin l.length) : (X → ℂ) → ℂ :=
        (fun u => K i (l.get k) (u i) (u (l.get k))) * wick K m (l.eraseIdx k)
      have hF : AnalyticAt ℂ F 0 := ((hm i).comp_of_eq (analytic_projection i) rfl).mul
        (wick_analytic K m hs hK hm l)
      have hG (k : Fin l.length) : AnalyticAt ℂ (G k) 0 :=
        ((hK i (l.get k)).comp_of_eq ((analytic_projection i).prod (analytic_projection (l.get k))) rfl).mul
          (wick_analytic K m hs hK hm (l.eraseIdx k))
      have hsum : AnalyticAt ℂ (∑ k, G k) 0 := by
        exact Finset.analyticAt_sum Finset.univ (fun k _ => hG k)
      have hFG : take n i (F + ∑ k, G k) =ᶠ[𝓝 0] take n i F + ∑ k, take n i (G k) :=
        (take_add n i hF hsum).trans (Filter.EventuallyEq.rfl.add
          (take_sum n i Finset.univ G (fun k _ => hG k)))
      have hcoefF : take n i F = (fun _ => mu i) * wick K m l := by
        rw [show F = _ from rfl, take_mul_right n i (wick_ignores K m hs l i hin)]
        congr 1
        funext u
        simp [take, mu]
      have hcoefG (k : Fin l.length) :
          take n i (G k) =
            (fun u => coefficient (n i) fun v => K i (l.get k) v (u (l.get k))) *
              wick K m (l.eraseIdx k) := by
        rw [show G k = _ from rfl, take_mul_right n i (wick_ignores K m hs _ i (fun h =>
          hin (List.eraseIdx_subset h)))]
        congr 1
        funext u
        have hne : l.get k ≠ i := fun h => hin (h ▸ List.get_mem l k)
        unfold take
        congr 1
        funext v
        dsimp only
        rw [Function.update_self, Function.update_of_ne hne]
      have hsplit := (spatialCoefficient_congr n l hFG).trans
        ((spatialCoefficient_add n l (take_analytic n i F hF)
          (by
            exact Finset.analyticAt_sum Finset.univ
              (fun k _ => take_analytic n i (G k) (hG k)))).trans
          (Filter.EventuallyEq.rfl.add (spatialCoefficient_sum n l Finset.univ
            (fun k => take n i (G k)) (fun k _ => take_analytic n i (G k) (hG k)))))
      rw [spatialCoefficient, wick_step K m hs]
      change spatialCoefficient n l (take n i (F + ∑ k, G k)) 0 = _
      have hsingle : spatialCoefficient n l ((fun _ => mu i) * wick K m l) 0 =
          mu i * spatialCoefficient n l (wick K m l) 0 :=
        congrFun (spatialCoefficient_const_mul n l (mu i) (wick K m l)) 0
      rw [hsplit.eq_of_nhds, Pi.add_apply, Finset.sum_apply, hcoefF, hsingle,
        ih _ hs₁ l htail rfl, affineMoment_marks A mu hsym]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have hnodup : (l.eraseIdx k).Nodup := htail.sublist (List.eraseIdx_sublist ..)
      have hignore : ignores (wick K m (l.eraseIdx k)) (l.get k) :=
        wick_ignores K m hs _ _ (by
          rw [← htail.erase_get k]
          exact htail.not_mem_erase)
      have hpair := spatialCoefficient_singleton n l k htail
        (fun t => coefficient (n i) (fun v => K i (l.get k) v t))
        (wick K m (l.eraseIdx k)) hignore
      rw [hcoefG, hpair, Pi.mul_apply,
        ih _ ((List.length_eraseIdx_le ..).trans_lt hs₁) _ hnodup rfl]


open LatticeGeneratingFieldLocality OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags physicalSource)
open OriginalFourMPhysicalCovariance (physicalCovariance)
open OriginalFourMSignedOverlap (chartCovariance)
open OriginalFourMJointWick
open OriginalGaussianExternalBlocks (explicitEffectiveKernel)
open OriginalGaussianSewnAnalytic (explicitMean)
open OriginalGaussianExternalSignedCandidate (rho rationalT cauchy G E N K)
open OriginalFourMChartProduct (native_rank24_determinant)
open FactorialFockMetric (weight)
open private same_flags jac slotCorrection physicalCovariance_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private chartPeriod freeCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private physicalSource_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
open private chartW chosenChartSource from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private selected_covariance_eq boundedWord externalLabel gramCorrection_symm creatorMatrix gramCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private explicit_covariance_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation

private theorem rho_swap (e f : Bool) (u v : ℂ) :
    rho e f u v = rho f e v u := by
  cases e <;> cases f <;> simp [rho, add_comm, mul_comm]

private theorem cauchy_swap (e f : Bool) (u v : ℂ) :
    cauchy e f u v = cauchy f e v u := by
  rw [cauchy, cauchy, rho_swap e f]
  congr 2
  cases e <;> cases f <;> simp [G, mul_comm] <;> ring

private theorem rationalT_swap (e f : Bool) (u v r : ℂ) :
    rationalT e f u v r = rationalT f e v u r := by
  have hE : E e f u v r = E f e v u r := by
    cases e <;> cases f <;> simp [E, K, mul_comm]
  have hN : N e f u v r = N f e v u r := by
    cases e <;> cases f <;> simp [N, add_comm, mul_comm, mul_left_comm]
  rw [rationalT, rationalT, hE, hN]
  ring

private theorem physical_covariance_swap (upperA : Bool) (c : Chart) (x : ℝ)
    (i j : Puncture) (u v : ℂ) :
    physicalCovariance upperA c x i j u v = physicalCovariance upperA c x j i v u := by
  have hC (l k e f : Bool) (u v : ℂ) :
      chartCovariance upperA c x l k e f u v = chartCovariance upperA c x k l f e v u := by
    unfold chartCovariance
    dsimp only
    by_cases h : l = k
    · simp only [h, ite_true, rho_swap e f, cauchy_swap e f]
      have hh : (if e = f then (0 : ℂ) else cauchy f e v u) =
          if f = e then 0 else cauchy f e v u := by simp [eq_comm]
      rw [hh, add_comm (chartW c x e u)]
      ring_nf
    · simp only [h, Ne.symm h, ite_false, rationalT_swap e f]
      ring
  have hS : slotCorrection c x i j u v = slotCorrection c x j i v u := by
    by_cases h : i = j
    · subst j
      simp only [slotCorrection, and_self, ite_true, freeCorrection]
      ring_nf
    · have hn : ¬ ((flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2) :=
        fun hf => h (same_flags c hf)
      have hn' : ¬ ((flags c j).1 = (flags c i).1 ∧ (flags c j).2 = (flags c i).2) :=
        fun hf => h (same_flags c hf).symm
      simp [slotCorrection, hn, hn']
  unfold physicalCovariance
  rw [hC, hS, mul_comm (jac c x i u) (jac c x j v)]

private def physicalEntry (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (i j : X) (u v : ℂ) : ℂ :=
  (D.G (colour i) (colour j) : ℂ) * physicalCovariance upperA c x (slot i) (slot j) u v

private def physicalMean (D : LatticeData) (q : Charge D) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (i : X) (u : ℂ) : ℂ :=
  -(bilinear D (unitCharge D (colour i)) q : ℂ) *
    physicalSource c x (slot i) u / chartPeriod upperA c x

/-- The ordinary spatial coefficient of one simultaneous physical Gaussian
summand on either radial chart is the literal factorial native Gaussian
occupation readout after the four actual inverse-lowered words. -/
theorem radial_spatial_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (ls : List (Puncture × List X)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) (hl : (ls.flatMap Prod.snd).Nodup) :
    let l := ls.flatMap Prod.snd
    let colour := fun i => (mode i).1
    let K := physicalEntry D upperA c x slot colour
    let mu := physicalMean D q upperA c x slot colour
    let P := (ls.map (fun entry => boundedWord D N c x entry.1 (entry.2.map mode))).prod
    spatialCoefficient (fun i => (mode i).2) l (fun u => coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) + ∑ i, mu i (u i) * v i)) 0) 0 =
      ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) *
        affineCoefficient (explicitEffectiveKernel D (externalLabel D N) w)
          (explicitMean D q (externalLabel D N) w) e) := by
  classical
  dsimp only
  let K := physicalEntry D upperA c x slot (fun i => (mode i).1)
  let m := physicalMean D q upperA c x slot (fun i => (mode i).1)
  let n := fun i => (mode i).2
  let l := ls.flatMap Prod.snd
  have hK (i j : X) : AnalyticAt ℂ (fun uv : ℂ × ℂ => K i j uv.1 uv.2) (0,0) :=
    analyticAt_const.mul (physicalCovariance_analytic upperA hx hx₁ c (slot i) (slot j))
  have hm (i : X) : AnalyticAt ℂ (m i) 0 :=
    (analyticAt_const.mul (physicalSource_analytic hx hx₁ c (slot i))).div_const
  have hs (u : X → ℂ) (i j : X) : K i j (u i) (u j) = K j i (u j) (u i) := by
    simp only [K, physicalEntry]
    rw [D.symmetric, physical_covariance_swap]
  have hscalar (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
        (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
          (fun v => coefficient (mode i).2 (fun u =>
            physicalCovariance upperA c x (slot i) (slot j) u v)) := by
    simp only [K, physicalEntry, n, coefficient_mul_scalar]
  have hcoeff (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
        (NativeAffineTransport.transportCovariance (creatorMatrix D N c x slot mode bound)
          (explicitEffectiveKernel D (externalLabel D N) w) +
          gramCorrection D c x slot mode) i j :=
    (hscalar i j).trans (selected_covariance_eq D hu N hx hx₁ upperA c hc hw hwc slot mode bound i j)
  have hsym (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
        (coefficient (n i) fun u => coefficient (n j) fun v => K j i v u) := by
    rw [hcoeff, hcoeff, Matrix.add_apply, Matrix.add_apply,
      NativeAffineTransport.transportCovariance_symm _ _
        (explicit_covariance_symmetric D _ hw) i j, gramCorrection_symm D hu c x slot mode i j]
  rw [spatial_marked_gaussian K m hs hK hm n hsym l hl]
  have h := radial_physical_selected_occupation D hu q N hx hx₁ upperA c hc hw hwc slot mode bound
    ls hslots hv
  dsimp only at h
  let B : Matrix X X ℂ := fun i j => (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (n j)
    (fun v => coefficient (mode i).2 (fun u => physicalCovariance upperA c x (slot i) (slot j) u v))
  have hB (i j : X) : B i j = B j i := by
    exact (hscalar i j).symm.trans ((hsym i j).trans (hscalar j i))
  have hj := OriginalFourMPhysicalCovariance.marked_gaussian_jet (id : X → X) l B
    (fun i => coefficient (n i) (m i)) hB
  simp only [id_eq, List.map_id, B, n, m, physicalMean, l] at hj
  erw [hj] at h
  let A : Matrix X X ℂ := fun i j => coefficient (n j) fun v => coefficient (n i) fun u => K i j u v
  let mu := fun i => coefficient (n i) (m i)
  change affineMoment A mu (jetOccupation l) = _
  have hAB : A = B := by
    funext i j
    exact hscalar i j
  rw [hAB]
  exact (affineMoment_coefficient B mu (jetOccupation l)).trans h

open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMShiftedTheta (chargeTheta_eq_charge_sum)
open private nativeSample from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalProduct
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private gaussianExponent gram sourceVector chartTau linear_source thetaSource from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct

set_option maxHeartbeats 600000 in
/-- The actual physical product on each chart is the simultaneous marked
Gaussian with the original mod-two charge fiber and period normalization.
The relative signs multiply the occurrence weights before marking. -/
theorem physical_product_marked_charge_fiber (D : LatticeData) (hu : IsUnit D.G.det)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    (x : ℝ) (hp : chartPeriod upperA c x ≠ 0) (a : ModTwoCharge D) (u v : X → ℂ) :
    let v' := fun i => relative c (slot i) * v i
    let K := physicalEntry D upperA c x slot colour
    let m := fun q => physicalMean D q upperA c x slot colour
    physicalProduct D hu slot colour upperA x c a u v =
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        ∑' q : {q : Charge D // reduceCharge D q = a},
          Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
            (bilinear D q.val q.val : ℂ) / 2) *
          Complex.exp ((1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v' i * v' j) +
            ∑ i, m q.val i (u i) * v' i) := by
  classical
  dsimp only
  unfold physicalProduct
  dsimp only
  rw [chargeTheta_eq_charge_sum, mul_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro q
  have hQ :
      gaussianExponent D (fun i => nativeSample D x (slot i) (colour i) (u i)) v
        (fun i j => relative c (slot i) * relative c (slot j) *
          physicalCovariance upperA c x (slot i) (slot j) (u i) (u j)) =
      (1 / 2 : ℂ) * ∑ i, ∑ j, physicalEntry D upperA c x slot colour i j (u i) (u j) *
        (relative c (slot i) * v i) * (relative c (slot j) * v j) := by
    rw [gaussianExponent, div_eq_mul_inv, one_div, mul_comm (2 : ℂ)⁻¹]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [gram, Matrix.map_apply, nativeSample, physicalEntry]
    ring
  have hL := linear_source D (fun i => nativeSample D x (slot i) (colour i) (u i)) v
    (fun i => relative c (slot i) * physicalSource c x (slot i) (u i)) q.val hp
  have hlinear : (∑ i, v i * (-(bilinear D (unitCharge D (colour i)) q.val : ℂ) *
        (relative c (slot i) * physicalSource c x (slot i) (u i)) / chartPeriod upperA c x)) =
      ∑ i, physicalMean D q.val upperA c x slot colour i (u i) *
        (relative c (slot i) * v i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [physicalMean]
    ring
  have hL' : 2 * (Real.pi : ℂ) * Complex.I *
      ((D.G.map (Int.cast : ℤ → ℂ) *ᵥ (fun i => (q.val i : ℂ))) ⬝ᵥ
        thetaSource D (chartPeriod upperA c x)
          (sourceVector D (fun i => nativeSample D x (slot i) (colour i) (u i)) v
            (fun i => relative c (slot i) * physicalSource c x (slot i) (u i)))) =
      ∑ i, physicalMean D q.val upperA c x slot colour i (u i) *
        (relative c (slot i) * v i) := hL.trans hlinear
  erw [hQ, hL']
  simp only [Complex.exp_add]
  ring

open LatticePositiveEnergy (chargeEnergy chargeEnergy_nonneg two_chargeEnergy)
open LatticeHalfFockChargedTensorCoefficients (chargeScalar chargeNorm)
open OriginalGaussianSewnAnalytic (sewn)
open OriginalGaussianSourceMeans (sourceConstant)
open OriginalGaussianDeterminant (gaussianLogDet)
open OriginalGaussianExternalBlocks (External)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open D5.S3.Analytic.OriginalHalfBinomialNome (Q0)
open private nome_square_source from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal
open private chargeScalar_pair from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

/-- At an actual radial nome, the rank-24 period normalization for each
charge summand is the original sewn Gaussian determinant times the
cubed complementary parameter. The lattice energy and scalar are the
ones in the original charge sum. -/
private theorem rank24_marked_charge_normalization (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (q : Charge D) (c : Chart) (hc : c = .A ∨ c = .B) (upperA : Bool) (x : ℝ)
    {w : ℂ} (hw : ‖w‖ < 1) (hwc : w ^ 2 = parameter c x)
    (hNome : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x) = Q0 (w ^ 2))
    {J : Type*} [Fintype J] [DecidableEq J] (label : J → External D) (e : (J ⊕ J) →₀ ℕ) :
    (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
        (bilinear D q q : ℂ) / 2) *
      affineCoefficient (explicitEffectiveKernel D label w) (explicitMean D q label w) e =
    (1 - w ^ 2) ^ (3 : ℕ) * ((chargeScalar D q * chargeScalar D (-q)) *
      w ^ (2 * (chargeEnergy D q).toNat) * sewn D q label e w) := by
  let m := (chargeEnergy D q).toNat
  have hm : (m : ℤ) = chargeEnergy D q := Int.toNat_of_nonneg (chargeEnergy_nonneg D hD q)
  have hn : (bilinear D q q : ℂ) = 2 * (m : ℂ) := by
    have ht : bilinear D q q = 2 * (m : ℤ) := by
      rw [hm, two_chargeEnergy]
    exact_mod_cast ht
  have hr : chartPeriod upperA c x = slitPeriod (w ^ 2) := by
    rw [hwc]
    rcases hc with rfl | rfl <;> rfl
  have hs : (16 : ℂ) ^ (-chargeEnergy D q) = ((16 : ℂ) ^ m)⁻¹ := by
    rw [← hm, zpow_neg, zpow_natCast]
  have h0 : 1 - w ^ 2 ≠ 0 := by
    have hw2 : ‖w ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hw2
    exact (lt_irrefl _) hw2
  have hname : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
      (bilinear D q q : ℂ) / 2) = Q0 (w ^ 2)^m := by
    rw [hn, show (Real.pi : ℂ) * Complex.I * chartTau upperA c x * (2 * (m : ℂ)) / 2 =
      (m : ℂ) * ((Real.pi : ℂ) * Complex.I * chartTau upperA c x) by ring,
      Complex.exp_nat_mul, hNome]
  have hQ := nome_square_source (by simpa [Metric.mem_ball] using hw)
  have hdet : (1 - w ^ 2) ^ (3 : ℕ) *
      Complex.exp (-(D.rank : ℂ) / 2 * gaussianLogDet w) =
      (slitPeriod (w ^ 2) ^ (12 : ℕ))⁻¹ := by
    rw [h24, show -((24 : ℕ) : ℂ) / 2 = -12 by norm_num,
      native_rank24_determinant hw, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 h0), one_mul]
  have hnorm : (chargeNorm D q : ℂ) = 2 * (m : ℂ) := hn
  rw [hr, hname, hQ, sewn, chargeScalar_pair, hs, hnorm,
    div_pow, mul_pow, ← pow_mul, ← Complex.exp_nat_mul,
    show (m : ℂ) * (2 * sourceConstant w) = 2 * (m : ℂ) * sourceConstant w by ring]
  calc
    _ = ((16 : ℂ) ^ m)⁻¹ * w ^ (2 * m) *
        ((slitPeriod (w ^ 2) ^ (12 : ℕ))⁻¹ *
          Complex.exp (2 * (m : ℂ) * sourceConstant w) *
          affineCoefficient (explicitEffectiveKernel D label w) (explicitMean D q label w) e) := by
          ring
    _ = _ := by rw [← hdet]; ring


private theorem coordinateJet_scale (s : X → ℂ) (l : List X) (f : (X → ℂ) → ℂ)
    (v : X → ℂ) :
    coordinateJet l (fun x => f (fun i => s i * x i)) v =
      (l.map s).prod * coordinateJet l f (fun i => s i * v i) := by
  have hder (i : X) (f : (X → ℂ) → ℂ) :
      coordinateDerivative i (fun x => f (fun j => s j * x j)) = fun v =>
        s i * coordinateDerivative i f (fun j => s j * v j) := by
    funext v
    have hup (t : ℂ) :
        (fun j => s j * Function.update v i t j) =
          Function.update (fun j => s j * v j) i (s i * t) := by
      funext j
      by_cases h : j = i
      · subst j
        simp
      · simp [Function.update_of_ne h]
    unfold coordinateDerivative
    simp_rw [hup]
    simpa only [smul_eq_mul] using
      deriv_comp_mul_left (s i) (fun t => f (Function.update (fun j => s j * v j) i t)) (v i)
  induction l generalizing f with
  | nil => simp [coordinateJet]
  | cons i l ih =>
    simp only [coordinateJet, hder, List.map_cons, List.prod_cons]
    rw [coordinateJet_const_mul]
    dsimp only
    rw [ih (coordinateDerivative i f)]
    ring

/-- A single actual charge summand on radial A or B has the native sewn
readout after its simultaneous marked spatial extraction. The relative
puncture signs, rank-24 determinant, charge weight and period are explicit. -/
theorem radial_spatial_sewn_charge (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (q : Charge D) (N : ℕ) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (upperA : Bool)
    (c : Chart) (hc : c = .A ∨ c = .B) {w : ℂ} (hw : ‖w‖ < 1)
    (hwc : w ^ 2 = parameter c x)
    (hNome : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x) = Q0 (w ^ 2))
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (ls : List (Puncture × List X)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) (hl : (ls.flatMap Prod.snd).Nodup) :
    let l := ls.flatMap Prod.snd
    let colour := fun i => (mode i).1
    let sign := fun i => relative c (slot i)
    let K := physicalEntry D upperA c x slot colour
    let m := physicalMean D q upperA c x slot colour
    let P := (ls.map (fun entry => boundedWord D N c x entry.1 (entry.2.map mode))).prod
    spatialCoefficient (fun i => (mode i).2) l (fun u =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      coordinateJet l (fun v => Complex.exp (
        (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * (sign i * v i) * (sign j * v j)) +
          ∑ i, m i (u i) * (sign i * v i))) 0) 0 =
      (l.map sign).prod * (1 - w ^ 2) ^ (3 : ℕ) *
        ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) *
          ((chargeScalar D q * chargeScalar D (-q)) * w ^ (2 * (chargeEnergy D q).toNat) *
            sewn D q (externalLabel D N) e w)) := by
  classical
  dsimp only
  let l := ls.flatMap Prod.snd
  let sign := fun i => relative c (slot i)
  let K := physicalEntry D upperA c x slot (fun i => (mode i).1)
  let m := physicalMean D q upperA c x slot (fun i => (mode i).1)
  let p := (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2)
  let f (u v : X → ℂ) := Complex.exp (
    (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) + ∑ i, m i (u i) * v i)
  have he (u : X → ℂ) :
      coordinateJet l (fun v => f u (fun i => sign i * v i)) 0 =
        (l.map sign).prod * coordinateJet l (f u) 0 := by
    simpa only [Pi.zero_apply, mul_zero, ← Pi.zero_def] using coordinateJet_scale sign l (f u) 0
  change spatialCoefficient (fun i => (mode i).2) l
    (fun u => p * coordinateJet l (fun v => f u (fun i => sign i * v i)) 0) 0 = _
  simp only [he, spatialCoefficient_const_mul]
  have h := radial_spatial_occupation D hu q N hx hx₁ upperA c hc hw hwc slot mode bound ls hslots hv hl
  change spatialCoefficient (fun i => (mode i).2) l (fun u => coordinateJet l (f u) 0) 0 = _ at h
  rw [h, ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hb := rank24_marked_charge_normalization D hD h24 q c hc upperA x hw hwc hNome
    (externalLabel D N) e
  change p * _ = _ at hb
  linear_combination (l.map sign).prod * ((List.map
    (fun entry => boundedWord D N c x entry.1 (entry.2.map mode)) ls).prod.coeff e) *
      (weight e : ℂ) * hb

open LatticeDiscriminantTheta (gramReal)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMPhysicalProduct (physical_chart_product)

/-- The simultaneous Taylor coefficients of the actual physical products
inherit the real-overlap sector identities. Analyticity is required at
the joint origin of the spatial coordinates and the marking weights. -/
theorem physical_chart_coefficient_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (n : X ⊕ X → ℕ) (l : List (X ⊕ X))
    (hf : ∀ c a, AnalyticAt ℂ (fun z : (X ⊕ X) → ℂ =>
        physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0)
    (a : ModTwoCharge D) :
    let jet := fun c a => spatialCoefficient n l (fun z : (X ⊕ X) → ℂ =>
        physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
    jet .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * jet .A b) ∧
    jet .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * jet .A b) := by
  classical
  dsimp only
  let F (c : Chart) (a : ModTwoCharge D) (z : (X ⊕ X) → ℂ) :=
    physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)
  let T := fun f => spatialCoefficient n l f 0
  change T (F .D a) = _ ∧ T (F .B a) = _
  let L := Pi.compRightL ℂ (fun _ : X ⊕ X => ℂ) (Sum.inl : X → X ⊕ X)
  have he := physical_chart_product D hu hD hr slot colour upperA hx hx₁ hwA hw
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (L.continuous.continuousAt (x := 0)).tendsto
  have h := hL.eventually he
  have hD' : F .D a =ᶠ[𝓝 0] (fun z => ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
      ∑ b, fourierSign D a b * F .A b z) := by
    filter_upwards [h] with u hu
    exact (hu (u ∘ Sum.inr) a).1
  have hB' : F .B a =ᶠ[𝓝 0] (fun z => (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * F .A b z)) := by
    filter_upwards [h] with u hu
    exact (hu (u ∘ Sum.inr) a).2
  have hsum (k : ModTwoCharge D → ℂ) :
      T (fun z => ∑ b, k b * F .A b z) = ∑ b, k b * T (F .A b) := by
    have hk (b : ModTwoCharge D) : AnalyticAt ℂ (fun z => k b * F .A b z) 0 :=
      analyticAt_const.mul (hf .A b)
    have he := spatialCoefficient_sum n l Finset.univ (fun b z => k b * F .A b z) (fun b _ => hk b)
    have he' := he.eq_of_nhds
    have heq : (∑ j, fun z => k j * F .A j z) = fun z => ∑ j, k j * F .A j z := by
      funext z
      simp only [Finset.sum_apply]
    rw [heq] at he'
    simpa only [T, Finset.sum_apply, spatialCoefficient_const_mul] using he'
  constructor
  · rw [show T (F .D a) = _ from (spatialCoefficient_congr n l hD').eq_of_nhds]
    change spatialCoefficient n l (fun z => ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
      ∑ b, fourierSign D a b * F .A b z) 0 = _
    rw [spatialCoefficient_const_mul]
    simpa only [T, F] using congrArg (fun t : ℂ => ((2 : ℂ) ^ (12 : ℕ))⁻¹ * t) (hsum (fourierSign D a))
  · rw [show T (F .B a) = _ from (spatialCoefficient_congr n l hB').eq_of_nhds]
    change spatialCoefficient n l (fun z => (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * F .A b z)) 0 = _
    rw [spatialCoefficient_const_mul, spatialCoefficient_const_mul]
    simpa only [T, F] using congrArg (fun t : ℂ => (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * t)) (hsum (fun b => fourierSign D a b * quadraticSign D b))

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick
