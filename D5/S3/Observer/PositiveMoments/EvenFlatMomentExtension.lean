/- GID: D5/S3/Observer/PositiveMoments/EvenFlatMomentExtension
   generality: G
   mirror-B: D5/B/S3/Observer/PositiveMoments/EvenFlatMomentExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flat even operator moments have a positive realization and a unique selfadjoint future. -/

import D5.S3.Observer.PositiveMoments.PrefixFutureUniqueness

/-! Finite-dimensional real inner-product spaces, including zero-dimensional carriers. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped InnerProductSpace MatrixOrder
open LinearMap
namespace D5.S3.Observer.PositiveMoments.EvenFlatMomentExtension
open D5.S3.Observer.PositiveMoments.PrefixPositiveRealization
open D5.S3.Observer.PositiveMoments.PrefixFutureUniqueness
variable {P E F U V : Type}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem low_span_of_flat (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v))
    (hspan : Submodule.span ℝ (⋃ i, Set.range (e i)) = ⊤)
    (hrank : Module.finrank ℝ (momentBlock M (r + 1) 0).range =
      Module.finrank ℝ (momentBlock M r 0).range) :
    Submodule.span ℝ (⋃ j : Fin r, Set.range (e j.castSucc)) = ⊤ := by
  let low : Fin r → U →ₗ[ℝ] E := fun j => e j.castSucc
  have hg0 := synthesis_gram (r + 1) M e hg
  have hg1 := synthesis_gram r M low (by intro i j u v;exact hg i.castSucc j.castSucc u v)
  have htop : (synthesis (r + 1) e).range = ⊤ := (synthesis_range _ _).trans hspan
  rw [← hg0, ← hg1, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint,
    LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint, htop, finrank_top] at hrank
  rw [← synthesis_range r low]
  exact Submodule.eq_top_of_finrank_eq hrank.symm

private theorem shifted_synthesis_gram (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) :
    (synthesis r (fun j => e j.castSucc)).adjoint ∘ₗ
      synthesis r (fun j => e j.succ) = momentBlock M r 1 := by
  classical
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    synthesis_apply, sum_inner, inner_sum]
  simp_rw [hg]
  simp [momentBlock, PiLp.inner_apply, LinearMap.sum_apply, inner_sum, Nat.add_assoc]
  exact Finset.sum_comm

private def FlatShiftGoal (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E) : Prop :=
  (∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) →
  Submodule.span ℝ (⋃ j : Fin r, Set.range (e j.castSucc)) = ⊤ →
  ∀ v : Fin r → U,
    (∑ j, e j.castSucc (v j)) = 0 → (∑ j, e j.succ (v j)) = 0

private theorem flat_shift (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E) : FlatShiftGoal r M e := by
  classical
  intro hgram hspan v hv
  apply generator_pairings _ (fun j : Fin r => e j.castSucc) hspan
  intro i u
  rw [inner_zero_right, inner_sum]
  have hmove : ∀ j : Fin r,
      inner ℝ (e i.castSucc u) (e j.succ (v j)) =
      inner ℝ (e i.succ u) (e j.castSucc (v j)) := by
    intro j
    rw [hgram, hgram]
    have hi : i.castSucc.val + j.succ.val = i.succ.val + j.castSucc.val := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hi]
  simp_rw [hmove]
  rw [← inner_sum, hv, inner_zero_right]

private theorem flat_operator (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v))
    (hspan : Submodule.span ℝ (⋃ j : Fin r, Set.range (e j.castSucc)) = ⊤)
    (hS : (momentBlock M r 1).IsPositive) :
    ∃ C : E →ₗ[ℝ] E, C.IsPositive ∧ (∀ j : Fin r, C ∘ₗ e j.castSucc = e j.succ) := by
  let T := synthesis r (fun j => e j.castSucc)
  let S := synthesis r (fun j => e j.succ)
  have hT : Function.Surjective T := LinearMap.range_eq_top.mp ((synthesis_range _ _).trans hspan)
  have hk : T.ker ≤ S.ker := by
    intro v hv
    have hv' : ∑ j, e j.castSucc (WithLp.ofLp v j) = 0 := by
      simpa only [LinearMap.mem_ker, T, synthesis_apply] using hv
    have hs := flat_shift r M e hg hspan (fun j => WithLp.ofLp v j) hv'
    simpa only [LinearMap.mem_ker, S, synthesis_apply] using hs
  let C := T.liftOfSurjective hT ⟨S, hk⟩
  have hC (v : Coeff U r) : C (T v) = S v := T.equivOfSurjective_apply hT hk
  have hCT : C ∘ₗ T = S := by ext v;exact hC v
  have hs : T.adjoint ∘ₗ C ∘ₗ T = momentBlock M r 1 := by
    rw [hCT]
    exact shifted_synthesis_gram r M e hg
  have hCsym : C.IsSymmetric := by
    intro x y
    obtain ⟨v, rfl⟩ := hT x
    obtain ⟨w, rfl⟩ := hT y
    have hp := hS.isSymmetric v w
    rw [← hs] at hp
    simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right] using hp
  have hCpos : C.IsPositive := positivity_descent T hT C hCsym (hs ▸ hS)
  refine ⟨C, hCpos, ?_⟩
  intro j
  ext u
  simpa only [T, S, synthesis_insert, LinearMap.comp_apply] using hC (coeffInsert r j u)

private theorem shift_powers (r : ℕ) (C : E →ₗ[ℝ] E) (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hshift : ∀ j : Fin r, C ∘ₗ e j.castSucc = e j.succ) :
    ∀ j : Fin (r + 1), (C^j.val) ∘ₗ e 0 = e j := by
  have he : ∀ j (hj : j ≤ r), (C^j) ∘ₗ e 0 = e ⟨j, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj;ext u;rfl
    | succ j ih =>
      intro hj
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, ih (by omega)]
      exact hshift ⟨j, by omega⟩
  exact fun j => he j.val (by omega)

private theorem even_generator_matches (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric) (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v))
    (he : ∀ j : Fin (r + 1), (C^j.val) ∘ₗ e 0 = e j) :
    matchesPrefix (2 * r) M C (e 0) := by
  intro k hk
  ext v
  apply ext_inner_left ℝ
  intro u
  let i : Fin (r + 1) := ⟨min k r, by omega⟩
  let j : Fin (r + 1) := ⟨k-i.val, by dsimp [i];omega⟩
  have hs : k = i.val + j.val := by dsimp [i, j];omega
  rw [hs, moment_pairing C hC]
  have hi := LinearMap.congr_fun (he i) u
  have hj := LinearMap.congr_fun (he j) v
  simp only [LinearMap.comp_apply] at hi hj
  rw [hi, hj]
  exact hg i j u v

/-- Gram flatness makes the truncated shift a well-defined positive realizing operator. -/
theorem even_flat_raw (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (hH : (momentBlock M (r + 1) 0).IsPositive)
    (hS : (momentBlock M r 1).IsPositive)
    (hrank : Module.finrank ℝ (momentBlock M (r + 1) 0).range =
      Module.finrank ℝ (momentBlock M r 0).range) :
    ∃ B : Coeff U (r + 1) →ₗ[ℝ] Coeff U (r + 1),
      Module.finrank ℝ B.range = Module.finrank ℝ (momentBlock M (r + 1) 0).range ∧
      ∃ C : B.range →ₗ[ℝ] B.range, C.IsPositive ∧
        let e : Fin (r + 1) → U →ₗ[ℝ] B.range := fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
        (∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) ∧
        Submodule.span ℝ (⋃ j : Fin r, Set.range (e j.castSucc)) = ⊤ ∧
        (∀ j : Fin (r + 1), (C^j.val) ∘ₗ e 0 = e j) ∧ matchesPrefix (2 * r) M C (e 0) := by
  obtain ⟨B, hB⟩ := gram_factor (momentBlock M (r + 1) 0) hH
  let e : Fin (r + 1) → U →ₗ[ℝ] B.range := fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
  have hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v) := by
    intro i j u v
    change inner ℝ (B (coeffInsert (r + 1) i u)) (B (coeffInsert (r + 1) j v)) = _
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ (coeffInsert (r + 1) i u) ((B.adjoint ∘ₗ B) (coeffInsert (r + 1) j v)) = _
    rw [← hB]
    simpa using block_entry M (r + 1) 0 i j u v
  have hspan := full_generator_span (r + 1) B.rangeRestrict
    (LinearMap.range_eq_top.mp B.range_rangeRestrict)
  have hlow := low_span_of_flat r M e hg hspan hrank
  obtain ⟨C, hC, hshift⟩ := flat_operator r M e hg hlow hS
  have he := shift_powers r C e hshift
  refine ⟨B, ?_, C, hC, hg, hlow, he, even_generator_matches r M C hC.isSymmetric e hg he⟩
  rw [hB, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint]

def even_flat_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : Prop :=
  1 ≤ r → (∀ k ≤ 2 * r, (M k).IsSymmetric) →
  (momentBlock M (r + 1) 0).IsPositive → (momentBlock M r 1).IsPositive →
  Module.finrank ℝ (momentBlock M (r + 1) 0).range =
    Module.finrank ℝ (momentBlock M r 0).range →
  ∃ (n : ℕ) (C : State n →ₗ[ℝ] State n) (J : U →ₗ[ℝ] State n),
    C.IsPositive ∧ matchesPrefix (2 * r) M C J ∧
    n = Module.finrank ℝ (momentBlock M (r + 1) 0).range ∧
    (∀ (m : ℕ) (C' : State m →ₗ[ℝ] State m) (J' : U →ₗ[ℝ] State m),
      C'.IsSymmetric → matchesPrefix (2 * r) M C' J' → ∀ k, moment C' J' k = moment C J k) ∧
    let h : U →ₗ[ℝ] Coeff U r :=
      (WithLp.linearEquiv 2 ℝ (Fin r → U)).symm.toLinearMap ∘ₗ
        (LinearMap.pi fun j : Fin r => M (r + j.val))
    (∃ R : U →ₗ[ℝ] Coeff U r, momentBlock M r 0 ∘ₗ R = h) ∧
      (∀ R : U →ₗ[ℝ] Coeff U r, momentBlock M r 0 ∘ₗ R = h →
        moment C J (2 * r + 1) = R.adjoint ∘ₗ momentBlock M r 1 ∘ₗ R)

private theorem even_gram (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (hM : matchesPrefix (2 * r) M C J) :
    (synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)).adjoint ∘ₗ
      synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J) = momentBlock M (r + 1) 0 := by
  apply synthesis_gram
  intro i j u v
  simpa only [LinearMap.comp_apply, Nat.add_zero, hM (i.val + j.val) (by omega)] using
    (moment_pairing C hC J i.val j.val u v).symm

/-- A spanning lower Krylov space makes the selfadjoint future unique. -/
theorem even_flat_future_unique (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (hM : matchesPrefix (2 * r) M C J) (hlow : lowerSpace r C J = ⊤)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V) (hC' : C'.IsSymmetric)
    (hM' : matchesPrefix (2 * r) M C' J') : ∀ k, moment C' J' k = moment C J k := by
  let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
  let S := synthesis (r + 1) (fun i => (C'^i.val) ∘ₗ J')
  have hT : Function.Surjective T := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hlow]
    rw [synthesis_range]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨j, u, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨j.castSucc, u, rfl⟩
  obtain ⟨q, hq⟩ := gram_isometry T S hT
    ((even_gram r M C J hC hM).trans (even_gram r M C' J' hC' hM').symm)
  have hqj (j : ℕ) (hj : j ≤ r) : q.toLinearMap ∘ₗ (C^j) ∘ₗ J = (C'^j) ∘ₗ J' := by
    ext u
    have hh := LinearMap.congr_fun hq (coeffInsert (r + 1) ⟨j, by omega⟩ u)
    simpa only [T, S, LinearMap.comp_apply, synthesis_insert] using hh
  have hi : q.toLinearMap ∘ₗ C = C' ∘ₗ q.toLinearMap := by
    have hz : C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C = 0 := by
      apply LinearMap.ker_eq_top.mp
      apply top_unique
      rw [← hlow]
      exact embedding_residual_low r C J C' J' q hqj
    exact (sub_eq_zero.mp hz).symm
  exact intertwining_moments q C J C' J' hi (by simpa [Module.End.one_eq_id] using hqj 0 (by omega))

def nextColumn (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : U →ₗ[ℝ] Coeff U r :=
  (WithLp.linearEquiv 2 ℝ (Fin r → U)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun j : Fin r => M (r + j.val))

/-- Every solution of the lower Hankel equation gives the same next moment. -/
theorem even_flat_next_moment (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v))
    (hlow : Submodule.span ℝ (⋃ j : Fin r, Set.range (e j.castSucc)) = ⊤)
    (he : ∀ j : Fin (r + 1), (C^j.val) ∘ₗ e 0 = e j) :
    (∃ R : U →ₗ[ℝ] Coeff U r, momentBlock M r 0 ∘ₗ R = nextColumn r M) ∧
    (∀ R : U →ₗ[ℝ] Coeff U r, momentBlock M r 0 ∘ₗ R = nextColumn r M →
      moment C (e 0) (2 * r + 1) = R.adjoint ∘ₗ momentBlock M r 1 ∘ₗ R) := by
  classical
  let T := synthesis r (fun j => e j.castSucc)
  let er := e ⟨r, by omega⟩
  have hT : Function.Surjective T := LinearMap.range_eq_top.mp ((synthesis_range _ _).trans hlow)
  have hG : T.adjoint ∘ₗ T = momentBlock M r 0 :=
    synthesis_gram r M (fun j => e j.castSucc) (by intro i j u v;exact hg i.castSucc j.castSucc u v)
  have hh : T.adjoint ∘ₗ er = nextColumn r M := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro u
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, T, synthesis_apply, sum_inner, er]
    simp_rw [hg]
    simp [nextColumn, PiLp.inner_apply, Nat.add_comm]
  have hS : T.adjoint ∘ₗ C ∘ₗ T = momentBlock M r 1 := by
    have hshift (j : Fin r) : C ∘ₗ e j.castSucc = e j.succ := by
      rw [← he j.castSucc, ← he j.succ, Fin.val_castSucc, Fin.val_succ, pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]
    have hCT : C ∘ₗ T = synthesis r (fun j => e j.succ) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, T, synthesis_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact LinearMap.congr_fun (hshift j) _
    rw [hCT]
    exact shifted_synthesis_gram r M e hg
  have her : moment C (e 0) (2 * r + 1) = er.adjoint ∘ₗ C ∘ₗ er := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro u
    rw [show 2 * r + 1 = r + (r + 1) by omega, moment_pairing C hC]
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, pow_succ', Module.End.mul_apply]
    have hp := LinearMap.congr_fun (he ⟨r, by omega⟩)
    simp only [LinearMap.comp_apply] at hp
    rw [hp, hp]
  constructor
  · obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective T (LinearMap.range_eq_top.mpr hT)
    refine ⟨R ∘ₗ er, ?_⟩
    rw [← hG, ← hh]
    apply LinearMap.ext
    intro u
    change T.adjoint (T (R (er u))) = T.adjoint (er u)
    exact congrArg T.adjoint (LinearMap.congr_fun hR (er u))
  · intro R hR
    have hTR : T ∘ₗ R = er := by
      ext u
      apply ext_inner_left ℝ
      intro x
      obtain ⟨v, rfl⟩ := hT x
      have ha := LinearMap.congr_fun hR u
      rw [← hG, ← hh] at ha
      have hb := congrArg (inner ℝ v) ha
      simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_right] using hb
    rw [her, ← hS, ← hTR, LinearMap.adjoint_comp]
    simp only [LinearMap.comp_assoc]

/-- A flat even prefix has a least-dimensional positive realization and a unique selfadjoint future. -/
theorem even_flat_positive_realization (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : even_flat_statement r M := by
  intro hr hsym hH hS hrank
  obtain ⟨B, hd, C, hC, hg, hlow, he, hmatch⟩ := even_flat_raw r M hH hS hrank
  let e : Fin (r + 1) → U →ₗ[ℝ] B.range := fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
  have hlow' : lowerSpace r C (e 0) = ⊤ := by
    have ht : (fun j : Fin r => (C^j.val) ∘ₗ e 0) = (fun j : Fin r => e j.castSucc) := by
      funext j;exact he j.castSucc
    change Submodule.span ℝ (⋃ j : Fin r, Set.range ((C^j.val) ∘ₗ e 0)) = ⊤
    have hp (j : Fin r) : (C^j.val) ∘ₗ e 0 = e j.castSucc := he j.castSucc
    simp_rw [hp]
    exact hlow
  obtain ⟨hsol, hformula⟩ := even_flat_next_moment r M C hC.isSymmetric e hg hlow he
  let q := (stdOrthonormalBasis ℝ B.range).repr
  let CQ := q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap
  let JQ := q.toLinearMap ∘ₗ e 0
  refine ⟨Module.finrank ℝ B.range, CQ, JQ,
    (LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hC, ?_, hd, ?_, hsol, ?_⟩
  · intro k hk
    rw [moment_transport]
    exact hmatch k hk
  · intro n C' J' hC' hM' k
    rw [moment_transport]
    exact even_flat_future_unique r M C (e 0) hC.isSymmetric hmatch hlow' C' J' hC' hM' k
  · intro R hR
    rw [moment_transport]
    exact hformula R hR

end D5.S3.Observer.PositiveMoments.EvenFlatMomentExtension
