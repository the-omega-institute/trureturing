/- GID: D5/S3/Observer/PositiveMoments/PrefixFutureUniqueness
   generality: G
   mirror-B: D5/B/S3/Observer/PositiveMoments/PrefixFutureUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Block extensions, exact next-moment defects, and finite-prefix future uniqueness. -/

import D5.S3.Observer.PositiveMoments.PrefixPositiveRealization

/-! Finite-dimensional real inner-product spaces, including zero-dimensional carriers. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped InnerProductSpace MatrixOrder
open LinearMap
namespace D5.S3.Observer.PositiveMoments.PrefixFutureUniqueness
open D5.S3.Observer.PositiveMoments.PrefixPositiveRealization
variable {P E F U V : Type}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def liftInput (J : U →ₗ[ℝ] E) : U →ₗ[ℝ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap ∘ₗ
    J.prod (0 : U →ₗ[ℝ] F)

private def inLeft : E →ₗ[ℝ] WithLp 2 (E × F) := liftInput LinearMap.id

private def inRight : F →ₗ[ℝ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap ∘ₗ
    (0 : F →ₗ[ℝ] E).prod LinearMap.id

private def outRight : WithLp 2 (E × F) →ₗ[ℝ] F :=
  LinearMap.snd ℝ E F ∘ₗ (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

def block (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] F) :
    (WithLp 2 (E × F)) →ₗ[ℝ] (WithLp 2 (E × F)) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap ∘ₗ
    ((C.comp (LinearMap.fst ℝ E F) + D.adjoint.comp (LinearMap.snd ℝ E F)).prod
      (D.comp (LinearMap.fst ℝ E F) + A.comp (LinearMap.snd ℝ E F))) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

private theorem symmetric_block_reconstruction
    (T : WithLp 2 (E × F) →ₗ[ℝ] WithLp 2 (E × F)) (hT : T.IsSymmetric)
    (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (hp : ∀ x y, inner ℝ (inLeft (F := F) x) (T (inLeft y)) = inner ℝ x (C y)) :
    T = block C (outRight ∘ₗ T ∘ₗ inLeft) (outRight ∘ₗ T ∘ₗ inRight) := by
  let D := outRight ∘ₗ T ∘ₗ inLeft
  let A := outRight ∘ₗ T ∘ₗ inRight
  have htop (x : E) : (T (inLeft (F := F) x)).fst = C x := by
    apply ext_inner_left ℝ
    intro y
    simpa [inLeft, liftInput, WithLp.prod_inner_apply] using hp y x
  have hd (x : E) : (T (inLeft (F := F) x)).snd = D x := rfl
  have ha (y : F) : (T (inRight (E := E) y)).snd = A y := rfl
  have hcross (y : F) : (T (inRight (E := E) y)).fst = D.adjoint y := by
    apply ext_inner_left ℝ
    intro x
    have hh := hT (inLeft (F := F) x) (inRight y)
    simpa [D, outRight, inLeft, inRight, liftInput, WithLp.prod_inner_apply, htop,
      LinearMap.adjoint_inner_right] using hh.symm
  have hsplit (z : WithLp 2 (E × F)) : z = inLeft z.fst + inRight z.snd := by
    apply (WithLp.linearEquiv 2 ℝ (E × F)).injective
    simpa [inLeft, inRight, liftInput] using (Prod.eta (WithLp.ofLp z)).symm
  ext z
  apply (WithLp.linearEquiv 2 ℝ (E × F)).injective
  change (T z).ofLp = (block C D A z).ofLp
  conv_lhs => rw [hsplit z, map_add]
  apply Prod.ext
  · simpa [block] using congrArg₂ (· + ·) (htop z.fst) (hcross z.snd)
  · simpa [block] using congrArg₂ (· + ·) (hd z.fst) (ha z.snd)

def lowerSpace (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ (⋃ j : Fin r, Set.range ((C ^ j.val) ∘ₗ J))

def block_extension_forward_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V) : Prop :=
  C.IsPositive → matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
  C'.IsPositive → matchesPrefix (2 * r + 1) M C' J' →
  ∃ (n : ℕ) (Q : V ≃ₗᵢ[ℝ] WithLp 2 (E × State n))
    (D : E →ₗ[ℝ] State n) (A : State n →ₗ[ℝ] State n),
    Q.toLinearMap ∘ₗ J' = liftInput J ∧
    Q.toLinearMap ∘ₗ C' ∘ₗ Q.symm.toLinearMap = block C D A ∧
    lowerSpace r C J ≤ D.ker

/-- The common prefix forces the embedding residual to vanish on the lower Krylov space. -/
theorem embedding_residual_low (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V) (q : E →ₗᵢ[ℝ] V)
    (hq : ∀ j ≤ r, q.toLinearMap ∘ₗ (C^j) ∘ₗ J = (C'^j) ∘ₗ J') :
    lowerSpace r C J ≤ (C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C).ker := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨j, u, rfl⟩ := Set.mem_iUnion.mp hx
  have h1 := LinearMap.congr_fun (hq j.val (by omega)) u
  have h2 := LinearMap.congr_fun (hq (j.val + 1) (by omega)) u
  simp only [LinearMap.comp_apply, pow_succ', Module.End.mul_apply, LinearIsometry.coe_toLinearMap] at h1 h2 ⊢
  change C' (q ((C^j.val) (J u))) - q (C ((C^j.val) (J u))) = 0
  rw [h1, h2]
  simp

/-- Every positive competitor is an orthogonal block extension preserving the input. -/
theorem realization_eq_block_extension (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V) :
    block_extension_forward_statement r M C J C' J' := by
  intro hC hM hcyc hC' hM'
  obtain ⟨q, hq, hpair⟩ := prefix_embedding r M C J C' J'
    hC.isSymmetric hC'.isSymmetric hM hM' hcyc
  let K := q.toLinearMap.range
  let b := (stdOrthonormalBasis ℝ Kᗮ).repr
  let Q := K.orthogonalDecomposition.trans (q.equivRange.symm.withLpProdCongr (p := 2) b)
  have hQi (x : E) : Q.symm (WithLp.toLp 2 (x, 0)) = q x := by
    simp [Q, K]
  have hQq (x : E) : Q (q x) = WithLp.toLp 2 (x, 0) := by
    rw [← hQi]
    simp
  let T := Q.toLinearMap ∘ₗ C' ∘ₗ Q.symm.toLinearMap
  have hT : T.IsPositive := (LinearMap.isPositive_linearIsometryEquiv_conj_iff Q).mpr hC'
  have hp (x y : E) : inner ℝ (inLeft x) (T (inLeft y)) = inner ℝ x (C y) := by
    change inner ℝ (WithLp.toLp 2 (x, 0)) (Q (C' (Q.symm (WithLp.toLp 2 (y, 0))))) = _
    rw [hQi, ← hQq, Q.inner_map_map, hpair]
  let D := outRight ∘ₗ T ∘ₗ inLeft
  let A := outRight ∘ₗ T ∘ₗ inRight
  refine ⟨Module.finrank ℝ Kᗮ, Q, D, A, ?_, symmetric_block_reconstruction T hT.isSymmetric C hC.isSymmetric hp, ?_⟩
  · ext u
    have hj := LinearMap.congr_fun (hq 0 (by omega)) u
    simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_apply, LinearMap.id_apply] at hj
    change Q (J' u) = WithLp.toLp 2 (J u, 0)
    rw [← hj]
    exact hQq _
  · intro x hx
    have hr := embedding_residual_low r C J C' J' q hq hx
    have he : C' (q x) = q (C x) := sub_eq_zero.mp hr
    change outRight (Q (C' (Q.symm (WithLp.toLp 2 (x, 0))))) = 0
    rw [hQi, he, hQq]
    rfl

private theorem positive_block_kernel (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (hB : (block C D A).IsPositive) : C.ker ≤ D.ker := by
  intro x hx
  have hc : C x = 0 := hx
  let z : WithLp 2 (E × F) := WithLp.toLp 2 (x, 0)
  have hz : inner ℝ (block C D A z) z = 0 := by simp [z, block, hc]
  have hp := positive_zero (block C D A) hB z hz
  have hd := congrArg (fun p : WithLp 2 (E × F) => p.snd) hp
  simpa [z, block] using hd

/-- A coupling vanishing on the truncated orbit preserves its block powers up to that order. -/
theorem block_krylov_binding (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (J : U →ₗ[ℝ] E) (r : ℕ)
    (hD : ∀ j < r, D ∘ₗ (C ^ j) ∘ₗ J = 0) :
    ∀ j ≤ r, (block C D A ^ j) ∘ₗ liftInput (F := F) J =
      liftInput (F := F) ((C ^ j) ∘ₗ J) := by
  intro j hj
  induction j with
  | zero => ext u <;> simp [liftInput]
  | succ j ih =>
      have hjr : j < r := by omega
      have ih' := ih (by omega)
      ext u
      have hd : D ((C ^ j) (J u)) = 0 := LinearMap.congr_fun (hD j hjr) u
      have hp := LinearMap.congr_fun ih' u
      change (block C D A ^ (j + 1)) (liftInput J u) =
        liftInput ((C ^ (j + 1)) ∘ₗ J) u
      rw [pow_succ', Module.End.mul_apply]
      change (block C D A) (((block C D A ^ j) ∘ₗ liftInput J) u) = _
      rw [hp]
      simp [pow_succ', Module.End.mul_apply, liftInput, block, hd]

private theorem block_next_apply (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (J : U →ₗ[ℝ] E) (r : ℕ)
    (hD : ∀ j < r, D ∘ₗ (C ^ j) ∘ₗ J = 0) (u : U) :
    (block C D A ^ (r + 1)) (liftInput J u) =
      WithLp.toLp 2 ((C ^ (r + 1)) (J u), D ((C ^ r) (J u))) := by
  rw [pow_succ', Module.End.mul_apply]
  have hp := LinearMap.congr_fun (block_krylov_binding C D A J r hD r le_rfl) u
  change (block C D A) (((block C D A ^ r) ∘ₗ liftInput J) u) = _
  rw [hp]
  simp [liftInput, block, pow_succ', Module.End.mul_apply]

private theorem block_prefix (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (J : U →ₗ[ℝ] E) (r : ℕ)
    (hC : C.IsSymmetric) (hB : (block C D A).IsSymmetric)
    (hD : ∀ j < r, D ∘ₗ (C^j) ∘ₗ J = 0) :
    ∀ k ≤ 2 * r + 1, moment (block C D A) (liftInput J) k = moment C J k := by
  intro k hk
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  by_cases hkr : k ≤ 2 * r
  · let i := min k r
    let j := k-i
    have hi : i ≤ r := Nat.min_le_right _ _
    have hj : j ≤ r := by dsimp [i, j]; omega
    have hs : k = i + j := by dsimp [i, j]; omega
    rw [hs, moment_pairing _ hB, moment_pairing _ hC]
    have hp := block_krylov_binding C D A J r hD
    have hpi := LinearMap.congr_fun (hp i hi) u
    have hpj := LinearMap.congr_fun (hp j hj) v
    simp only [LinearMap.comp_apply] at hpi hpj
    rw [hpi, hpj]
    simp [liftInput]
  · have hs : k = r + (r + 1) := by omega
    rw [hs, moment_pairing _ hB, moment_pairing _ hC]
    have hp := LinearMap.congr_fun (block_krylov_binding C D A J r hD r le_rfl) u
    simp only [LinearMap.comp_apply] at hp
    rw [hp, block_next_apply C D A J r hD v]
    simp [liftInput]

private theorem next_defect_pairing (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (J : U →ₗ[ℝ] E) (r : ℕ)
    (hD : ∀ j < r, D ∘ₗ (C ^ j) ∘ₗ J = 0) (u v : U) :
    inner ℝ ((block C D A ^ (r + 1)) (liftInput J u))
        ((block C D A ^ (r + 1)) (liftInput J v)) -
      inner ℝ ((C ^ (r + 1)) (J u)) ((C ^ (r + 1)) (J v)) =
    inner ℝ (D ((C ^ r) (J u))) (D ((C ^ r) (J v))) := by
  rw [block_next_apply C D A J r hD u, block_next_apply C D A J r hD v]
  simp

/-- The first unprescribed moment difference is the square of the last coupling. -/
theorem next_defect_operator_binding (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (A : F →ₗ[ℝ] F) (J : U →ₗ[ℝ] E) (r : ℕ)
    (hC : C.IsSymmetric) (hB : (block C D A).IsSymmetric)
    (hD : ∀ j < r, D ∘ₗ (C^j) ∘ₗ J = 0) :
    moment (block C D A) (liftInput J) (2 * r + 2) - moment C J (2 * r + 2) =
      (D ∘ₗ (C^r) ∘ₗ J).adjoint ∘ₗ (D ∘ₗ (C^r) ∘ₗ J) := by
  ext v
  apply ext_inner_left ℝ
  intro u
  have hs : 2 * r + 2 = (r + 1) + (r + 1) := by omega
  simp only [LinearMap.sub_apply, inner_sub_right, hs,
    moment_pairing _ hB, moment_pairing _ hC,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact next_defect_pairing C D A J r hD u v

def block_extension_reverse_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] F) : Prop :=
  C.IsPositive → matchesPrefix (2 * r + 1) M C J → (block C D A).IsPositive →
  lowerSpace r C J ≤ D.ker →
  matchesPrefix (2 * r + 1) M (block C D A) (liftInput J) ∧ C.ker ≤ D.ker ∧
    moment (block C D A) (liftInput J) (2 * r + 2) - moment C J (2 * r + 2) =
      (D ∘ₗ (C ^ r) ∘ₗ J).adjoint ∘ₗ (D ∘ₗ (C ^ r) ∘ₗ J)

/-- Every admissible positive block extension matches the prefix and has the stated defect. -/
theorem block_extension_realizes_prefix (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (D : E →ₗ[ℝ] F) (A : F →ₗ[ℝ] F) :
    block_extension_reverse_statement r M C J D A := by
  intro hC hM hB hL
  have hd : ∀ j < r, D ∘ₗ (C^j) ∘ₗ J = 0 := by
    intro j hj
    ext u
    apply hL
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, u, rfl⟩
  refine ⟨?_, positive_block_kernel C D A hB,
    next_defect_operator_binding C D A J r hC.isSymmetric hB.isSymmetric hd⟩
  intro k hk
  exact (block_prefix C D A J r hC.isSymmetric hB.isSymmetric hd k hk).trans (hM k hk)

def futureUnique (N : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  ∀ (n : ℕ) (C' : State n →ₗ[ℝ] State n) (J' : U →ₗ[ℝ] State n),
    C'.IsPositive → matchesPrefix N M C' J' → ∀ k, moment C' J' k = moment C J k

def future_unique_iff_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  C.IsPositive → matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
  (futureUnique (2 * r + 1) M C J ↔ lowerSpace r C J ⊔ C.ker = ⊤) ∧
  (lowerSpace r C J ⊔ C.ker = ⊤ ↔
    Module.finrank ℝ (momentBlock M (r + 1) 1).range =
      Module.finrank ℝ (momentBlock M r 1).range)

private theorem weighted_rank (r q : ℕ) (hq : q ≤ r + 1) (M : ℕ → U →ₗ[ℝ] U)
    (C B : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hB : C = B.adjoint ∘ₗ B)
    (hM : matchesPrefix (2 * r + 1) M C J) :
    Module.finrank ℝ (momentBlock M q 1).range =
      Module.finrank ℝ ((Submodule.span ℝ (⋃ i : Fin q, Set.range ((C^i.val) ∘ₗ J))).map B) := by
  let T := synthesis q (fun i => (C^i.val) ∘ₗ J)
  have hg : (B ∘ₗ T).adjoint ∘ₗ (B ∘ₗ T) = momentBlock M q 1 := by
    have hh := synthesis_gram q (fun k => M (k + 1))
      (fun i => B ∘ₗ (C^i.val) ∘ₗ J) (by
        intro i j u v
        simp only [LinearMap.comp_apply]
        rw [← LinearMap.adjoint_inner_right]
        change inner ℝ ((C^i.val) (J u)) ((B.adjoint ∘ₗ B) ((C^j.val) (J v))) = _
        rw [← hB]
        have hm := moment_pairing C hC J i.val (j.val + 1) u v
        rw [hM _ (by omega)] at hm
        simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using hm.symm)
    have ht : synthesis q (fun i => B ∘ₗ (C^i.val) ∘ₗ J) = B ∘ₗ T := by
      ext x
      simp [synthesis_apply, T, map_sum]
    rw [ht] at hh
    simpa only [momentBlock, Nat.add_zero] using hh
  rw [← hg, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint,
    LinearMap.range_comp, synthesis_range]

private theorem rank_span_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hM : matchesPrefix (2 * r + 1) M C J)
    (hcyc : cyclicPrefix r C J) :
    (lowerSpace r C J ⊔ C.ker = ⊤ ↔
      Module.finrank ℝ (momentBlock M (r + 1) 1).range =
        Module.finrank ℝ (momentBlock M r 1).range) := by
  obtain ⟨B, hB⟩ := gram_factor C hC
  have hk : C.ker = B.ker := by rw [hB, LinearMap.ker_adjoint_comp_self]
  rw [weighted_rank r (r + 1) le_rfl M C B J hC.isSymmetric hB hM,
    weighted_rank r r (by omega) M C B J hC.isSymmetric hB hM, hcyc, Submodule.map_top]
  change _ ↔ Module.finrank ℝ B.range = Module.finrank ℝ ((lowerSpace r C J).map B)
  rw [hk]
  have heq : (lowerSpace r C J).map B = B.range ↔ lowerSpace r C J ⊔ B.ker = ⊤ := by
    simpa only [codisjoint_iff] using
      (Submodule.map_eq_range_iff (f := B) (p := lowerSpace r C J))
  constructor
  · intro h
    rw [heq.mpr h]
  · intro h
    apply heq.mp
    exact Submodule.eq_of_le_of_finrank_eq (LinearMap.map_le_range) h.symm

private theorem nonzero_last_coupling (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (r : ℕ) (hcyc : cyclicPrefix r C J) (D : E →ₗ[ℝ] ℝ)
    (hD : D ≠ 0) (hL : lowerSpace r C J ≤ D.ker) :
    D ∘ₗ (C^r) ∘ₗ J ≠ 0 := by
  intro hz
  apply hD
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hcyc]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨u, rfl⟩ := hj
  by_cases hjr : j.val < r
  · apply hL
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨⟨j.val, hjr⟩, u, rfl⟩
  · have heq : j.val = r := by omega
    change D ((C ^ j.val) (J u)) = 0
    rw [heq]
    exact LinearMap.congr_fun hz u

private theorem factor_through (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F)
    (hker : C.ker ≤ D.ker) : ∃ G : E →ₗ[ℝ] F, G ∘ₗ C = D := by
  let T := C.rangeRestrict
  have hT : Function.Surjective T := range_eq_top.mp C.range_rangeRestrict
  have hk : T.ker ≤ D.ker := by simpa only [T, LinearMap.ker_rangeRestrict] using hker
  let B := T.liftOfSurjective hT ⟨D, hk⟩
  have hB (x : E) : B (T x) = D x := T.equivOfSurjective_apply hT hk
  obtain ⟨G, hG⟩ := B.exists_extend
  refine ⟨G, ?_⟩
  ext x
  change G (C x) = D x
  have he := LinearMap.congr_fun hG (T x)
  exact he.trans (hB x)

private theorem block_explicit_positive (C : E →ₗ[ℝ] E) (hC : C.IsPositive)
    (G : E →ₗ[ℝ] F) :
    (block C (G ∘ₗ C) (G ∘ₗ C ∘ₗ G.adjoint)).IsPositive := by
  let V : E →ₗ[ℝ] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap ∘ₗ (LinearMap.id.prod G)
  have hv : V.adjoint =
      (LinearMap.fst ℝ E F + G.adjoint ∘ₗ LinearMap.snd ℝ E F) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap := by
    symm
    apply (LinearMap.eq_adjoint_iff _ V).mpr
    intro x y
    simp [V, WithLp.prod_inner_apply, inner_add_left, LinearMap.adjoint_inner_left]
  convert hC.conj_adjoint V using 1
  rw [hv]
  ext x
  simp [block, V, hC.adjoint_eq, LinearMap.adjoint_comp, map_add]

private def BlockPositiveGoal (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F) : Prop :=
  C.IsPositive → C.ker ≤ D.ker → ∃ A : F →ₗ[ℝ] F, (block C D A).IsPositive

private theorem arbitrary_block_extension (C : E →ₗ[ℝ] E) (D : E →ₗ[ℝ] F) :
    BlockPositiveGoal C D := by
  intro hC hker
  obtain ⟨G, hG⟩ := factor_through C D hker
  refine ⟨G ∘ₗ C ∘ₗ G.adjoint, ?_⟩
  rw [← hG]
  exact block_explicit_positive C hC G

private theorem nonzero_positive_extension (C : E →ₗ[ℝ] E)
    (L : Submodule ℝ E) (hC : C.IsPositive) (hL : L ⊔ C.ker ≠ ⊤) :
    ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ), D ≠ 0 ∧ L ≤ D.ker ∧
      (block C D A).IsPositive := by
  obtain ⟨D, hD, hker⟩ := (L ⊔ C.ker).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hL)
  obtain ⟨A, hA⟩ := arbitrary_block_extension C D hC (le_sup_right.trans hker)
  exact ⟨D, A, hD, le_sup_left.trans hker, hA⟩

private theorem adjoint_square_nonzero {U : Type}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (D : U →ₗ[ℝ] E) (hD : D ≠ 0) : D.adjoint ∘ₗ D ≠ 0 := by
  intro hzero
  apply hD
  apply LinearMap.ker_eq_top.mp
  rw [← LinearMap.ker_adjoint_comp_self D, hzero, LinearMap.ker_zero]

private theorem positive_escape {U : Type}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hcyc : cyclicPrefix r C J)
    (hL : lowerSpace r C J ⊔ C.ker ≠ ⊤) :
    ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ),
      (block C D A).IsPositive ∧ lowerSpace r C J ≤ D.ker ∧
      (∀ k ≤ 2 * r + 1, moment (block C D A) (liftInput J) k = moment C J k) ∧
      moment (block C D A) (liftInput J) (2 * r + 2) ≠ moment C J (2 * r + 2) := by
  obtain ⟨D, A, hd, hl, hp⟩ := nonzero_positive_extension C (lowerSpace r C J) hC hL
  have hlast := nonzero_last_coupling C J r hcyc D hd hl
  have hb := block_extension_realizes_prefix r (fun k => moment C J k) C J D A hC
    (fun _ _ => rfl) hp hl
  refine ⟨D, A, hp, hl, hb.1, ?_⟩
  intro heq
  have hz : (D ∘ₗ (C^r) ∘ₗ J).adjoint ∘ₗ (D ∘ₗ (C^r) ∘ₗ J) = 0 := by
    rw [← hb.2.2, heq, sub_self]
  exact adjoint_square_nonzero _ hlast hz

private theorem embedding_residual_kernel (C : E →ₗ[ℝ] E) (C' : V →ₗ[ℝ] V)
    (hC' : C'.IsPositive) (q : E →ₗᵢ[ℝ] V)
    (hp : ∀ x y, inner ℝ (q x) (C' (q y)) = inner ℝ x (C y)) :
    C.ker ≤ (C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C).ker := by
  intro x hx
  have hx' : C x = 0 := hx
  have hz : inner ℝ (C' (q x)) (q x) = 0 := by rw [real_inner_comm, hp, hx', inner_zero_right]
  have hz' := positive_zero C' hC' (q x) hz
  change C' (q x) - q (C x) = 0
  simp [hx', hz']

private theorem future_unique_of_span (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hM : matchesPrefix (2 * r + 1) M C J)
    (hcyc : cyclicPrefix r C J) (hspan : lowerSpace r C J ⊔ C.ker = ⊤) :
    futureUnique (2 * r + 1) M C J := by
  intro n C' J' hC' hM'
  obtain ⟨q, hq, hp⟩ := prefix_embedding r M C J C' J' hC.isSymmetric hC'.isSymmetric hM hM' hcyc
  have hz : C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hspan]
    exact sup_le (embedding_residual_low r C J C' J' q hq)
      (embedding_residual_kernel C C' hC' q hp)
  exact intertwining_moments q C J C' J' (sub_eq_zero.mp hz).symm
    (by simpa [Module.End.one_eq_id] using hq 0 (by omega))

private theorem positive_future_span_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hM : matchesPrefix (2 * r + 1) M C J)
    (hcyc : cyclicPrefix r C J) :
    futureUnique (2 * r + 1) M C J ↔ lowerSpace r C J ⊔ C.ker = ⊤ := by
  refine ⟨?_, future_unique_of_span r M C J hC hM hcyc⟩
  intro huni
  by_contra hspan
  obtain ⟨D, A, hB, hD, hprefix, hneq⟩ := positive_escape r C J hC hcyc hspan
  let q := (stdOrthonormalBasis ℝ (WithLp 2 (E × ℝ))).repr
  let CB := block C D A
  let JB := liftInput (F := ℝ) J
  have hp : matchesPrefix (2 * r + 1) M
      (q.toLinearMap ∘ₗ CB ∘ₗ q.symm.toLinearMap) (q.toLinearMap ∘ₗ JB) := by
    intro k hk
    rw [moment_transport]
    exact (hprefix k hk).trans (hM k hk)
  have he := huni _ _ _ ((LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hB) hp (2 * r + 2)
  rw [moment_transport] at he
  exact hneq he

/-- Future uniqueness is equivalent to the kernel span criterion and shifted rank flatness. -/
theorem future_unique_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) :
    future_unique_iff_statement r M C J := by
  intro hC hM hcyc
  exact ⟨positive_future_span_iff r M C J hC hM hcyc,
    rank_span_iff r M C J hC hM hcyc⟩

def defectSet (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Set (U →ₗ[ℝ] U) :=
  {N | ∃ (n : ℕ) (C' : State n →ₗ[ℝ] State n) (J' : U →ₗ[ℝ] State n),
    C'.IsPositive ∧ matchesPrefix (2 * r + 1) M C' J' ∧
      N = moment C' J' (2 * r + 2) - moment C J (2 * r + 2)}

def next_moment_defects_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  C.IsPositive → matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
  let W := (lowerSpace r C J ⊔ C.ker)ᗮ
  let Q : U →ₗ[ℝ] W := W.orthogonalProjectionOnto.toLinearMap ∘ₗ (C ^ r) ∘ₗ J
  Function.Surjective Q ∧
    Module.finrank ℝ W = Module.finrank ℝ (momentBlock M (r + 1) 1).range -
      Module.finrank ℝ (momentBlock M r 1).range ∧
    defectSet r M C J = {N | ∃ Z : W →ₗ[ℝ] W, Z.IsPositive ∧ N = Q.adjoint ∘ₗ Z ∘ₗ Q} ∧
    (∀ N ∈ defectSet r M C J, N.IsPositive)

private theorem defect_cone_realization (r : ℕ) (C : E →ₗ[ℝ] E)
    (J : U →ₗ[ℝ] E) (hC : C.IsPositive)
    (Z : (lowerSpace r C J ⊔ C.ker)ᗮ →ₗ[ℝ] (lowerSpace r C J ⊔ C.ker)ᗮ)
    (hZ : Z.IsPositive) :
    let W := (lowerSpace r C J ⊔ C.ker)ᗮ
    let Q : U →ₗ[ℝ] W := W.orthogonalProjectionOnto.toLinearMap ∘ₗ (C^r) ∘ₗ J
    ∃ (D : E →ₗ[ℝ] W) (A : W →ₗ[ℝ] W),
      (block C D A).IsPositive ∧ lowerSpace r C J ≤ D.ker ∧
      (∀ k ≤ 2 * r + 1, moment (block C D A) (liftInput J) k = moment C J k) ∧
      moment (block C D A) (liftInput J) (2 * r + 2) - moment C J (2 * r + 2) =
        Q.adjoint ∘ₗ Z ∘ₗ Q := by
  dsimp only
  let W := (lowerSpace r C J ⊔ C.ker)ᗮ
  let P : E →ₗ[ℝ] W := W.orthogonalProjectionOnto.toLinearMap
  obtain ⟨B, hB⟩ := gram_factor Z hZ
  let D : E →ₗ[ℝ] W := B ∘ₗ P
  have hP : lowerSpace r C J ⊔ C.ker ≤ P.ker := by
    intro x hx
    exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx
  have hD : lowerSpace r C J ⊔ C.ker ≤ D.ker := by
    intro x hx
    change B (P x) = 0
    rw [show P x = 0 from hP hx, map_zero]
  obtain ⟨A, hA⟩ := arbitrary_block_extension C D hC (le_sup_right.trans hD)
  have hL := le_sup_left.trans hD
  have hb := block_extension_realizes_prefix r (fun k => moment C J k) C J D A hC
    (fun _ _ => rfl) hA hL
  refine ⟨D, A, hA, hL, hb.1, ?_⟩
  rw [hb.2.2, hB]
  simp only [D, P, W, LinearMap.adjoint_comp, LinearMap.comp_assoc]

private theorem projection_factor (K : Submodule ℝ E) (D : E →ₗ[ℝ] F) (hD : K ≤ D.ker) :
    D.domRestrict Kᗮ ∘ₗ Kᗮ.orthogonalProjectionOnto.toLinearMap = D := by
  apply LinearMap.ext
  intro x
  change D (Kᗮ.starProjection x) = D x
  rw [Submodule.starProjection_orthogonal_val, map_sub]
  have hz : D (K.starProjection x) = 0 := hD (K.orthogonalProjectionOnto x).property
  rw [hz, sub_zero]

private theorem last_projection_surj (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hcyc : cyclicPrefix r C J) (K : Submodule ℝ E) (hL : lowerSpace r C J ≤ K) :
    Function.Surjective (Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ (C^r) ∘ₗ J) := by
  let P := Kᗮ.orthogonalProjectionOnto.toLinearMap
  let Q := P ∘ₗ (C^r) ∘ₗ J
  have hall : ∀ x : E, P x ∈ Q.range := by
    intro x
    have hx : x ∈ Submodule.span ℝ (⋃ j : Fin (r + 1), Set.range ((C^j.val) ∘ₗ J)) := by rw [hcyc];trivial
    have hs : Submodule.span ℝ
        (⋃ j : Fin (r + 1), Set.range ((C^j.val) ∘ₗ J)) ≤ Q.range.comap P := by
      apply Submodule.span_le.mpr
      rintro y hy
      obtain ⟨j, u, rfl⟩ := Set.mem_iUnion.mp hy
      by_cases hj : j.val < r
      · have hl : (C^j.val) (J u) ∈ K := hL
          (Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨j.val, hj⟩, u, rfl⟩))
        have hz : P ((C^j.val) (J u)) = 0 :=
          Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hl
        change P ((C^j.val) (J u)) ∈ Q.range
        rw [hz]
        exact Q.range.zero_mem
      · have hj' : j.val = r := by omega
        exact ⟨u, by simp only [Q, LinearMap.comp_apply, hj']⟩
    exact hs hx
  intro w
  have hw := hall (w : E)
  simpa only [P, Q, LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hw

private theorem orthogonal_gap (L : Submodule ℝ E) (B : E →ₗ[ℝ] E) :
    Module.finrank ℝ (L ⊔ B.ker)ᗮ =
      Module.finrank ℝ B.range - Module.finrank ℝ (L.map B) := by
  let K := L ⊔ B.ker
  have hd := B.finrank_range_add_finrank_ker
  have hdK := (B.domRestrict K).finrank_range_add_finrank_ker
  have hk : Module.finrank ℝ (B.domRestrict K).ker = Module.finrank ℝ B.ker := by
    change Module.finrank ℝ (B.ker.comap K.subtype) = _
    exact (Submodule.comapSubtypeEquivOfLe (show B.ker ≤ K from le_sup_right)).finrank_eq
  have hm : (B.domRestrict K).range = L.map B := by
    rw [LinearMap.range_domRestrict]
    have hz : B.ker.map B = ⊥ := by
      apply le_antisymm ?_ bot_le
      rintro y ⟨x, hx, rfl⟩
      exact hx
    simp only [K, Submodule.map_sup, hz, sup_bot_eq]
  rw [hk, hm] at hdK
  have ho := K.finrank_add_finrank_orthogonal
  change Module.finrank ℝ Kᗮ = _
  omega

/-- All possible next-moment defects form precisely the positive cone compressed by Q. -/
theorem next_moment_defects (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : next_moment_defects_statement r M C J := by
  intro hC hM hcyc
  dsimp only
  let K := lowerSpace r C J ⊔ C.ker
  let W := Kᗮ
  let P := W.orthogonalProjectionOnto.toLinearMap
  let Q := P ∘ₗ (C^r) ∘ₗ J
  have hsurj : Function.Surjective Q := last_projection_surj r C J hcyc K le_sup_left
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (momentBlock M (r + 1) 1).range -
      Module.finrank ℝ (momentBlock M r 1).range := by
    obtain ⟨B, hB⟩ := gram_factor C hC
    have hk : C.ker = B.ker := by rw [hB, LinearMap.ker_adjoint_comp_self]
    rw [weighted_rank r (r + 1) le_rfl M C B J hC.isSymmetric hB hM,
      weighted_rank r r (by omega) M C B J hC.isSymmetric hB hM, hcyc, Submodule.map_top]
    change Module.finrank ℝ (lowerSpace r C J ⊔ C.ker)ᗮ = _
    rw [hk]
    exact orthogonal_gap (lowerSpace r C J) B
  have hset : defectSet r M C J = {N | ∃ Z : W →ₗ[ℝ] W, Z.IsPositive ∧ N = Q.adjoint ∘ₗ Z ∘ₗ Q} := by
    ext N
    constructor
    · rintro ⟨n, C', J', hC', hM', rfl⟩
      obtain ⟨m, q, D, A, hJ, hT, hD⟩ := realization_eq_block_extension r M C J C' J' hC hM hcyc hC' hM'
      have hB : (block C D A).IsPositive := hT ▸ (LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hC'
      have hr := block_extension_realizes_prefix r M C J D A hC hM hB hD
      have hf := projection_factor K D (sup_le hD hr.2.1)
      let Z : W →ₗ[ℝ] W := (D.domRestrict W).adjoint ∘ₗ D.domRestrict W
      refine ⟨Z, LinearMap.isPositive_adjoint_comp_self _, ?_⟩
      have hmoment : moment C' J' (2 * r + 2) = moment (block C D A) (liftInput J) (2 * r + 2) := by
        rw [← hT, ← hJ, moment_transport]
      rw [hmoment, hr.2.2]
      change _ = (P ∘ₗ (C^r) ∘ₗ J).adjoint ∘ₗ Z ∘ₗ (P ∘ₗ (C^r) ∘ₗ J)
      rw [← hf]
      simp only [Z, P, W, LinearMap.adjoint_comp, LinearMap.comp_assoc]
    · rintro ⟨Z, hZ, rfl⟩
      obtain ⟨D, A, hB, hD, hprefix, hdef⟩ := defect_cone_realization r C J hC Z hZ
      let q := (stdOrthonormalBasis ℝ (WithLp 2 (E × W))).repr
      refine ⟨_, q.toLinearMap ∘ₗ block C D A ∘ₗ q.symm.toLinearMap,
        q.toLinearMap ∘ₗ liftInput J, (LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hB, ?_, ?_⟩
      · intro k hk
        rw [moment_transport]
        exact (hprefix k hk).trans (hM k hk)
      · rw [moment_transport]
        exact hdef.symm
  refine ⟨hsurj, hdim, hset, ?_⟩
  intro N hN
  obtain ⟨Z, hZ, rfl⟩ := hset ▸ hN
  exact hZ.adjoint_conj Q

private theorem ordinary_rank (r q : ℕ) (hq : q ≤ r + 1) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hM : matchesPrefix (2 * r + 1) M C J) :
    Module.finrank ℝ (momentBlock M q 0).range =
      Module.finrank ℝ (Submodule.span ℝ (⋃ i : Fin q, Set.range ((C^i.val) ∘ₗ J))) := by
  have hg := synthesis_gram q M (fun i => (C^i.val) ∘ₗ J) (by
    intro i j u v
    simpa only [LinearMap.comp_apply, Nat.add_zero, hM (i.val + j.val) (by omega)] using
      (moment_pairing C hC J i.val j.val u v).symm)
  rw [← hg, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint, synthesis_range]

private theorem ordinary_flat_span_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (hM : matchesPrefix (2 * r + 1) M C J) (hcyc : cyclicPrefix r C J) :
    (Module.finrank ℝ (momentBlock M (r + 1) 0).range =
      Module.finrank ℝ (momentBlock M r 0).range) ↔ lowerSpace r C J = ⊤ := by
  rw [ordinary_rank r (r + 1) le_rfl M C J hC hM,
    ordinary_rank r r (by omega) M C J hC hM, hcyc, finrank_top]
  exact ⟨fun h => Submodule.eq_top_of_finrank_eq h.symm, fun h => by change Module.finrank ℝ E = Module.finrank ℝ (lowerSpace r C J);rw [h, finrank_top]⟩

private theorem bottom_positive (a : ℝ) (ha : 0 ≤ a) :
    (block (0 : E →ₗ[ℝ] E) (0 : E →ₗ[ℝ] ℝ)
      (a • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))).IsPositive := by
  apply (LinearMap.isPositive_iff _).mpr
  constructor
  · intro x y
    simp [block, WithLp.prod_inner_apply, mul_assoc, mul_left_comm, mul_comm]
  · intro x
    simp [block, WithLp.prod_inner_apply]
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using mul_nonneg ha (sq_nonneg x.snd)

private theorem strict_block_extension (C : E →ₗ[ℝ] E) (hC : C.IsPositive)
    (hker : C.ker = ⊥) (G : E →ₗ[ℝ] ℝ) (η : ℝ) (hη : 0 < η) :
    let A := G ∘ₗ C ∘ₗ G.adjoint + η • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    (block C (G ∘ₗ C) A).IsPositive ∧ (block C (G ∘ₗ C) A).ker = ⊥ := by
  dsimp only
  let A := G ∘ₗ C ∘ₗ G.adjoint + η • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hbase := block_explicit_positive C hC G
  have hdelta := bottom_positive (E := E) η hη.le
  have hp : (block C (G ∘ₗ C) A).IsPositive := by
    convert hbase.add hdelta using 1
    ext x
    apply (WithLp.linearEquiv 2 ℝ (E × ℝ)).injective
    simp [block, A, map_add, ← LinearMap.star_eq_adjoint]
    ring
  refine ⟨hp, ?_⟩
  apply bot_unique
  intro x hx
  have hzero : block C (G ∘ₗ C) A x = 0 := hx
  have hcros : inner ℝ x.fst (C (G.adjoint x.snd)) = x.snd * G (C x.fst) := by
    rw [← hC.isSymmetric, LinearMap.adjoint_inner_right]
    rfl
  have he : inner ℝ (block C (G ∘ₗ C) A x) x =
      inner ℝ (C (x.fst + G.adjoint x.snd)) (x.fst + G.adjoint x.snd) + η * x.snd^2 := by
    simp [block, A, map_add, inner_add_left, inner_add_right,
      ← LinearMap.adjoint_inner_right, hC.adjoint_eq, hcros, pow_two]
    ring
  have hs : inner ℝ (C (x.fst + G.adjoint x.snd)) (x.fst + G.adjoint x.snd) + η * x.snd^2 = 0 := by
    rw [← he, hzero, inner_zero_left]
  have hc := hC.inner_nonneg_left (x.fst + G.adjoint x.snd)
  have hy : x.snd = 0 := by
    have hle : η * x.snd^2 ≤ 0 := by linarith
    have hy2 : x.snd^2 = 0 := le_antisymm
      (by nlinarith only [hle, hη]) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hy2
  have hcx : C x.fst = 0 := by
    have ht := congrArg (fun p : WithLp 2 (E × ℝ) => p.fst) hzero
    simpa [block, hy] using ht
  have hxf : x.fst = 0 := by
    have hxker : x.fst ∈ C.ker := hcx
    simpa [hker] using hxker
  apply (WithLp.linearEquiv 2 ℝ (E × ℝ)).injective
  apply Prod.ext
  · simpa using hxf
  · simpa using hy

private theorem strict_escape (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hk : C.ker = ⊥) (hcyc : cyclicPrefix r C J)
    (hL : lowerSpace r C J ≠ ⊤) :
    ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ),
      (block C D A).IsPositive ∧ (block C D A).ker = ⊥ ∧
      lowerSpace r C J ≤ D.ker ∧
      (∀ k ≤ 2 * r + 1, moment (block C D A) (liftInput J) k = moment C J k) ∧
      moment (block C D A) (liftInput J) (2 * r + 2) ≠ moment C J (2 * r + 2) := by
  obtain ⟨D, hD, hDL⟩ := (lowerSpace r C J).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hL)
  obtain ⟨G, hG⟩ := factor_through C D (by rw [hk];exact bot_le)
  let A := G ∘ₗ C ∘ₗ G.adjoint + (1 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  obtain ⟨hB, hBk⟩ := strict_block_extension C hC hk G 1 zero_lt_one
  rw [hG] at hB hBk
  have hp := block_extension_realizes_prefix r (fun k => moment C J k) C J D A hC
    (fun _ _ => rfl) hB hDL
  refine ⟨D, A, hB, hBk, hDL, hp.1, ?_⟩
  intro heq
  apply adjoint_square_nonzero _ (nonzero_last_coupling C J r hcyc D hD hDL)
  rw [← hp.2.2, heq, sub_self]

def strictFutureUnique (N : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  ∀ (n : ℕ) (C' : State n →ₗ[ℝ] State n) (J' : U →ₗ[ℝ] State n),
    C'.IsPositive → C'.ker = ⊥ → matchesPrefix N M C' J' →
      ∀ k, moment C' J' k = moment C J k

def ordinary_flat_future_unique_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  1 ≤ r → C.IsPositive → matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
  let flat := Module.finrank ℝ (momentBlock M (r + 1) 0).range =
    Module.finrank ℝ (momentBlock M r 0).range
  (flat → futureUnique (2 * r + 1) M C J) ∧
    (C.ker = ⊥ → ((futureUnique (2 * r + 1) M C J ↔ flat) ∧
      (strictFutureUnique (2 * r + 1) M C J ↔ flat)))

/-- Ordinary flatness is sufficient and is necessary for a positive definite canonical state. -/
theorem ordinary_flat_future_unique (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : ordinary_flat_future_unique_statement r M C J := by
  intro hr hC hM hcyc
  dsimp only
  have hflat := ordinary_flat_span_iff r M C J hC.isSymmetric hM hcyc
  have hpos := positive_future_span_iff r M C J hC hM hcyc
  have hsuff (h : lowerSpace r C J = ⊤) : futureUnique (2 * r + 1) M C J := hpos.mpr (by rw [h, top_sup_eq])
  refine ⟨fun h => hsuff (hflat.mp h), ?_⟩
  intro hk
  have hf : futureUnique (2 * r + 1) M C J ↔ lowerSpace r C J = ⊤ := by simpa only [hk, sup_bot_eq] using hpos
  refine ⟨hf.trans hflat.symm, ?_, ?_⟩
  · intro hu
    apply hflat.mpr
    by_contra hL
    obtain ⟨D, A, hB, hBk, hD, hprefix, hneq⟩ := strict_escape r C J hC hk hcyc hL
    let q := (stdOrthonormalBasis ℝ (WithLp 2 (E × ℝ))).repr
    let CB := block C D A
    let JB := liftInput (F := ℝ) J
    have hp : matchesPrefix (2 * r + 1) M
        (q.toLinearMap ∘ₗ CB ∘ₗ q.symm.toLinearMap) (q.toLinearMap ∘ₗ JB) := by
      intro k hk
      rw [moment_transport]
      exact (hprefix k hk).trans (hM k hk)
    have hbk : (q.toLinearMap ∘ₗ CB ∘ₗ q.symm.toLinearMap).ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      have hz : CB (q.symm x) = 0 := q.injective (by simpa using hx)
      have hz' := LinearMap.ker_eq_bot'.mp hBk (q.symm x) hz
      simpa using congrArg q hz'
    have he := hu _ _ _ ((LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hB) hbk hp (2 * r + 2)
    rw [moment_transport] at he
    exact hneq he
  · intro h n C' J' hC' hk' hM'
    exact hsuff (hflat.mp h) n C' J' hC' hM'

private theorem scalar_map (A : ℝ →ₗ[ℝ] ℝ) : A = A 1 • LinearMap.id := by
  ext x
  simpa [mul_comm] using A.map_smul x (1 : ℝ)

private theorem scaled_block_positive (C : E →ₗ[ℝ] E) (hC : C.IsPositive)
    (G : E →ₗ[ℝ] ℝ) (t a : ℝ)
    (ha : t^2 * (G ∘ₗ C ∘ₗ G.adjoint) 1 ≤ a) :
    (block C (t • (G ∘ₗ C)) (a • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))).IsPositive := by
  let α := (G ∘ₗ C ∘ₗ G.adjoint) 1
  have hbase := block_explicit_positive C hC (t • G)
  have hscalar : (t • G) ∘ₗ C ∘ₗ (t • G).adjoint =
      (t^2 * α) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    rw [scalar_map ((t • G) ∘ₗ C ∘ₗ (t • G).adjoint)]
    congr 1
    simp [α, LinearMap.comp_apply, LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint,
      pow_two, mul_assoc]
  rw [hscalar] at hbase
  have hdelta := bottom_positive (E := E) (a - t^2 * α) (sub_nonneg.mpr ha)
  convert hbase.add hdelta using 1
  ext x
  apply (WithLp.linearEquiv 2 ℝ (E × ℝ)).injective
  simp [block, ← LinearMap.star_eq_adjoint, map_add, smul_add, add_smul, smul_smul]
  ring

private def TwoSidedScalingGoal (C : E →ₗ[ℝ] E) (D₀ : E →ₗ[ℝ] ℝ) (Λ : ℝ) : Prop :=
  0 < Λ → C.IsPositive → (Λ • LinearMap.id - C).IsPositive →
  C.ker ≤ D₀.ker → (Λ • LinearMap.id - C).ker ≤ D₀.ker →
  ∃ ε : ℝ, 0 < ε ∧
    (block C (ε • D₀) ((Λ / 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))).IsPositive ∧
    (Λ • LinearMap.id -
      block C (ε • D₀) ((Λ / 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))).IsPositive

private theorem two_sided_scaling (C : E →ₗ[ℝ] E) (D₀ : E →ₗ[ℝ] ℝ) (Λ : ℝ) :
    TwoSidedScalingGoal C D₀ Λ := by
  intro hΛ hC hCp hker hkerp
  let Cp := Λ • LinearMap.id - C
  obtain ⟨G, hG⟩ := factor_through C D₀ hker
  obtain ⟨K, hK⟩ := factor_through Cp D₀ hkerp
  let α := (G ∘ₗ C ∘ₗ G.adjoint) 1
  let β := (K ∘ₗ Cp ∘ₗ K.adjoint) 1
  have hα : 0 ≤ α := by
    have h := hC.conj_adjoint G
    simpa [α] using h.inner_nonneg_left (1 : ℝ)
  have hβ : 0 ≤ β := by
    have h := hCp.conj_adjoint K
    simpa [β, Cp] using h.inner_nonneg_left (1 : ℝ)
  let q := Λ / (2 * (1 + α + β))
  have hden : 0 < 2 * (1 + α + β) := by positivity
  have hq : 0 < q := div_pos hΛ hden
  let ε := Real.sqrt q
  have hε : 0 < ε := Real.sqrt_pos.mpr hq
  have hεsq : ε^2 = q := Real.sq_sqrt hq.le
  have hαb : ε^2 * α ≤ Λ / 2 := by
    rw [hεsq]
    dsimp [q]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hβb : (-ε)^2 * β ≤ Λ / 2 := by
    rw [neg_sq, hεsq]
    dsimp [q]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  refine ⟨ε, hε, ?_, ?_⟩
  · simpa only [hG] using scaled_block_positive C hC G ε (Λ / 2) hαb
  · have hp := scaled_block_positive Cp hCp K (-ε) (Λ / 2) hβb
    rw [hK] at hp
    convert hp using 1
    ext x
    apply (WithLp.linearEquiv 2 ℝ (E × ℝ)).injective
    simp [block, Cp, ← LinearMap.star_eq_adjoint, map_sub, smul_sub]
    apply Prod.ext <;> simp <;> first | ring | module

private def BoundedBlockGoal (C : E →ₗ[ℝ] E) (L : Submodule ℝ E) (Λ : ℝ) : Prop :=
  0 < Λ → C.IsPositive → (Λ • LinearMap.id - C).IsPositive →
  L ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker ≠ ⊤ →
  ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ), D ≠ 0 ∧ L ≤ D.ker ∧
    (block C D A).IsPositive ∧
    (Λ • LinearMap.id - block C D A).IsPositive

private theorem nonzero_bounded_extension (C : E →ₗ[ℝ] E)
    (L : Submodule ℝ E) (Λ : ℝ) : BoundedBlockGoal C L Λ := by
  intro hΛ hC hCp hL
  let K : Submodule ℝ E := L ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker
  have hproper : K < ⊤ := lt_top_iff_ne_top.mpr hL
  obtain ⟨D₀, hD₀, hker⟩ := Submodule.exists_le_ker_of_lt_top K hproper
  have hcinc : C.ker ≤ K := le_trans (show C.ker ≤ L ⊔ C.ker from le_sup_right) le_sup_left
  have hpinc : (Λ • LinearMap.id - C).ker ≤ K := le_sup_right
  have hlinc : L ≤ K := le_trans (show L ≤ L ⊔ C.ker from le_sup_left) le_sup_left
  have hk : C.ker ≤ D₀.ker := hcinc.trans hker
  have hkp : (Λ • LinearMap.id - C).ker ≤ D₀.ker := hpinc.trans hker
  have hlk : L ≤ D₀.ker := hlinc.trans hker
  obtain ⟨ε, hε, hB, hBp⟩ := two_sided_scaling C D₀ Λ hΛ hC hCp hk hkp
  refine ⟨ε • D₀, (Λ/2) • LinearMap.id, ?_, ?_, hB, hBp⟩
  · exact smul_ne_zero hε.ne' hD₀
  · intro x hx
    have hz : D₀ x = 0 := hlk hx
    change ε • D₀ x = 0
    rw [hz, smul_zero]

private theorem nonzero_bounded_nonneg_extension (C : E →ₗ[ℝ] E)
    (L : Submodule ℝ E) (Λ : ℝ) (hΛ : 0 ≤ Λ) (hC : C.IsPositive)
    (hCp : (Λ • LinearMap.id - C).IsPositive)
    (hL : L ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker ≠ ⊤) :
    ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ), D ≠ 0 ∧ L ≤ D.ker ∧
      (block C D A).IsPositive ∧ (Λ • LinearMap.id - block C D A).IsPositive := by
  have hpos : 0 < Λ := by
    by_contra hn
    have hz : Λ = 0 := le_antisymm (le_of_not_gt hn) hΛ
    have hc0 : C = 0 := le_antisymm
      ((LinearMap.le_def).mpr (by simpa [hz] using hCp))
      (LinearMap.nonneg_iff_isPositive.mpr hC)
    apply hL
    simp [hc0]
  exact nonzero_bounded_extension C L Λ hpos hC hCp hL

private theorem bounded_escape {U : Type}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hC : C.IsPositive) (hCp : (Λ • LinearMap.id - C).IsPositive)
    (hcyc : cyclicPrefix r C J)
    (hL : lowerSpace r C J ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker ≠ ⊤) :
    ∃ (D : E →ₗ[ℝ] ℝ) (A : ℝ →ₗ[ℝ] ℝ),
      (block C D A).IsPositive ∧ (Λ • LinearMap.id - block C D A).IsPositive ∧
      lowerSpace r C J ≤ D.ker ∧
      (∀ k ≤ 2 * r + 1, moment (block C D A) (liftInput J) k = moment C J k) ∧
      moment (block C D A) (liftInput J) (2 * r + 2) ≠ moment C J (2 * r + 2) := by
  obtain ⟨D, A, hd, hl, hp, hpb⟩ := nonzero_bounded_nonneg_extension C
    (lowerSpace r C J) Λ hΛ hC hCp hL
  have hlast := nonzero_last_coupling C J r hcyc D hd hl
  have hb := block_extension_realizes_prefix r (fun k => moment C J k) C J D A hC
    (fun _ _ => rfl) hp hl
  refine ⟨D, A, hp, hpb, hl, hb.1, ?_⟩
  intro heq
  have hz : (D ∘ₗ (C^r) ∘ₗ J).adjoint ∘ₗ (D ∘ₗ (C^r) ∘ₗ J) = 0 := by
    rw [← hb.2.2, heq, sub_self]
  exact adjoint_square_nonzero _ hlast hz

def boundedFutureUnique (N : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (Λ : ℝ) : Prop :=
  ∀ (n : ℕ) (C' : State n →ₗ[ℝ] State n) (J' : U →ₗ[ℝ] State n),
    C'.IsPositive → (Λ • LinearMap.id - C').IsPositive → matchesPrefix N M C' J' →
    ∀ k, moment C' J' k = moment C J k

def bounded_future_unique_iff_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (Λ : ℝ) : Prop :=
  0 ≤ Λ → C.IsPositive → (Λ • LinearMap.id - C).IsPositive →
  matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
  (boundedFutureUnique (2 * r + 1) M C J Λ ↔
    lowerSpace r C J ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker = ⊤)

private theorem bounded_future_of_span (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (Λ : ℝ)
    (hC : C.IsPositive) (hCp : (Λ • LinearMap.id - C).IsPositive)
    (hM : matchesPrefix (2 * r + 1) M C J) (hcyc : cyclicPrefix r C J)
    (hspan : lowerSpace r C J ⊔ C.ker ⊔ (Λ • LinearMap.id - C).ker = ⊤) :
    boundedFutureUnique (2 * r + 1) M C J Λ := by
  intro n C' J' hC' hCp' hM'
  obtain ⟨q, hq, hp⟩ := prefix_embedding r M C J C' J' hC.isSymmetric hC'.isSymmetric hM hM' hcyc
  have hpp : ∀ (x y : E), inner ℝ (q x) (((Λ • LinearMap.id - C') : State n →ₗ[ℝ] State n) (q y)) =
      inner ℝ x (((Λ • LinearMap.id - C) : E →ₗ[ℝ] E) y) := by
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_sub_right, inner_smul_right, q.inner_map_map, hp]
  have hkp := embedding_residual_kernel (Λ • LinearMap.id - C)
    (Λ • LinearMap.id - C') hCp' q hpp
  have hkp' : (Λ • LinearMap.id - C).ker ≤
      (C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C).ker := by
    intro x hx
    have hz := hkp hx
    change ((Λ • LinearMap.id - C') : State n →ₗ[ℝ] State n) (q x) - q (((Λ • LinearMap.id - C) : E →ₗ[ℝ] E) x) = 0 at hz
    change C' (q x) - q (C x) = 0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul] at hz
    have hn : C' (q x) - q (C x) = -((Λ • q x - C' (q x)) - (Λ • q x - q (C x))) := by module
    rw [hn, hz, neg_zero]
  have hz : C' ∘ₗ q.toLinearMap - q.toLinearMap ∘ₗ C = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hspan]
    exact sup_le (sup_le (embedding_residual_low r C J C' J' q hq)
      (embedding_residual_kernel C C' hC' q hp)) hkp'
  exact intertwining_moments q C J C' J' (sub_eq_zero.mp hz).symm
    (by simpa [Module.End.one_eq_id] using hq 0 (by omega))

/-- A common spectral upper bound adds the upper endpoint kernel to the uniqueness criterion. -/
theorem bounded_future_unique_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (Λ : ℝ) :
    bounded_future_unique_iff_statement r M C J Λ := by
  intro hΛ hC hCp hM hcyc
  refine ⟨?_, bounded_future_of_span r M C J Λ hC hCp hM hcyc⟩
  intro huni
  by_contra hspan
  obtain ⟨D, A, hB, hBp, hD, hprefix, hneq⟩ := bounded_escape r C J Λ hΛ hC hCp hcyc hspan
  let q := (stdOrthonormalBasis ℝ (WithLp 2 (E × ℝ))).repr
  let CB := block C D A
  let JB := liftInput (F := ℝ) J
  have hp : matchesPrefix (2 * r + 1) M
      (q.toLinearMap ∘ₗ CB ∘ₗ q.symm.toLinearMap) (q.toLinearMap ∘ₗ JB) := by
    intro k hk
    rw [moment_transport]
    exact (hprefix k hk).trans (hM k hk)
  have hbq : (Λ • LinearMap.id - q.toLinearMap ∘ₗ CB ∘ₗ q.symm.toLinearMap).IsPositive := by
    convert (LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hBp using 1
    ext x
    simp [CB]
  have he := huni _ _ _ ((LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hB) hbq hp (2 * r + 2)
  rw [moment_transport] at he
  exact hneq he

end D5.S3.Observer.PositiveMoments.PrefixFutureUniqueness
