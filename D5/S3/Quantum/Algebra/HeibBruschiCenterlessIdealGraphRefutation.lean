/- GID: D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.claim; result=D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.result; claim=D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.claim
   digest: Refutes Heib-Bruschi Conjecture 83 over every field with the two-dimensional affine Lie algebra. -/

/-
proof_shape (definitions, with no independent proof claim):
  IsAdmissible: definition; Edge: definition; IdealGraphProperty: definition;
  HasProperIdealGraphSubset: definition; conjectureOver: definition; claim: definition;
  Affine: definition; affineBasis: definition.
proof_shape (same-delivery helpers inlined):
  affineAddCommGroup: bind-only; consumer: affineLieRing.
  affineModule: bind-only; consumer: affineLieAlgebra.
  affineLieRing: bind-only (coordinate ring identities); consumer: conjecture_fails.
  affineLieAlgebra: bind-only (coordinate scalar identity); consumer: conjecture_fails.
  affineBasis_admissible: bind-only (four coordinate computations); consumer: conjecture_fails.
  affine_center_zero: bind-only (center membership and coordinate normalization);
    consumer: conjecture_fails.
  affineBasis_proper_subset: bind-only (singleton and first-coordinate normalization);
    consumer: conjecture_fails.
  ideal_contains_y: bind-only (nonzero-element witness, ideal closure and inverse-scalar
    normalization in the two coordinate cases); consumer: internal_has_top.
  internal_has_top: bind-only (internal-sum independence and spanning, common-vector
    contradiction, and lattice bindings); consumer: conjecture_fails.
  admissible_map: bind-only (basis and Lie-equivalence bindings); consumer: conjecture_fails.
  proper_subset_map: bind-only (basis bindings and equivalence injectivity);
    consumer: conjecture_fails.
  conjecture_fails: bind-only (the affine model, the normalized coordinate facts, internal-sum
    bindings and top-ideal basis transport); consumer: result.
  result: bind-only (the same proof after specialization to the rational field).
escape_witness: none under the normalization criterion of CLAUDE.md §3.2.
admission_basis: open-problem-resolution (#13676; Refuted)
Frozen dependencies (direct): none; Mathlib only.
Registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.Lie.Abelian

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Algebra.HeibBruschiCenterlessIdealGraphRefutation

open Module

variable {K L : Type} [Field K] [LieRing L] [LieAlgebra K L]

/-- Eq. (7) of arXiv:2601.16161 with the convention δ(j,k) = 0 (here `none`, x₀ = 0) iff α_jk = 0. -/
def IsAdmissible {n : ℕ} (b : Basis (Fin n) K L) : Prop :=
  ∃ (α : Fin n → Fin n → K) (δ : Fin n → Fin n → Option (Fin n)),
    (∀ j k, α j k = -α k j) ∧ (∀ j k, δ j k = δ k j) ∧
    (∀ j k, δ j k = none ↔ α j k = 0) ∧
    ∀ j k, ⁅b j, b k⁆ = α j k • (δ j k).elim 0 b

/-- An edge from `j` to `l` labelled `k` of the minimal graph (Algorithm 1). -/
def Edge {n : ℕ} (b : Basis (Fin n) K L) (j k l : Fin n) : Prop :=
  ∃ κ : K, κ ≠ 0 ∧ ⁅b j, b k⁆ = κ • b l

/-- Definition 75: no edge leaves `W`. -/
def IdealGraphProperty {n : ℕ} (b : Basis (Fin n) K L) (W : Set (Fin n)) : Prop :=
  ∀ j k l, Edge b j k l → j ∈ W → l ∈ W

def HasProperIdealGraphSubset {n : ℕ} (b : Basis (Fin n) K L) : Prop :=
  ∃ W : Set (Fin n), W.Nonempty ∧ W ≠ Set.univ ∧ IdealGraphProperty b W

/-- Conjecture 83 over the field `K`. -/
def conjectureOver (K : Type) [Field K] : Prop :=
  ∀ (L : Type) [LieRing L] [LieAlgebra K L] (n : ℕ) (b : Basis (Fin n) K L),
    IsAdmissible b → LieAlgebra.center K L = ⊥ →
      ¬ HasProperIdealGraphSubset b ∨
      ∃ (J : Type) (_ : DecidableEq J) (I : J → LieIdeal K L),
        DirectSum.IsInternal (fun j => ((I j : LieSubalgebra K L).toSubmodule)) ∧
        ∀ j, LieAlgebra.center K (I j) = ⊥ ∧
          ∀ (m : ℕ) (c : Basis (Fin m) K (I j)), IsAdmissible c →
            ¬ HasProperIdealGraphSubset c

/-- The paper's convention: `𝔽` is any field. -/
def claim : Prop := ∀ (K : Type) [Field K], conjectureOver K

private def Affine (K : Type) := K × K

private instance affineAddCommGroup : AddCommGroup (Affine K) :=
  inferInstanceAs (AddCommGroup (K × K))

private instance affineModule : Module K (Affine K) :=
  inferInstanceAs (Module K (K × K))

private instance affineLieRing : LieRing (Affine K) where
  bracket x y := (0, x.1 * y.2 - y.1 * x.2)
  add_lie x y z := by
    apply Prod.ext
    · change (0 : K) = 0 + 0
      ring
    · change (x.1 + y.1) * z.2 - z.1 * (x.2 + y.2) =
        (x.1 * z.2 - z.1 * x.2) + (y.1 * z.2 - z.1 * y.2)
      ring
  lie_add x y z := by
    apply Prod.ext
    · change (0 : K) = 0 + 0
      ring
    · change x.1 * (y.2 + z.2) - (y.1 + z.1) * x.2 =
        (x.1 * y.2 - y.1 * x.2) + (x.1 * z.2 - z.1 * x.2)
      ring
  lie_self x := by
    apply Prod.ext
    · rfl
    · change x.1 * x.2 - x.1 * x.2 = 0
      ring
  leibniz_lie x y z := by
    apply Prod.ext
    · change (0 : K) = 0 + 0
      ring
    · change x.1 * (y.1 * z.2 - z.1 * y.2) - 0 * x.2 =
        (0 * z.2 - z.1 * (x.1 * y.2 - y.1 * x.2)) +
          (y.1 * (x.1 * z.2 - z.1 * x.2) - 0 * y.2)
      ring

private instance affineLieAlgebra : LieAlgebra K (Affine K) where
  lie_smul t x y := by
    apply Prod.ext
    · change (0 : K) = t * 0
      ring
    · change x.1 * (t * y.2) - (t * y.1) * x.2 = t * (x.1 * y.2 - y.1 * x.2)
      ring

private def affineBasis : Basis (Fin 2) K (Affine K) := Basis.finTwoProd K

private theorem affineBasis_admissible : IsAdmissible (affineBasis (K := K)) := by
  have b0 : affineBasis (K := K) 0 = (1, 0) := Basis.finTwoProd_zero K
  have b1 : affineBasis (K := K) 1 = (0, 1) := Basis.finTwoProd_one K
  let α : Fin 2 → Fin 2 → K := fun j k =>
    if j = k then 0 else if j = 0 then 1 else -1
  let δ : Fin 2 → Fin 2 → Option (Fin 2) := fun j k =>
    if j = k then none else some 1
  refine ⟨α, δ, ?_, ?_, ?_, ?_⟩
  · intro j k
    fin_cases j <;> fin_cases k <;> simp [α]
  · intro j k
    fin_cases j <;> fin_cases k <;> rfl
  · intro j k
    fin_cases j <;> fin_cases k <;> simp [α, δ]
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅affineBasis (K := K) 0, affineBasis 0⁆ = (0 : K) • (0 : Affine K)
      rw [b0]
      change (0, (1 : K) * 0 - 1 * 0) = (0 * 0, 0 * 0)
      simp
    · change ⁅affineBasis (K := K) 0, affineBasis 1⁆ = (1 : K) • affineBasis 1
      rw [b0, b1]
      change (0, (1 : K) * 1 - 0 * 0) = (1 * 0, 1 * 1)
      simp
    · change ⁅affineBasis (K := K) 1, affineBasis 0⁆ = (-1 : K) • affineBasis 1
      rw [b0, b1]
      change (0, (0 : K) * 0 - 1 * 1) = ((-1) * 0, (-1) * 1)
      simp
    · change ⁅affineBasis (K := K) 1, affineBasis 1⁆ = (0 : K) • (0 : Affine K)
      rw [b1]
      change (0, (0 : K) * 1 - 0 * 1) = (0 * 0, 0 * 0)
      simp

private theorem affine_center_zero : LieAlgebra.center K (Affine K) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  intro z hz
  have hc := (LieModule.mem_maxTrivSubmodule K (Affine K) (Affine K) z).mp hz
  have hx := congrArg Prod.snd (hc (1, 0))
  have hy := congrArg Prod.snd (hc (0, 1))
  change 1 * z.2 - z.1 * 0 = 0 at hx
  change 0 * z.2 - z.1 * 1 = 0 at hy
  apply Prod.ext
  · change z.1 = 0
    simpa using hy
  · change z.2 = 0
    simpa using hx

private theorem affineBasis_proper_subset :
    HasProperIdealGraphSubset (affineBasis (K := K)) := by
  refine ⟨{1}, ⟨1, Set.mem_singleton 1⟩, ?_, ?_⟩
  · intro h
    have h0 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h.symm ▸ Set.mem_univ 0
    simp at h0
  · intro j k l he _
    fin_cases l
    · obtain ⟨κ, hκ, he⟩ := he
      have b0 : affineBasis (K := K) 0 = (1, 0) := Basis.finTwoProd_zero K
      change ⁅affineBasis j, affineBasis k⁆ = κ • affineBasis 0 at he
      rw [b0] at he
      have hc := congrArg Prod.fst he
      change (0 : K) = κ * 1 at hc
      exact (hκ (by simpa using hc.symm)).elim
    · exact Set.mem_singleton 1

private theorem ideal_contains_y (I : LieIdeal K (Affine K)) (hI : I ≠ ⊥) :
    (0, 1) ∈ I := by
  have hsub : I.toSubmodule ≠ ⊥ := by
    intro hs
    exact hI ((LieSubmodule.toSubmodule_inj I ⊥).mp hs)
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff I.toSubmodule).mp hsub
  by_cases ha : z.1 = 0
  · have hb : z.2 ≠ 0 := by
      intro hb
      exact hz0 (Prod.ext ha hb)
    have he : z.2⁻¹ • z = (0, 1) := by
      apply Prod.ext
      · change z.2⁻¹ * z.1 = 0
        rw [ha, mul_zero]
      · change z.2⁻¹ * z.2 = 1
        exact inv_mul_cancel₀ hb
    rw [← he]
    exact I.toSubmodule.smul_mem _ hz
  · have hbr : (0, z.1) ∈ I := by
      have hm := lie_mem_left K (Affine K) I z (0, 1) hz
      change (0, z.1 * 1 - 0 * z.2) ∈ I at hm
      simpa only [mul_one, zero_mul, sub_zero] using hm
    have he : z.1⁻¹ • ((0, z.1) : Affine K) = (0, 1) := by
      apply Prod.ext
      · change z.1⁻¹ * 0 = 0
        exact mul_zero _
      · change z.1⁻¹ * z.1 = 1
        exact inv_mul_cancel₀ ha
    rw [← he]
    exact I.toSubmodule.smul_mem _ hbr

private theorem internal_has_top {J : Type} [DecidableEq J]
    (I : J → LieIdeal K (Affine K))
    (h : DirectSum.IsInternal (fun j => (I j : LieSubalgebra K (Affine K)).toSubmodule)) :
    ∃ j, I j = ⊤ := by
  classical
  have hex : ∃ j, I j ≠ ⊥ := by
    by_contra hn
    have hn : ∀ j, I j = ⊥ := by
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    have hle : (⊤ : Submodule K (Affine K)) ≤ ⊥ := by
      rw [← h.submodule_iSup_eq_top]
      refine iSup_le fun j => ?_
      rw [hn j]
      exact bot_le
    have hy : ((0, 1) : Affine K) ∈ (⊥ : Submodule K (Affine K)) :=
      hle (by trivial)
    have hz : ((0, 1) : Affine K) = 0 := hy
    exact one_ne_zero (congrArg Prod.snd hz)
  obtain ⟨j, hj⟩ := hex
  have hzero : ∀ i, i ≠ j → I i = ⊥ := by
    intro i hij
    by_contra hi
    have hd := h.submodule_iSupIndep.pairwiseDisjoint hij
    have hz := Submodule.disjoint_def.mp hd (0, 1)
      (ideal_contains_y (I i) hi) (ideal_contains_y (I j) hj)
    exact one_ne_zero (congrArg Prod.snd hz)
  refine ⟨j, ?_⟩
  apply LieSubmodule.toSubmodule_injective
  change (I j : LieSubalgebra K (Affine K)).toSubmodule = ⊤
  apply le_antisymm le_top
  rw [← h.submodule_iSup_eq_top]
  refine iSup_le fun i => ?_
  by_cases hi : i = j
  · subst i
    exact le_rfl
  · rw [hzero i hi]
    exact bot_le

private theorem admissible_map {M : Type} [LieRing M] [LieAlgebra K M] {n : ℕ}
    (b : Basis (Fin n) K L) (e : L ≃ₗ⁅K⁆ M) (hb : IsAdmissible b) :
    IsAdmissible (b.map e.toLinearEquiv) := by
  obtain ⟨α, δ, ha, hd, hn, hbr⟩ := hb
  refine ⟨α, δ, ha, hd, hn, ?_⟩
  intro j k
  calc
    ⁅(b.map e.toLinearEquiv) j, (b.map e.toLinearEquiv) k⁆ = e ⁅b j, b k⁆ := by
      rw [Basis.map_apply, Basis.map_apply]
      exact (e.map_lie _ _).symm
    _ = e (α j k • (δ j k).elim 0 b) := congrArg e (hbr j k)
    _ = α j k • (δ j k).elim 0 (b.map e.toLinearEquiv) := by
      cases hδ : δ j k with
      | none =>
        change e (α j k • 0) = α j k • 0
        rw [smul_zero, map_zero, smul_zero]
      | some l =>
        change e (α j k • b l) = α j k • (b.map e.toLinearEquiv) l
        rw [map_smul, Basis.map_apply]
        rfl

private theorem proper_subset_map {M : Type} [LieRing M] [LieAlgebra K M] {n : ℕ}
    (b : Basis (Fin n) K L) (e : L ≃ₗ⁅K⁆ M) (hb : HasProperIdealGraphSubset b) :
    HasProperIdealGraphSubset (b.map e.toLinearEquiv) := by
  obtain ⟨W, hne, hproper, hgraph⟩ := hb
  refine ⟨W, hne, hproper, ?_⟩
  intro j k l he hj
  apply hgraph j k l ?_ hj
  obtain ⟨κ, hκ, he⟩ := he
  refine ⟨κ, hκ, e.injective ?_⟩
  change e ⁅b j, b k⁆ = e (κ • b l)
  rw [e.map_lie, map_smul]
  simpa only [Basis.map_apply, LieEquiv.coe_toLinearEquiv] using he

theorem conjecture_fails (K : Type) [Field K] : ¬ conjectureOver K := by
  intro hc
  have h := hc (Affine K) 2 (affineBasis (K := K))
    affineBasis_admissible affine_center_zero
  obtain h | ⟨J, hJ, I, hsum, hcomponents⟩ := h
  · exact h affineBasis_proper_subset
  · let _ : DecidableEq J := hJ
    obtain ⟨j, hj⟩ := internal_has_top I hsum
    have hgraph := (hcomponents j).2
    rw [hj] at hgraph
    let e : Affine K ≃ₗ⁅K⁆ (⊤ : LieIdeal K (Affine K)) :=
      (LieIdeal.topEquiv (R := K) (L := Affine K)).symm
    exact hgraph 2 ((affineBasis (K := K)).map e.toLinearEquiv)
      (admissible_map _ e affineBasis_admissible)
      (proper_subset_map _ e affineBasis_proper_subset)

theorem result : ¬ claim := fun h => conjecture_fails ℚ (h ℚ)

end D5.S3.Quantum.Algebra.HeibBruschiCenterlessIdealGraphRefutation
