/- GID: D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every linear N-qubit doily has an odd number of negative lines. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

/-! Canonical Pauli line signs on nondegenerate binary four-spaces.

The fifteen isotropic triples are transported along a symplectic linear equivalence.
For any four single-qubit binary labels, the sum of their fifteen multiplication
exponents is twice the local pairing of the first symplectic pair. This identity is
checked on the fixed four-generator coordinate space. Multiplication over all qubits
makes the product of all line phases minus one. These phases are the actual matrix
line signs, so the number of negative lines is odd.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 32

open scoped BigOperators
open Module
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_smul)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (letterProduct letterPhase letter_mul letter_comm word_mul word_comm_sign wordUnit)
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization (sign_sum)
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (complexSign)

namespace D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

noncomputable section

/-- The unsigned single-qubit label, with `(1,1)` represented by `Y = iXZ`. -/
def canonicalLabel (p : ZMod 2 × ZMod 2) : Pauli :=
  if p.1 = 0 then (if p.2 = 0 then .I else .Z)
  else (if p.2 = 0 then .X else .Y)

/-- The literal tensor product of the canonical single-qubit labels. -/
def observable {N : ℕ} (v : Fin N → ZMod 2 × ZMod 2) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  wordOp fun j => canonicalLabel (v j)

/-- The binary symplectic form expressing Pauli commutation. -/
def B {N : ℕ} (v w : Fin N → ZMod 2 × ZMod 2) : ZMod 2 :=
  ∑ j, ((v j).1 * (w j).2 + (v j).2 * (w j).1)

/-- A four-dimensional subspace with nondegenerate restricted symplectic form. -/
def IsLinearDoily {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) : Prop :=
  Module.finrank (ZMod 2) U = 4 ∧
    ∀ u ∈ U, (∀ w ∈ U, B u w = 0) → u = 0

/-- The projective points over the binary field are precisely the nonzero vectors. -/
def points {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Fin N → ZMod 2 × ZMod 2) := by
  classical
  exact Finset.univ.filter fun v => v ∈ U ∧ v ≠ 0

/-- The isotropic lines: three distinct nonzero vectors `{u,v,u+v}` in the subspace. -/
def lines {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Finset (Fin N → ZMod 2 × ZMod 2)) := by
  classical
  exact (points U).powerset.filter fun l =>
    l.card = 3 ∧ ∀ u ∈ l, ∀ v ∈ l, u ≠ v → u + v ∈ l ∧ B u v = 0

/-- Product of the three canonical observables; isotropy makes its order immaterial. -/
def lineProduct {N : ℕ} (l : Finset (Fin N → ZMod 2 × ZMod 2)) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (l.toList.map observable).prod

/-- A line is negative exactly when its three observables multiply to minus identity. -/
def negativeLines {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Finset (Fin N → ZMod 2 × ZMod 2)) := by
  classical
  exact (lines U).filter fun l => lineProduct l = -1

/-- The all-qubit parity assertion for linear doilies. -/
def claim : Prop :=
  ∀ (N : ℕ), 2 ≤ N →
    ∀ U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2),
      IsLinearDoily U → Odd (negativeLines U).card

/-- The multiplication exponent in the fourth roots of unity. -/
def localExponent (u v : ZMod 2 × ZMod 2) : ZMod 4 :=
  (u.1.val * u.2.val : ℕ) + (v.1.val * v.2.val : ℕ) -
    ((u + v).1.val * (u + v).2.val : ℕ) + 2 * (u.2.val * v.1.val : ℕ)

def phase {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) : ℂ :=
  ∏ j, AddChar.zmodChar 4 Complex.I_pow_four (localExponent (u j) (v j))

private theorem local_mul (u v : ZMod 2 × ZMod 2) :
    pauliMatrix (canonicalLabel u) * pauliMatrix (canonicalLabel v) =
      AddChar.zmodChar 4 Complex.I_pow_four (localExponent u v) •
        pauliMatrix (canonicalLabel (u + v)) := by
  have hp : letterPhase (canonicalLabel u) (canonicalLabel v) =
      AddChar.zmodChar 4 Complex.I_pow_four (localExponent u v) := by
    rcases u with ⟨x, z⟩
    rcases v with ⟨y, t⟩
    fin_cases x <;> fin_cases z <;> fin_cases y <;> fin_cases t
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (Complex.I : ℂ) = Complex.I ^ 1
      norm_num [pow_succ, Complex.I_sq]
    · change (-Complex.I : ℂ) = Complex.I ^ 3
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (-Complex.I : ℂ) = Complex.I ^ 3
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (Complex.I : ℂ) = Complex.I ^ 1
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
    · change (Complex.I : ℂ) = Complex.I ^ 1
      norm_num [pow_succ, Complex.I_sq]
    · change (-Complex.I : ℂ) = Complex.I ^ 3
      norm_num [pow_succ, Complex.I_sq]
    · change (1 : ℂ) = Complex.I ^ 0
      norm_num [pow_succ, Complex.I_sq]
  have hl : letterProduct (canonicalLabel u) (canonicalLabel v) = canonicalLabel (u + v) := by
    rcases u with ⟨x, z⟩
    rcases v with ⟨y, t⟩
    fin_cases x <;> fin_cases z <;> fin_cases y <;> fin_cases t <;> rfl
  simpa only [hp, hl] using letter_mul (canonicalLabel u) (canonicalLabel v)

private theorem local_comm (u v : ZMod 2 × ZMod 2) :
    pauliMatrix (canonicalLabel u) * pauliMatrix (canonicalLabel v) =
      complexSign (u.1 * v.2 + u.2 * v.1) •
        (pauliMatrix (canonicalLabel v) * pauliMatrix (canonicalLabel u)) := by
  have hs : (sgn (canonicalLabel u) (canonicalLabel v) : ℂ) =
      complexSign (u.1 * v.2 + u.2 * v.1) := by
    rcases u with ⟨x, z⟩
    rcases v with ⟨y, t⟩
    fin_cases x <;> fin_cases z <;> fin_cases y <;> fin_cases t
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((-1 : ℤ) : ℂ) = (-1 : ℂ)
      norm_num
    · change ((1 : ℤ) : ℂ) = (1 : ℂ)
      norm_num
  simpa only [hs] using letter_comm (canonicalLabel u) (canonicalLabel v)

private theorem observable_mul {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable v = phase u v • observable (u + v) := by
  classical
  unfold observable
  rw [word_mul]
  unfold wordOp
  rw [← tensor_smul]
  simp_rw [← letter_mul, local_mul]
  exact tensor_smul _ _

private theorem observable_sq {N : ℕ} (u : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable u = 1 := by
  exact (wordUnit (fun j => canonicalLabel (u j))).val_inv

private theorem observable_comm {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable v = complexSign (B u v) • (observable v * observable u) := by
  classical
  unfold observable
  rw [word_comm_sign]
  unfold wordOp
  rw [tensor_mul, ← tensor_smul]
  conv_lhs => arg 1; ext i; rw [← letter_comm, local_comm]
  rw [tensor_smul, ← sign_sum]
  rfl

private theorem local_phase_sq (u v : ZMod 2 × ZMod 2) :
    AddChar.zmodChar 4 Complex.I_pow_four (localExponent u v) ^ 2 =
      complexSign (u.1 * v.2 + u.2 * v.1) := by
  rcases u with ⟨x, z⟩
  rcases v with ⟨y, t⟩
  fin_cases x <;> fin_cases z <;> fin_cases y <;> fin_cases t
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 1) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 3) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 3) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 1) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 1) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 3) ^ 2 = (-1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]
  · change (Complex.I ^ 0) ^ 2 = (1 : ℂ)
    norm_num [pow_succ, Complex.I_sq]

private theorem phase_sq {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) :
    phase u v ^ 2 = complexSign (B u v) := by
  unfold phase
  rw [← Finset.prod_pow]
  simp_rw [local_phase_sq]
  exact (sign_sum _ _).symm

private theorem triple_sign {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2)
    (h : B u v = 0) :
    observable u * observable v * observable (u + v) = 1 ∨
      observable u * observable v * observable (u + v) = -1 := by
  have hs : phase u v = 1 ∨ phase u v = -1 := by
    apply sq_eq_one_iff.mp
    rw [phase_sq, h]
    rfl
  rw [observable_mul, smul_mul_assoc, observable_sq]
  rcases hs with hs | hs
  · simp [hs]
  · simp [hs]

private theorem line_sign {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2))
    (l : Finset (Fin N → ZMod 2 × ZMod 2)) (hl : l ∈ lines U) :
    lineProduct l = 1 ∨ lineProduct l = -1 := by
  classical
  have hl' : l ⊆ points U ∧ l.card = 3 ∧
      ∀ u ∈ l, ∀ v ∈ l, u ≠ v → u + v ∈ l ∧ B u v = 0 := by
    simpa only [lines, Finset.mem_filter, Finset.mem_powerset] using hl
  obtain ⟨u, v, w, hlist⟩ := List.length_eq_three.mp
    (l.length_toList.trans hl'.2.1)
  have hdistinct := l.nodup_toList
  rw [hlist] at hdistinct
  have huv : u ≠ v := by
    intro h
    exact (List.nodup_cons.mp hdistinct).1 (by simp [h])
  have hu : u ∈ l := Finset.mem_toList.mp (by simp [hlist])
  have hv : v ∈ l := Finset.mem_toList.mp (by simp [hlist])
  have hu0 : u ≠ 0 := (Finset.mem_filter.mp (hl'.1 hu)).2.2
  have hv0 : v ≠ 0 := (Finset.mem_filter.mp (hl'.1 hv)).2.2
  obtain ⟨hsum, hcomm⟩ := hl'.2.2 u hu v hv huv
  have hsum' : u + v = u ∨ u + v = v ∨ u + v = w := by
    simpa only [← Finset.mem_toList, hlist, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] using hsum
  have hw : u + v = w := by
    rcases hsum' with h | h | h
    · exact False.elim (hv0 (add_left_cancel (h.trans (add_zero u).symm)))
    · exact False.elim (hu0 (add_right_cancel (h.trans (zero_add v).symm)))
    · exact h
  unfold lineProduct
  rw [hlist]
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ← mul_assoc, ← hw] using triple_sign u v hcomm

private def modelForm (a b : Fin 4 → ZMod 2) : ZMod 2 :=
  a 0 * b 1 + a 1 * b 0 + a 2 * b 3 + a 3 * b 2

private theorem B_add_left {N : ℕ} (u v w : Fin N → ZMod 2 × ZMod 2) :
    B (u + v) w = B u w + B v w := by
  unfold B
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
  ring

private theorem B_smul_left {N : ℕ} (c : ZMod 2) (u v : Fin N → ZMod 2 × ZMod 2) :
    B (c • u) v = c * B u v := by
  unfold B
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem B_comm {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) : B u v = B v u := by
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem B_add_right {N : ℕ} (u v w : Fin N → ZMod 2 × ZMod 2) :
    B u (v + w) = B u v + B u w := by
  rw [B_comm, B_add_left, B_comm v u, B_comm w u]

theorem B_self {N : ℕ} (u : Fin N → ZMod 2 × ZMod 2) : B u u = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [mul_comm (u j).2 (u j).1]
  exact CharTwo.add_self_eq_zero _

private theorem symplectic_coordinates {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) (hU : IsLinearDoily U) :
    ∃ e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U,
      ∀ a b, B (e a : Fin N → ZMod 2 × ZMod 2) (e b : Fin N → ZMod 2 × ZMod 2) = modelForm a b := by
  classical
  let form : LinearMap.BilinForm (ZMod 2) U :=
    { toFun := fun u =>
        { toFun := fun v => B (u : Fin N → ZMod 2 × ZMod 2)
            (v : Fin N → ZMod 2 × ZMod 2)
          map_add' := fun v w => B_add_right _ _ _
          map_smul' := fun c v => by
            change B (u : Fin N → ZMod 2 × ZMod 2) (c • (v : Fin N → ZMod 2 × ZMod 2)) = _
            rw [B_comm, B_smul_left, B_comm]
            rfl }
      map_add' := fun u v => by ext w; exact B_add_left _ _ _
      map_smul' := fun c u => by ext v; exact B_smul_left _ _ _ }
  have halt : form.IsAlt := fun u => B_self (u : Fin N → ZMod 2 × ZMod 2)
  have hnd : form.Nondegenerate := by
    apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft halt.isRefl).mpr
    intro u hu
    apply Subtype.ext
    exact hU.2 u u.property (fun w hw => hu ⟨w, hw⟩)
  obtain ⟨n, b, hb⟩ :=
    D5.S3.QuadraticForms.SymplecticBasis.exists_isSymplecticBasis halt hnd
  have hdim : Module.finrank (ZMod 2) U = n + n := by
    simpa using Module.finrank_eq_card_basis b
  have hn : n = 2 := by have h4 := hU.1; omega
  subst n
  let idx : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
    Equiv.ofBijective ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1] (by decide)
  let c : Basis (Fin 4) (ZMod 2) U := b.reindex idx.symm
  have hrev (i j : Fin 2) :
      form (b (Sum.inr i)) (b (Sum.inl j)) =
        form (b (Sum.inl j)) (b (Sum.inr i)) := B_comm _ _
  have hpair : ∀ i j : Fin 4,
      form (c i) (c j) = modelForm (Pi.single i 1) (Pi.single j 1) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [c, idx, Basis.reindex_apply, hrev, hb.inl_inl, hb.inr_inr,
        hb.inl_inr_self, hb.inl_inr_of_ne, modelForm]
  refine ⟨c.equivFun.symm, ?_⟩
  intro a d
  change form (c.equivFun.symm a) (c.equivFun.symm d) = modelForm a d
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hpair]
  simp [Fin.sum_univ_succ, modelForm]
  ring

/-- Ordered representatives of the fifteen lines in binary symplectic four-space. -/
private def modelPair : Fin 15 → (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) :=
  ![⟨![0, 0, 0, 1], ![0, 1, 0, 0]⟩,
    ⟨![0, 0, 0, 1], ![1, 0, 0, 0]⟩,
    ⟨![0, 0, 0, 1], ![1, 1, 0, 0]⟩,
    ⟨![0, 0, 1, 0], ![0, 1, 0, 0]⟩,
    ⟨![0, 0, 1, 0], ![1, 0, 0, 0]⟩,
    ⟨![0, 0, 1, 0], ![1, 1, 0, 0]⟩,
    ⟨![0, 0, 1, 1], ![0, 1, 0, 0]⟩,
    ⟨![0, 0, 1, 1], ![1, 0, 0, 0]⟩,
    ⟨![0, 0, 1, 1], ![1, 1, 0, 0]⟩,
    ⟨![0, 1, 0, 1], ![1, 0, 1, 0]⟩,
    ⟨![0, 1, 0, 1], ![1, 0, 1, 1]⟩,
    ⟨![0, 1, 1, 0], ![1, 0, 0, 1]⟩,
    ⟨![0, 1, 1, 0], ![1, 0, 1, 1]⟩,
    ⟨![0, 1, 1, 1], ![1, 0, 0, 1]⟩,
    ⟨![0, 1, 1, 1], ![1, 0, 1, 0]⟩]

private def modelSet (k : Fin 15) : Finset (Fin 4 → ZMod 2) :=
  {(modelPair k).1, (modelPair k).2, (modelPair k).1 + (modelPair k).2}

private theorem model_pair_facts : ∀ k : Fin 15,
    (modelPair k).1 ≠ 0 ∧ (modelPair k).2 ≠ 0 ∧
      (modelPair k).1 ≠ (modelPair k).2 ∧
        modelForm (modelPair k).1 (modelPair k).2 = 0 := by
  decide

private theorem model_set_facts : ∀ k : Fin 15,
    (modelSet k).card = 3 ∧ (∀ a ∈ modelSet k, a ≠ 0) ∧
      ∀ a ∈ modelSet k, ∀ b ∈ modelSet k, a ≠ b →
        a + b ∈ modelSet k ∧ modelForm a b = 0 := by
  intro k
  refine ⟨?_, ?_, ?_⟩
  · fin_cases k <;> decide
  · simp only [modelSet, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    fin_cases k <;> decide
  · intro a ha b hb hab
    simp only [modelSet, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals revert hab; fin_cases k <;> decide

private theorem model_set_injective : Function.Injective modelSet := by
  decide

private theorem model_cover : ∀ a b : Fin 4 → ZMod 2,
    a ≠ 0 → b ≠ 0 → a ≠ b → modelForm a b = 0 →
      ∃ k : Fin 15, modelSet k = {a, b, a + b} := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduction covers the 256 assignments of four single-qubit binary labels.
private theorem local_total_exponent : ∀ w : Fin 4 → ZMod 2 × ZMod 2,
    (∑ k : Fin 15, localExponent (Fintype.linearCombination (ZMod 2) w (modelPair k).1)
      (Fintype.linearCombination (ZMod 2) w (modelPair k).2)) =
        2 * ((w 0).1 * (w 1).2 + (w 0).2 * (w 1).1).val := by
  decide

private theorem fourthRoot_two (b : ZMod 2) :
    AddChar.zmodChar 4 Complex.I_pow_four (2 * b.val) = complexSign b := by
  rw [show (2 : ZMod 4) * b.val = ((2 * b.val : ℕ) : ZMod 4) by push_cast; rfl,
    AddChar.zmodChar_apply', pow_mul, Complex.I_sq]
  exact (D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.complex_sign_val b).symm

private theorem local_phase_product (w : Fin 4 → ZMod 2 × ZMod 2) :
    (∏ k : Fin 15, AddChar.zmodChar 4 Complex.I_pow_four
      (localExponent (Fintype.linearCombination (ZMod 2) w (modelPair k).1)
        (Fintype.linearCombination (ZMod 2) w (modelPair k).2))) =
        complexSign ((w 0).1 * (w 1).2 + (w 0).2 * (w 1).1) := by
  have hprod := (map_prod (AddChar.zmodChar 4 Complex.I_pow_four).toMonoidHom
    (fun k : Fin 15 => Multiplicative.ofAdd
      (localExponent (Fintype.linearCombination (ZMod 2) w (modelPair k).1)
        (Fintype.linearCombination (ZMod 2) w (modelPair k).2)))
    Finset.univ).symm
  rw [← ofAdd_sum] at hprod
  simp only [AddChar.toMonoidHom_apply, toAdd_ofAdd] at hprod
  rw [hprod, local_total_exponent, fourthRoot_two]

private theorem coordinates_eval {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) (a : Fin 4 → ZMod 2) (j : Fin N) :
    (e a : Fin N → ZMod 2 × ZMod 2) j =
      Fintype.linearCombination (ZMod 2)
        (fun i => (e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j) a := by
  simpa only [Fintype.linearCombination_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.piRing_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, LinearEquiv.coe_coe] using
    (LinearEquiv.piRing_symm_apply (S := ZMod 2)
      (LinearEquiv.piRing (ZMod 2) (ZMod 2 × ZMod 2) (Fin 4) (ZMod 2)
        ((LinearMap.proj j).comp (U.subtype.comp e.toLinearMap))) a)

private theorem total_phase {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (he : ∀ a b, B (e a : Fin N → ZMod 2 × ZMod 2)
      (e b : Fin N → ZMod 2 × ZMod 2) = modelForm a b) :
    (∏ k : Fin 15, phase (e (modelPair k).1 : Fin N → ZMod 2 × ZMod 2)
      (e (modelPair k).2 : Fin N → ZMod 2 × ZMod 2)) = -1 := by
  unfold phase
  have hloc (k : Fin 15) (j : Fin N) :
      localExponent ((e (modelPair k).1 : Fin N → ZMod 2 × ZMod 2) j)
        ((e (modelPair k).2 : Fin N → ZMod 2 × ZMod 2) j) =
      localExponent
        (Fintype.linearCombination (ZMod 2)
          (fun i => (e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j)
          (modelPair k).1)
        (Fintype.linearCombination (ZMod 2)
          (fun i => (e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j)
          (modelPair k).2) := by
    congr 1
    · exact coordinates_eval e _ j
    · exact coordinates_eval e _ j
  simp_rw [hloc]
  rw [Finset.prod_comm]
  simp_rw [local_phase_product]
  rw [← sign_sum]
  change complexSign (B (e (Pi.single 0 1) : Fin N → ZMod 2 × ZMod 2)
    (e (Pi.single 1 1) : Fin N → ZMod 2 × ZMod 2)) = -1
  rw [he]
  norm_num [modelForm, complexSign]

private theorem commute_of_B_zero {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2)
    (h : B u v = 0) : Commute (observable u) (observable v) := by
  change observable u * observable v = observable v * observable u
  rw [observable_comm, h]
  simp [complexSign]

theorem lineProduct_triple {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hB : B u v = 0) :
    lineProduct {u, v, u + v} = phase u v • 1 := by
  classical
  have hsu : u + v ≠ u := fun h => hv (add_left_cancel (h.trans (add_zero u).symm))
  have hsv : u + v ≠ v := fun h => hu (add_right_cancel (h.trans (zero_add v).symm))
  have hp : ({u, v, u + v} : Finset _).toList.Perm [u, v, u + v] := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      (by simp [huv, Ne.symm hsu, Ne.symm hsv])).2
    intro x
    simp
  have hBu : B u (u + v) = 0 := by rw [B_add_right, B_self, hB, zero_add]
  have hBv : B v (u + v) = 0 := by rw [B_add_right, B_comm v u, hB, B_self, add_zero]
  have hc : [observable u, observable v, observable (u + v)].Pairwise Commute := by
    simp [commute_of_B_zero u v hB, commute_of_B_zero u (u + v) hBu,
      commute_of_B_zero v (u + v) hBv]
  have hprod := (hp.symm.map observable).prod_eq' hc
  change (({u, v, u + v} : Finset _).toList.map observable).prod = _
  rw [← hprod]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ← mul_assoc]
  rw [observable_mul, smul_mul_assoc, observable_sq]

private def embeddedLine {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) (k : Fin 15) :
    Finset (Fin N → ZMod 2 × ZMod 2) :=
  (modelSet k).image fun a => (e a : Fin N → ZMod 2 × ZMod 2)

private theorem embedded_lines {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2))
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (he : ∀ a b, B (e a : Fin N → ZMod 2 × ZMod 2)
      (e b : Fin N → ZMod 2 × ZMod 2) = modelForm a b) :
    lines U = Finset.univ.image (embeddedLine e) ∧ Function.Injective (embeddedLine e) := by
  classical
  have ei : Function.Injective (fun a => (e a : Fin N → ZMod 2 × ZMod 2)) :=
    Subtype.val_injective.comp e.injective
  have enz (a : Fin 4 → ZMod 2) (ha : a ≠ 0) :
      (e a : Fin N → ZMod 2 × ZMod 2) ≠ 0 := by
    intro h
    apply ha
    apply ei
    simpa using h
  constructor
  · apply Finset.ext
    intro l
    constructor
    · intro hl
      have hl' : l ⊆ points U ∧ l.card = 3 ∧
          ∀ u ∈ l, ∀ v ∈ l, u ≠ v → u + v ∈ l ∧ B u v = 0 := by
        simpa only [lines, Finset.mem_filter, Finset.mem_powerset] using hl
      obtain ⟨u, v, w, huv, huw, hvw, hset⟩ := Finset.card_eq_three.mp hl'.2.1
      have hu : u ∈ l := by simp [hset]
      have hv : v ∈ l := by simp [hset]
      obtain ⟨huU, hu0⟩ := (Finset.mem_filter.mp (hl'.1 hu)).2
      obtain ⟨hvU, hv0⟩ := (Finset.mem_filter.mp (hl'.1 hv)).2
      obtain ⟨hsum, hB⟩ := hl'.2.2 u hu v hv huv
      have hw : u + v = w := by
        have hm : u + v = u ∨ u + v = v ∨ u + v = w := by simpa [hset] using hsum
        rcases hm with h | h | h
        · exact False.elim (hv0 (add_left_cancel (h.trans (add_zero u).symm)))
        · exact False.elim (hu0 (add_right_cancel (h.trans (zero_add v).symm)))
        · exact h
      let a : Fin 4 → ZMod 2 := e.symm ⟨u, huU⟩
      let b : Fin 4 → ZMod 2 := e.symm ⟨v, hvU⟩
      have hea : (e a : Fin N → ZMod 2 × ZMod 2) = u := by simp [a]
      have heb : (e b : Fin N → ZMod 2 × ZMod 2) = v := by simp [b]
      have ha0 : a ≠ 0 := by intro h; apply hu0; simpa [h] using hea.symm
      have hb0 : b ≠ 0 := by intro h; apply hv0; simpa [h] using heb.symm
      have hab : a ≠ b := by intro h; apply huv; rw [← hea, ← heb, h]
      have hform : modelForm a b = 0 := by rw [← he, hea, heb, hB]
      obtain ⟨k, hk⟩ := model_cover a b ha0 hb0 hab hform
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      simp [embeddedLine, hk, hea, heb, hset, ← hw, map_add]
    · intro hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powerset.mpr
        intro u hu
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
        simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(e a).property, enz a ((model_set_facts k).2.1 a ha)⟩
      · constructor
        · rw [embeddedLine, Finset.card_image_of_injective _ ei]
          exact (model_set_facts k).1
        · intro u hu v hv huv
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
          have hab : a ≠ b := fun h => huv (by rw [h])
          have hcond := (model_set_facts k).2.2 a ha b hb hab
          refine ⟨?_, by rw [he]; exact hcond.2⟩
          have hadd : (e (a + b) : Fin N → ZMod 2 × ZMod 2) =
              (e a : Fin N → ZMod 2 × ZMod 2) + (e b : Fin N → ZMod 2 × ZMod 2) := by simp
          rw [← hadd]
          exact Finset.mem_image.mpr ⟨a + b, hcond.1, rfl⟩
  · intro k m h
    apply model_set_injective
    exact Finset.image_injective ei h

private theorem odd_of_sign_product {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, f i = 1 ∨ f i = -1) (hp : (∏ i, f i) = -1) :
    Odd (Finset.univ.filter fun i => f i = -1).card := by
  classical
  apply (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)).mp
  calc
    (-1 : ℂ) ^ (Finset.univ.filter fun i => f i = -1).card =
        ∏ i, if f i = -1 then (-1 : ℂ) else 1 := by simp [Finset.prod_ite]
    _ = ∏ i, f i := by
      apply Finset.prod_congr rfl
      intro i _
      rcases hf i with h | h <;> norm_num [h]
    _ = -1 := hp

private theorem scalar_identity_injective (N : ℕ) :
    Function.Injective (fun c : ℂ => c • (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)) :=
  smul_left_injective ℂ one_ne_zero

private theorem parity_from_coordinates {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2))
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (he : ∀ a b, B (e a : Fin N → ZMod 2 × ZMod 2)
      (e b : Fin N → ZMod 2 × ZMod 2) = modelForm a b) :
    Odd (negativeLines U).card := by
  classical
  have ei : Function.Injective (fun a => (e a : Fin N → ZMod 2 × ZMod 2)) :=
    Subtype.val_injective.comp e.injective
  have enz (a : Fin 4 → ZMod 2) (ha : a ≠ 0) :
      (e a : Fin N → ZMod 2 × ZMod 2) ≠ 0 := by
    intro h
    apply ha
    apply ei
    simpa using h
  obtain ⟨hgeom, hinj⟩ := embedded_lines U e he
  let f : Fin 15 → ℂ := fun k => phase
    (e (modelPair k).1 : Fin N → ZMod 2 × ZMod 2)
    (e (modelPair k).2 : Fin N → ZMod 2 × ZMod 2)
  have hprod (k : Fin 15) : lineProduct (embeddedLine e k) = f k • 1 := by
    have hpair := model_pair_facts k
    have hne : (e (modelPair k).1 : Fin N → ZMod 2 × ZMod 2) ≠
        (e (modelPair k).2 : Fin N → ZMod 2 × ZMod 2) := fun h => hpair.2.2.1 (ei h)
    have hB : B (e (modelPair k).1 : Fin N → ZMod 2 × ZMod 2)
        (e (modelPair k).2 : Fin N → ZMod 2 × ZMod 2) = 0 := by rw [he]; exact hpair.2.2.2
    simpa [embeddedLine, modelSet, map_add, f] using
      lineProduct_triple _ _ (enz _ hpair.1) (enz _ hpair.2.1) hne hB
  have hneg (k : Fin 15) : lineProduct (embeddedLine e k) = -1 ↔ f k = -1 := by
    rw [hprod k]
    constructor
    · intro h
      apply scalar_identity_injective N
      simpa using h
    · intro h
      simp [h]
  have hs (k : Fin 15) : f k = 1 ∨ f k = -1 := by
    have hmem : embeddedLine e k ∈ lines U := by
      rw [hgeom]
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rcases line_sign U _ hmem with h | h
    · left
      apply scalar_identity_injective N
      simpa [hprod k] using h
    · exact Or.inr ((hneg k).mp h)
  have hodd := odd_of_sign_product f hs (total_phase e he)
  unfold negativeLines
  rw [hgeom, Finset.filter_image, Finset.card_image_of_injective _ hinj]
  simpa only [hneg] using hodd

/-- Every linear doily has an odd number of negative lines. -/
theorem result : claim := by
  intro N _ U hU
  obtain ⟨e, he⟩ := symplectic_coordinates U hU
  exact parity_from_coordinates U e he

end

end D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
