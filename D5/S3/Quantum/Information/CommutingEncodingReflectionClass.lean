/- GID: D5/S3/Quantum/Information/CommutingEncodingReflectionClass
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncodingReflectionClass
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting product and reflection encodings give the same qubit state class. -/

import D5.S3.Quantum.Information.CommutingEncoding.LocalSiteNormalForm
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction

/-! Commuting qubit product encodings and their local-reflection replacements. -/

open scoped BigOperators
open Matrix
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj tensor_unitary)

open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient

namespace D5.S3.Quantum.Information.CommutingEncodingReflectionClass

/-- A complete orthonormal orbit under pairwise commuting product unitaries. -/
def IsCommutingProductEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) ∧
  (∀ a b, ∑ x, star ((tensorOp (U a) *ᵥ ψ) x) * (tensorOp (U b) *ᵥ ψ) x = if a = b then 1 else 0)

/-- A commuting product encoding whose individual qubit factors are Hermitian involutions. -/
def IsCommutingReflectionEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop := IsCommutingProductEncoding ψ U ∧
  (∀ a j, (U a j).IsHermitian ∧ U a j * U a j = 1)

/-- Arbitrary local unitary factors give the same commuting encoding class as reflections. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → ∀ ψ : (Fin n → Fin 2) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) → ((∃ U, IsCommutingProductEncoding ψ U) ↔
      (∃ U, IsCommutingReflectionEncoding ψ U))

private lemma product_encoding_conjugate {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : IsCommutingProductEncoding ψ U)
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsCommutingProductEncoding (tensorOp V *ᵥ ψ)
      (fun a j => V j * U a j * (V j)ᴴ) := by
  classical
  let T := tensorOp V
  have hT := tensor_unitary V hV
  have hTtT : Tᴴ * T = 1 := hT.1
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⟨T, hT⟩
  have ht (a) : tensorOp (fun j => V j * U a j * (V j)ᴴ) = C (tensorOp (U a)) := by
    change tensorOp (fun j => V j * U a j * (V j)ᴴ) = tensorOp V * tensorOp (U a) * (tensorOp V)ᴴ
    rw [tensor_adj, tensor_mul, tensor_mul]
  have he (a) : tensorOp (fun j => V j * U a j * (V j)ᴴ) *ᵥ (T *ᵥ ψ) =
      T *ᵥ (tensorOp (U a) *ᵥ ψ) := by
    rw [ht]; change (T * tensorOp (U a) * Tᴴ) *ᵥ (T *ᵥ ψ) = _
    simp only [← Matrix.mulVec_mulVec]; rw [Matrix.mulVec_mulVec ψ Tᴴ T, hTtT, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro a j; exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hV j) (hU.1 a j)) (Unitary.star_mem (hV j))
  · intro a b; simp only [ht, ← map_mul, hU.2.1 a b]
  · intro a b; change star (tensorOp (fun j => V j * U a j * (V j)ᴴ) *ᵥ (T *ᵥ ψ)) ⬝ᵥ
      (tensorOp (fun j => V j * U b j * (V j)ᴴ) *ᵥ (T *ᵥ ψ)) = _
    rw [he a, he b,
      D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.unitary_preserves_overlap
        T hTtT]
    exact hU.2.2 a b
private lemma reflection_encoding_conjugate {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : IsCommutingReflectionEncoding ψ U)
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsCommutingReflectionEncoding (tensorOp V *ᵥ ψ)
      (fun a j => V j * U a j * (V j)ᴴ) := by
  refine ⟨product_encoding_conjugate ψ U hU.1 V hV, ?_⟩
  intro a j; refine ⟨Matrix.isHermitian_mul_mul_conjTranspose (V j) (hU.2 a j).1, ?_⟩
  have hv : (V j)ᴴ * V j = 1 := (hV j).1
  calc
    _ = V j * U a j * ((V j)ᴴ * V j) * U a j * (V j)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = V j * (U a j * U a j) * (V j)ᴴ := by
      rw [hv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [(hU.2 a j).2, Matrix.mul_one]; exact (hV j).2
private def pauli_symbol (p : Pauli) : ZMod 2 × ZMod 2 :=
  let b := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.bellInput p
  (b.2, b.1)

private def word_symbol {n : ℕ} (p : Fin n → Pauli) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun j => (pauli_symbol (p j)).1, fun j => (pauli_symbol (p j)).2)

private lemma symbol_bijective : Function.Bijective pauli_symbol := by decide

private lemma word_symbol_bijective (n : ℕ) : Function.Bijective (@word_symbol n) := by
  exact ((Equiv.piCongrRight fun _ : Fin n =>
      Equiv.ofBijective pauli_symbol symbol_bijective).trans
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod 2) (fun _ => ZMod 2))).bijective

private lemma word_symbol_mul {n : ℕ} (p q : Fin n → Pauli) :
    word_symbol (fun j => letterProduct (p j) (q j)) = word_symbol p + word_symbol q := by
  have h (p q : Pauli) : pauli_symbol (letterProduct p q) = pauli_symbol p + pauli_symbol q := by
    cases p <;> cases q <;> decide
  exact Prod.ext (funext fun j => congrArg Prod.fst (h (p j) (q j)))
    (funext fun j => congrArg Prod.snd (h (p j) (q j)))

private lemma word_sign {n : ℕ} (p q : Fin n → Pauli) :
    (∏ j, (sgn (p j) (q j) : ℂ)) = complexSign
      (BinaryLagrangianGraphForm.sp (word_symbol p) (word_symbol q)) := by
  rw [BinaryLagrangianGraphForm.sp, sign_sum]
  apply Finset.prod_congr rfl
  intro j _
  change (sgn (p j) (q j) : ℂ) = complexSign
    ((pauli_symbol (p j)).1 * (pauli_symbol (q j)).2 +
     (pauli_symbol (p j)).2 * (pauli_symbol (q j)).1)
  have table (r t : Pauli) : sgn r t = if
      (pauli_symbol r).1 * (pauli_symbol t).2 +
      (pauli_symbol r).2 * (pauli_symbol t).1 = 0 then 1 else -1 := by decide +revert
  rw [table]
  unfold complexSign
  split_ifs <;> norm_num

private lemma diagonal_trace_support (d : Fin 2 → ℂ) (p : Pauli)
    (h : Matrix.trace (pauliMatrix p * diagonal d) ≠ 0) : p = .I ∨ p = .Z := by
  cases p <;> simp_all [pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private lemma finite_isotropic_extension {n : ℕ}
    (B : LinearMap.BilinForm (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hAlt : B.IsAlt) (hNd : B.Nondegenerate)
    (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hS : ∀ u ∈ S, ∀ v ∈ S, B u v = 0) :
    ∃ L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)),
      S ≤ L ∧ (∀ u ∈ L, ∀ v ∈ L, B u v = 0) ∧ Module.finrank (ZMod 2) L = n := by
  classical
  obtain ⟨L, hSL, hmax⟩ := Finite.exists_le_maximal
    (p := fun L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) =>
      ∀ u ∈ L, ∀ v ∈ L, B u v = 0) hS
  have hL := hmax.1
  have hperp : B.orthogonal L = L := by
    apply le_antisymm
    · intro x hx; have hT : ∀ u ∈ L ⊔ Submodule.span (ZMod 2) {x},
          ∀ v ∈ L ⊔ Submodule.span (ZMod 2) {x}, B u v = 0 := by
        intro u hu v hv; obtain ⟨u, huL, u', hu', rfl⟩ := Submodule.mem_sup.mp hu
        obtain ⟨v, hvL, v', hv', rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu'
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv'
        have hxu : B x v = 0 := (hAlt.eq_iff).mp (hx v hvL)
        simp [map_add, hL u huL v hvL, hx u huL, hxu, hAlt.self_eq_zero]
      apply hmax.2 hT le_sup_left
      exact Submodule.mem_sup.mpr
        ⟨0, L.zero_mem, x, Submodule.mem_span_singleton_self x, zero_add x⟩
    · intro x hx y hy; exact hL y hy x hx
  have hd := B.finrank_orthogonal hNd L
  rw [hperp] at hd
  have hE : Module.finrank (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) = n + n := by
    simp [Module.finrank_prod]
  rw [hE] at hd; exact ⟨L, hSL, hL, by omega⟩

private lemma diagonal_on_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (s : Set (Matrix ι ι ℂ)) (hs : ∀ A ∈ s, (Fᴴ * A * F).IsDiag)
    (A : Matrix ι ι ℂ) (hA : A ∈ Submodule.span ℂ s) : (Fᴴ * A * F).IsDiag := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hs A hA
  | zero => simpa only [Matrix.mul_zero, Matrix.zero_mul] using
      (Matrix.isDiag_zero : (0 : Matrix ι ι ℂ).IsDiag)
  | add A B _ _ hA hB =>
      simpa only [Matrix.mul_add, Matrix.add_mul] using hA.add hB
  | smul c A _ hA =>
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hA.smul c

private lemma local_forms_isotropic_span {n : ℕ}
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a))
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hsites : ∀ j, (∀ a, ∃ d : Fin 2 → ℂ, V j * U a j * (V j)ᴴ = diagonal d) ∨
      (∃ (c : Fin (2 ^ n) → ℂ) (p : Fin (2 ^ n) → Pauli), (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V j * U a j * (V j)ᴴ = c a • pauliMatrix (p a)))) :
    ∃ (B : LinearMap.BilinForm (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
      (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2))),
      B.IsAlt ∧ B.Nondegenerate ∧ (∀ u v, B u v = BinaryLagrangianGraphForm.sp u v) ∧
      (∀ u ∈ S, ∀ v ∈ S, B u v = 0) ∧ (∀ a, tensorOp (fun j => V j * U a j * (V j)ᴴ) ∈
        Submodule.span ℂ (wordOp '' {p | word_symbol p ∈ S})) := by
  classical
  let A a j := V j * U a j * (V j)ᴴ
  let allowed (a : Fin (2 ^ n)) (p : Fin n → Pauli) :=
    ∀ j, Matrix.trace (pauliMatrix (p j) * A a j) ≠ 0
  let T := word_symbol '' {p : Fin n → Pauli | ∃ a, allowed a p}
  let B := BinaryStabilizerGraphNormalForm.spForm n
  let S := Submodule.span (ZMod 2) T
  have hlocal (a b) (p q : Fin n → Pauli) (hp : allowed a p) (hq : allowed b q) (j) :
      A a j * A b j = (sgn (p j) (q j) : ℂ) • (A b j * A a j) := by
    rcases hsites j with hdiag | ⟨c, r, hc, hr⟩
    · obtain ⟨d, hd⟩ := hdiag a
      obtain ⟨e, he⟩ := hdiag b
      have hp' := diagonal_trace_support d (p j) (by simpa only [A, hd] using hp j)
      have hq' := diagonal_trace_support e (q j) (by simpa only [A, he] using hq j)
      change (V j * U a j * (V j)ᴴ) * (V j * U b j * (V j)ᴴ) =
        (sgn (p j) (q j) : ℂ) • ((V j * U b j * (V j)ᴴ) * (V j * U a j * (V j)ᴴ))
      rw [hd, he]
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq' <;>
        rw [hp', hq'] <;> simp [sgn, anticomm, Matrix.diagonal_mul_diagonal, mul_comm]
    · have hp' : p j = r a := by
        have hh := hp j
        change Matrix.trace (pauliMatrix (p j) * (V j * U a j * (V j)ᴴ)) ≠ 0 at hh
        rw [hr, Matrix.mul_smul, Matrix.trace_smul, pauli_trace_pair] at hh
        by_contra h; simp [h] at hh
      have hq' : q j = r b := by
        have hh := hq j
        change Matrix.trace (pauliMatrix (q j) * (V j * U b j * (V j)ᴴ)) ≠ 0 at hh
        rw [hr, Matrix.mul_smul, Matrix.trace_smul, pauli_trace_pair] at hh
        by_contra h; simp [h] at hh
      change (V j * U a j * (V j)ᴴ) * (V j * U b j * (V j)ᴴ) =
        (sgn (p j) (q j) : ℂ) • ((V j * U b j * (V j)ᴴ) * (V j * U a j * (V j)ᴴ))
      rw [hr, hr, hp', hq', smul_mul_smul, smul_mul_smul, letter_comm]
      simp only [smul_smul]; congr 1; ring
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    ⟨tensorOp V, tensor_unitary V hV⟩
  have ht (a) : tensorOp (A a) = C (tensorOp (U a)) := by
    change tensorOp (fun j => V j * U a j * (V j)ᴴ) =
      tensorOp V * tensorOp (U a) * (tensorOp V)ᴴ
    rw [tensor_adj, tensor_mul, tensor_mul]
  have comm (a b) : tensorOp (A a) * tensorOp (A b) = tensorOp (A b) * tensorOp (A a) := by
    simp only [ht, ← map_mul, hc a b]
  have iso (p q : Fin n → Pauli) (a b) (hp : allowed a p) (hq : allowed b q) :
      B (word_symbol p) (word_symbol q) = 0 := by
    have he : tensorOp (A a) * tensorOp (A b) =
        (∏ j, (sgn (p j) (q j) : ℂ)) • (tensorOp (A b) * tensorOp (A a)) := by
      rw [tensor_mul, tensor_mul, ← BinaryStabilizerGraphNormalForm.tensor_smul]
      exact congrArg tensorOp (funext (hlocal a b p q hp hq))
    have hne : tensorOp (A b) * tensorOp (A a) ≠ 0 := by
      have hu a : tensorOp (A a) ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
        apply tensor_unitary
        intro j
        exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
          ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hV j) (hU a j)) (Unitary.star_mem (hV j))
      have hu := (Matrix.unitaryGroup (Fin n → Fin 2) ℂ).mul_mem (hu b) (hu a)
      intro hz; have hh := hu.1; rw [hz, star_zero, zero_mul] at hh; exact zero_ne_one hh
    rw [comm a b] at he
    have hs : (∏ j, (sgn (p j) (q j) : ℂ)) = 1 :=
      (smul_left_injective ℂ hne) (he.symm.trans (one_smul ℂ _).symm)
    rw [word_sign] at hs
    have bits (x : ZMod 2) : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x
    change BinaryLagrangianGraphForm.sp (word_symbol p) (word_symbol q) = 0
    rcases bits (BinaryLagrangianGraphForm.sp (word_symbol p) (word_symbol q)) with h | h
    · exact h
    · rw [h, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_one] at hs; norm_num at hs
  refine ⟨B, S, BinaryStabilizerGraphNormalForm.sp_alt n,
    BinaryStabilizerGraphNormalForm.sp_nondegenerate n, fun _ _ => rfl, ?_, ?_⟩
  · intro u hu v hv
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨p, ⟨a, hp⟩, rfl⟩ := hu
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨q, ⟨b, hq⟩, rfl⟩ := hv; exact iso p q a b hp hq
      | zero => simp
      | add v w _ _ hv hw => simp [map_add, hv, hw]
      | smul c v _ hv => simp [hv]
    | zero => simp
    | add u w _ _ hu hw => simp [map_add, hu, hw]
    | smul c u _ hu => simp [hu]
  · intro a
    rw [word_expansion (tensorOp (A a))]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : Matrix.trace (wordOp p * tensorOp (A a)) = 0
    · simp [hp]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨p, Submodule.subset_span ⟨p, ⟨a, ?_⟩, rfl⟩, rfl⟩
      rw [show wordOp p = tensorOp (fun j => pauliMatrix (p j)) from rfl,
        tensor_mul, tensor_trace] at hp
      exact fun j => Finset.prod_ne_zero_iff.mp hp j (Finset.mem_univ j)

private noncomputable def binary_character {n : ℕ} (x : Fin n → Fin 2) :
    AddChar (Fin n → Fin 2) ℂ :=
  ∑ j, (x j).val • (AddChar.zmodChar 2 (by norm_num : (-1 : ℂ) ^ 2 = 1)).compAddMonoidHom
    (Pi.evalAddMonoidHom (fun _ : Fin n => Fin 2) j)

private lemma binary_character_apply {n : ℕ} (x a : Fin n → Fin 2) :
    binary_character x a = ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val) := by
  rw [binary_character, AddChar.sum_apply]
  change (∏ j, ((-1 : ℂ) ^ (a j).val) ^ (x j).val) = _
  simp only [pow_mul]

private lemma binary_character_frame {n : ℕ}
    (H : (Fin n → Fin 2) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (hH : ∀ a, (H a).IsHermitian)
    (hmul : ∀ a b, H (a + b) = H a * H b)
    (htrace : ∀ a, Matrix.trace (H a) = if a = 0 then (2 ^ n : ℂ) else 0) :
    ∃ F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧ ∀ a, Fᴴ * H a * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) := by
  classical
  let χ (a x : Fin n → Fin 2) : ℂ := binary_character x a
  have hχadd (a b x : Fin n → Fin 2) : χ (a + b) x = χ a x * χ b x :=
    (binary_character x).map_add_eq_mul a b
  have hχstar (a x : Fin n → Fin 2) : star (χ a x) = χ a x := by simp [χ, binary_character_apply]
  have haab (a b : Fin n → Fin 2) : a + (a + b) = b := by
    funext j
    exact CharTwo.add_cancel_left (R := ZMod 2) (a j) (b j)
  let P (x : Fin n → Fin 2) := ∑ a, χ a x • H a
  have hPeig (a x : Fin n → Fin 2) : H a * P x = χ a x • P x := by
    let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) := ⟨fun b => a + b, fun b => a + b, haab a, haab a⟩
    calc
      _ = ∑ b, χ b x • H (a + b) := by
        simp only [P, Matrix.mul_sum, Matrix.mul_smul, ← hmul]
      _ = ∑ b, χ (a + b) x • H b := by
        apply Fintype.sum_equiv e
        intro b; change χ b x • H (a + b) = χ (a + (a + b)) x • H (a + b); rw [haab]
      _ = _ := by simp only [hχadd, mul_smul, P, Finset.smul_sum]
  have hPne (x : Fin n → Fin 2) : P x ≠ 0 := by
    have ht : Matrix.trace (P x) = (2 ^ n : ℂ) := by
      simp [P, Matrix.trace_sum, Matrix.trace_smul, htrace, χ, binary_character_apply]
    intro hz; rw [hz, Matrix.trace_zero] at ht
    exact (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)) ht.symm
  have hentry (x : Fin n → Fin 2) : ∃ r k, P x r k ≠ 0 := by
    by_contra! hz
    apply hPne x
    ext r k; exact hz r k
  choose r k hentry using hentry
  let v (x : Fin n → Fin 2) : EuclideanSpace ℂ (Fin n → Fin 2) :=
    WithLp.toLp 2 (fun t => P x t (k x))
  have hv (x) : v x ≠ 0 := by
    intro hz; apply hentry x
    have hh := congrArg (fun w : EuclideanSpace ℂ (Fin n → Fin 2) => w (r x)) hz
    exact hh
  let f (x : Fin n → Fin 2) : EuclideanSpace ℂ (Fin n → Fin 2) := (‖v x‖ : ℂ)⁻¹ • v x
  have hnorm (x) : ‖f x‖ = 1 := norm_smul_inv_norm (hv x)
  have hraw (a x : Fin n → Fin 2) :
      H a *ᵥ (fun t => P x t (k x)) = χ a x • (fun t => P x t (k x)) := by
    funext t; exact congrArg (fun M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ => M t (k x))
      (hPeig a x)
  have heig (a x : Fin n → Fin 2) : H a *ᵥ (f x) = χ a x • (f x : (Fin n → Fin 2) → ℂ) := by
    change H a *ᵥ ((‖v x‖ : ℂ)⁻¹ • (fun t => P x t (k x))) =
      χ a x • ((‖v x‖ : ℂ)⁻¹ • (fun t => P x t (k x)))
    rw [Matrix.mulVec_smul, hraw, smul_smul, smul_smul, mul_comm]
  have hsingle (x : Fin n → Fin 2) (j : Fin n) : χ (Pi.single j 1) x = (-1 : ℂ) ^ (x j).val := by
    change binary_character x (Pi.single j 1) = _
    rw [binary_character_apply]
    rw [Finset.prod_eq_single j]
    · simp [Pi.single_apply]
    · intro i _ hij; simp [Pi.single_apply, hij, Ne.symm hij]
    · simp
  have horth (x y : Fin n → Fin 2) (hxy : x ≠ y) : (∑ t, star (f x t) * f y t) = 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    let a : Fin n → Fin 2 := Pi.single j 1
    have hne : χ a y ≠ χ a x := by
      rw [hsingle, hsingle]; generalize hx : x j = r at *; generalize hy : y j = t at *
      fin_cases r <;> fin_cases t <;> norm_num at *
    have hh : star (f x : (Fin n → Fin 2) → ℂ) ⬝ᵥ (H a *ᵥ f y) = star (H a *ᵥ f x) ⬝ᵥ (f y) := by
      rw [Matrix.star_mulVec, (hH a).eq, Matrix.dotProduct_mulVec]
    rw [heig, heig, star_smul, smul_dotProduct, dotProduct_smul, hχstar] at hh
    have hz : (χ a y - χ a x) * (∑ t, star (f x t) * f y t) = 0 := by
      change (χ a y - χ a x) * (star (f x : (Fin n → Fin 2) → ℂ) ⬝ᵥ f y) = 0; linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  have hself (x : Fin n → Fin 2) : (∑ t, star (f x t) * f x t) = 1 := by
    have hh : inner ℂ (f x) (f x) = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hnorm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      mul_comm] using hh
  let F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun t x => f x t
  have hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext x y; change (∑ t, star (f x t) * f y t) = if x = y then 1 else 0; by_cases hxy : x = y
    · subst y
      simpa using hself x
    · simpa [hxy] using horth x y hxy
  refine ⟨F, hF, ?_⟩
  intro a
  have hHF : H a * F = F * diagonal (χ a) := by
    ext t x; rw [Matrix.mul_diagonal]; change (H a *ᵥ (f x)) t = f x t * χ a x
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (heig a x) t
  calc
    _ = Fᴴ * (H a * F) := Matrix.mul_assoc _ _ _
    _ = Fᴴ * (F * diagonal (χ a)) := by rw [hHF]
    _ = (Fᴴ * F) * diagonal (χ a) := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by
      rw [show Fᴴ * F = 1 from hF.1, Matrix.one_mul]
      simp only [χ, binary_character_apply]

private lemma hermitian_phased_pauli_reflections {n : ℕ} (hn : 1 ≤ n)
    (c : ℂ) (p : Fin n → Pauli) (hc : star c * c = 1) (hh : (c • wordOp p).IsHermitian) :
    ∃ R : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ j, (R j).IsHermitian ∧ R j * R j = 1) ∧ tensorOp R = c • wordOp p := by
  classical
  let j₀ : Fin n := ⟨0, by omega⟩
  have hw : (wordOp p)ᴴ = wordOp p :=
    D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_hermitian p
  have hwne : wordOp p ≠ 0 := Units.ne_zero
      (D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.wordUnit p)
  have hcs : star c = c := by
    apply smul_left_injective ℂ hwne
    simpa only [Matrix.conjTranspose_smul, hw] using hh.eq
  have hsign : c = 1 ∨ c = -1 := by
    apply sq_eq_one_iff.mp
    simpa only [hcs, pow_two] using hc
  have hpauli (q : Pauli) : (pauliMatrix q).IsHermitian ∧ pauliMatrix q * pauliMatrix q = 1 := by
    refine ⟨D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian q,
      ?_⟩
    exact D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.pauli_square q
  refine ⟨fun j => (if j = j₀ then c else 1) • pauliMatrix (p j), ?_, ?_⟩
  · intro j; dsimp only
    have hs : (if j = j₀ then c else 1) = 1 ∨ (if j = j₀ then c else 1) = -1 := by
      split_ifs <;> simp_all
    rcases hs with hs | hs
    · rw [hs, one_smul]; exact hpauli (p j)
    · rw [hs, neg_one_smul]
      exact ⟨(hpauli (p j)).1.neg, by simpa only [neg_mul_neg] using (hpauli (p j)).2⟩
  · rw [D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_smul]
    have hp : (∏ j : Fin n, if j = j₀ then c else 1) = c := by simp
    rw [hp]; rfl

set_option backward.isDefEq.respectTransparency false in
private lemma lagrangian_phased_representation {n : ℕ}
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) :
    ∃ (H : (Fin n → Fin 2) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (c : (Fin n → Fin 2) → ℂ) (p : (Fin n → Fin 2) → Fin n → Pauli), (∀ a, star (c a) * c a = 1) ∧
      (∀ a, H a = c a • wordOp (p a)) ∧ (∀ a, (H a).IsHermitian) ∧ (∀ a b, H (a + b) = H a * H b) ∧
      (∀ a, Matrix.trace (H a) = if a = 0 then (2 ^ n : ℂ) else 0) ∧
      (∀ p, word_symbol p ∈ L → wordOp p ∈ Submodule.span ℂ (Set.range H)) := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 2) L hdim
  let e := b.equivFun.symm
  let P (j : Fin n) := (Equiv.ofBijective word_symbol (word_symbol_bijective n)).symm
    (b j : (Fin n → ZMod 2) × (Fin n → ZMod 2))
  have hP j : word_symbol (P j) = (b j : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
    (Equiv.ofBijective word_symbol (word_symbol_bijective n)).apply_symm_apply _
  have square (p : Fin n → Pauli) : wordOp p * wordOp p = 1 := (wordUnit p).val_inv
  have commuteP (i j) : Commute (wordOp (P i)) (wordOp (P j)) := by
    change wordOp (P i) * wordOp (P j) = _
    rw [word_comm_sign, word_sign, hP, hP,
      hL _ (b i).property _ (b j).property, sign_zero, one_smul]
  let φ (j : Fin n) : Multiplicative (Fin 2) →* Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := {
    toFun := fun a => if a.toAdd = 0 then 1 else wordOp (P j)
    map_one' := by simp
    map_mul' := by
      intro a c
      change (if a.toAdd + c.toAdd = 0 then 1 else wordOp (P j)) = _
      generalize a.toAdd = x
      generalize c.toAdd = y
      fin_cases x <;> fin_cases y <;> simp [square]
  }
  have commφ : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j _ x y
    dsimp only [φ, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> first | exact Commute.one_left _ | exact Commute.one_right _ | exact commuteP i j
  let Φ := MonoidHom.noncommPiCoprod φ commφ
  let H (a : Fin n → Fin 2) := Φ (fun j => Multiplicative.ofAdd (a j))
  have hmul (a c : Fin n → Fin 2) : H (a + c) = H a * H c :=
    Φ.map_mul (fun j => Multiplicative.ofAdd (a j)) (fun j => Multiplicative.ofAdd (c j))
  have hzero : H 0 = 1 := Φ.map_one
  have gen (j : Fin n) (a : Fin 2) : ∃ p : Fin n → Pauli,
      φ j (Multiplicative.ofAdd a) = wordOp p ∧
      word_symbol p = (id (α := ZMod 2) a) • (b j : (Fin n → ZMod 2) × (Fin n → ZMod 2)) := by
    fin_cases a
    · refine ⟨fun _ => .I, ?_, ?_⟩
      · simp [φ, word_one]
      · change word_symbol (fun _ : Fin n => Pauli.I) = (0 : ZMod 2) • _
        rw [zero_smul]; rfl
    · refine ⟨P j, by simp [φ], ?_⟩
      change word_symbol (P j) = (1 : ZMod 2) • _
      rw [one_smul]; exact hP j
  have phase (p q : Fin n → Pauli) :
      star (∏ j, letterPhase (p j) (q j)) * (∏ j, letterPhase (p j) (q j)) = 1 := by
    rw [star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    cases p j <;> cases q j <;> simp [letterPhase]
  have lift (a : Fin n → Fin 2) (s : Finset (Fin n)) : ∃ c : ℂ, ∃ p : Fin n → Pauli,
      star c * c = 1 ∧
      s.noncommProd (fun j => φ j (Multiplicative.ofAdd (a j)))
        (fun i _ j _ hij => commφ hij _ _) = c • wordOp p ∧
      word_symbol p = ∑ j ∈ s, (id (α := ZMod 2) (a j)) •
        (b j : (Fin n → ZMod 2) × (Fin n → ZMod 2)) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨1, fun _ => .I, by simp,
        by simp only [Finset.noncommProd_empty, one_smul, word_one],
        by simp only [Finset.sum_empty]; rfl⟩
    | @insert j s hj ih =>
      obtain ⟨c, p, hc, he, hs⟩ := ih
      obtain ⟨q, hq, hqs⟩ := gen j (a j)
      refine ⟨c * (∏ k, letterPhase (q k) (p k)), fun k => letterProduct (q k) (p k), ?_, ?_, ?_⟩
      · calc
          _ = (star c * c) * (star (∏ k, letterPhase (q k) (p k)) *
              (∏ k, letterPhase (q k) (p k))) := by rw [star_mul]; ring
          _ = 1 := by rw [hc, phase]; ring
      · rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, he, hq,
          Matrix.mul_smul, word_mul, smul_smul]
      · rw [word_symbol_mul, hqs, hs, Finset.sum_insert hj]
  have hlift (a : Fin n → Fin 2) : ∃ c : ℂ, ∃ p : Fin n → Pauli,
      star c * c = 1 ∧ H a = c • wordOp p ∧
      word_symbol p = (e a : (Fin n → ZMod 2) × (Fin n → ZMod 2)) := by
    obtain ⟨c, p, hc, he, hs⟩ := lift a Finset.univ
    refine ⟨c, p, hc, he, hs.trans ?_⟩
    change _ = ((b.equivFun.symm a : L) : (Fin n → ZMod 2) × (Fin n → ZMod 2))
    rw [b.equivFun_symm_apply]
    simp
  choose c p hc he hs using hlift
  refine ⟨H, c, p, hc, he, ?_, hmul, ?_, ?_⟩
  · intro a
    have hu : (H a)ᴴ * H a = 1 := by
      rw [he, Matrix.conjTranspose_smul, word_hermitian, smul_mul_smul, hc, one_smul, square]
    have haa : a + a = 0 := funext fun j => CharTwo.add_self_eq_zero (R := ZMod 2) (a j)
    have hsq : H a * H a = 1 := by rw [← hmul, haa, hzero]
    change (H a)ᴴ = H a
    calc
      _ = (H a)ᴴ * (H a * H a) := by rw [hsq, Matrix.mul_one]
      _ = H a := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro a
    by_cases ha : a = 0
    · subst a; rw [hzero]; simp
    · have hp : p a ≠ fun _ => .I := by
        intro hp
        have hz : e a = 0 := by
          apply Subtype.val_injective
          rw [← hs, hp]
          rfl
        exact ha (e.injective (hz.trans e.map_zero.symm))
      have ht := word_trace_pair (p a) (fun _ => .I)
      rw [word_one, Matrix.mul_one, ite_eq_right hp] at ht
      rw [he, Matrix.trace_smul, ht, smul_zero, ite_eq_right ha]
  · intro q hq
    let a : Fin n → Fin 2 := b.equivFun ⟨word_symbol q, hq⟩
    have hpa : p a = q := by
      apply (word_symbol_bijective n).1
      rw [hs]
      exact congrArg Subtype.val (b.equivFun.symm_apply_apply ⟨word_symbol q, hq⟩)
    have hne : c a ≠ 0 := by intro h; simpa [h] using hc a
    have hm := (Submodule.span ℂ (Set.range H)).smul_mem (c a)⁻¹
      (Submodule.subset_span (Set.mem_range_self a))
    simpa only [he, hpa, smul_smul, inv_mul_cancel₀ hne, one_smul] using hm

private lemma lagrangian_reflection_representation {n : ℕ} (hn : 1 ≤ n)
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) :
    ∃ R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a b, tensorOp (R (a + b)) = tensorOp (R a) * tensorOp (R b)) ∧
      (∀ a, Matrix.trace (tensorOp (R a)) = if a = 0 then (2 ^ n : ℂ) else 0) ∧
      (∀ p, word_symbol p ∈ L →
        wordOp p ∈ Submodule.span ℂ (Set.range (fun a => tensorOp (R a)))) := by
  classical
  obtain ⟨H, c, p, hc, he, hH, hmul, htrace, hspan⟩ := lagrangian_phased_representation L hL hdim
  have hex (a : Fin n → Fin 2) : ∃ R : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ j, (R j).IsHermitian ∧ R j * R j = 1) ∧ tensorOp R = H a := by
    rw [he a]
    exact hermitian_phased_pauli_reflections hn (c a) (p a) (hc a) (by rw [← he a]; exact hH a)
  choose R hR hRop using hex
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · intro a b; simpa only [hRop] using hmul a b
  · intro a; simpa only [hRop] using htrace a
  · intro p hp; simpa only [hRop] using hspan p hp

private lemma lagrangian_character_frame {n : ℕ} (hn : 1 ≤ n)
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) : ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧ (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F = diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) ∧
      (∀ p, word_symbol p ∈ L → (Fᴴ * wordOp p * F).IsDiag) := by
  classical
  obtain ⟨R, hR, hmul, htrace, hspan⟩ := lagrangian_reflection_representation hn L hL hdim
  have hH (a) : (tensorOp (R a)).IsHermitian := by
    change (tensorOp (R a))ᴴ = tensorOp (R a); rw [tensor_adj]; congr 1; funext j
    exact (hR a j).1.eq
  obtain ⟨F, hF, he⟩ := binary_character_frame (fun a => tensorOp (R a)) hH hmul htrace
  refine ⟨F, R, hF, hR, he, ?_⟩
  intro p hp; apply diagonal_on_span F (Set.range (fun a => tensorOp (R a))) ?_ _ (hspan p hp)
  rintro A ⟨a, rfl⟩
  rw [he a]; exact Matrix.isDiag_diagonal _

private lemma stabilizer_frame_of_site_normal_forms {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a))
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hsites : ∀ j, (∀ a, ∃ d : Fin 2 → ℂ, V j * U a j * (V j)ᴴ = diagonal d) ∨
      (∃ (c : Fin (2 ^ n) → ℂ) (p : Fin (2 ^ n) → Pauli), (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V j * U a j * (V j)ᴴ = c a • pauliMatrix (p a)))) :
    ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧ (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧ (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  classical
  obtain ⟨B, S, hAlt, hNd, hB, hS, hspan⟩ := local_forms_isotropic_span U hU hc V hV hsites
  obtain ⟨L, hSL, hL, hdim⟩ := finite_isotropic_extension B hAlt hNd S hS
  have hsp : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0 := by
    intro u hu v hv; rw [← hB]; exact hL u hu v hv
  obtain ⟨F, R, hF, hR, hRd, hdiag⟩ := lagrangian_character_frame hn L hsp hdim
  have hd (a) : (Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F).IsDiag := by
    refine diagonal_on_span F (wordOp '' {p : Fin n → Pauli | word_symbol p ∈ L})
      ?_ _ ?_
    · rintro A ⟨p, hp, rfl⟩
      exact hdiag p hp
    · have hincl : wordOp '' {p : Fin n → Pauli | word_symbol p ∈ S} ⊆
          wordOp '' {p : Fin n → Pauli | word_symbol p ∈ L} := Set.image_mono (fun p hp => hSL hp)
      exact Submodule.span_mono hincl (hspan a)
  let eig (a : Fin (2 ^ n)) := Matrix.diag (Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F)
  have he (a) : Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F =
      diagonal (eig a) := (hd a).diagonal_diag.symm
  refine ⟨F, eig, R, hF, ?_, he, hR, hRd⟩
  intro a x; have hu : tensorOp (fun j => V j * U a j * (V j)ᴴ) ∈
      Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    apply tensor_unitary
    intro j; exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hV j) (hU a j)) (Unitary.star_mem (hV j))
  have hdu : diagonal (eig a) ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    rw [← he a]; exact (Matrix.unitaryGroup (Fin n → Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n → Fin 2) ℂ).mul_mem (Unitary.star_mem hF) hu) hF
  exact congrFun (Matrix.diagonal_mem_unitary.mp hdu).1 x

private lemma spectral_frame_of_local_signs {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a))
    (hs : ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j)) : ∃ (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧ (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  classical
  have hsite (j : Fin n) := local_site_normal_form (fun a => U a j)
    (fun a => hU a j) (fun a b => hs a b j)
  choose V hV hv using hsite
  obtain ⟨F, eig, R, hF, heig, hd, hR, hRd⟩ :=
    stabilizer_frame_of_site_normal_forms hn U hU hc V hV hv
  exact ⟨V, F, eig, R, hV, hF, heig, hd, hR, hRd⟩

private lemma uniform_weights {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (eig : ι → ι → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (ho : ∀ a b, ∑ x, star (c x * eig a x) * (c x * eig b x) = if a = b then 1 else 0) :
    ∀ x, (Fintype.card ι : ℂ) * (star (c x) * c x) = 1 := by
  classical
  let M : Matrix ι ι ℂ := fun x a => c x * eig a x
  have hcol : Mᴴ * M = 1 := by
    ext a b; exact ho a b
  have hrow : M * Mᴴ = 1 := mul_eq_one_comm.mp hcol
  intro x; have hx := congrFun (congrFun hrow x) x
  rw [Matrix.one_apply_eq] at hx; change (∑ a, (c x * eig a x) * star (c x * eig a x)) = 1 at hx
  have he (a : ι) : (c x * eig a x) * star (c x * eig a x) = star (c x) * c x := by
    rw [star_mul]; calc
      _ = (star (c x) * c x) * (star (eig a x) * eig a x) := by ring
      _ = _ := by rw [heig a x, mul_one]
  simpa only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hx

private lemma flat_of_diagonal_encoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : IsCommutingProductEncoding ψ U)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ) (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (hd : ∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) :
    ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1 := by
  classical
  let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])
  let c := Fᴴ *ᵥ ψ
  have hFF : F * Fᴴ = 1 := hF.2
  have he (a : Fin (2 ^ n)) : Fᴴ *ᵥ (tensorOp (U a) *ᵥ ψ) = fun x => c x * eig a x := by
    calc
      _ = (Fᴴ * tensorOp (U a) * F) *ᵥ c := by
        dsimp only [c]; simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]; ext x; simp [Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    exact D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.unitary_preserves_overlap
      Fᴴ (by simpa only [Matrix.conjTranspose_conjTranspose] using hFF) v w
  have hw := uniform_weights c (fun a => eig (e a)) (fun a x => heig (e a) x) (by
    intro a b; calc
      _ = ∑ x, star ((Fᴴ *ᵥ (tensorOp (U (e a)) *ᵥ ψ)) x) *
          (Fᴴ *ᵥ (tensorOp (U (e b)) *ᵥ ψ)) x := by rw [he, he]
      _ = if e a = e b then 1 else 0 := (hp _ _).trans (hU.2.2 (e a) (e b))
      _ = _ := by simp only [e.injective.eq_iff])
  simpa [c, Fintype.card_fun] using hw

private lemma character_orthogonality {n : ℕ} (a b : Fin n → Fin 2) : (∑ x : Fin n → Fin 2,
      (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) * (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val))) =
      if a = b then (2 ^ n : ℂ) else 0 := by
  classical
  let ψ : AddChar (Fin n → Fin 2) ℂ := binary_character a + binary_character b
  have hsingle (v : Fin n → Fin 2) (j : Fin n) :
      binary_character v (Pi.single j 1) = (-1 : ℂ) ^ (v j).val := by
    rw [binary_character_apply]
    rw [Finset.prod_eq_single j]
    · simp [Pi.single_apply]
    · intro i _ hij; simp [Pi.single_apply, hij, Ne.symm hij]
    · simp
  have hzero : ψ = 0 ↔ a = b := by
    constructor
    · intro h; funext j
      have hj := congrArg (fun e : AddChar (Fin n → Fin 2) ℂ => e (Pi.single j 1)) h
      change binary_character a (Pi.single j 1) * binary_character b (Pi.single j 1) = 1 at hj
      rw [hsingle, hsingle] at hj; generalize ha : a j = r at *; generalize hb : b j = t at *
      fin_cases r <;> fin_cases t <;> norm_num at *
    · rintro rfl
      ext x; change binary_character a x * binary_character a x = 1
      simp only [binary_character_apply]
      rw [← Finset.prod_mul_distrib]; apply Finset.prod_eq_one; intro j _; generalize x j = r
      generalize a j = t
      fin_cases r <;> fin_cases t <;> norm_num
  have hs := AddChar.sum_eq_ite ψ
  have hfun (x : Fin n → Fin 2) : ψ x = (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) *
        (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val)) := by
    change binary_character a x * binary_character b x = _
    simp only [binary_character_apply, Nat.mul_comm]
  simpa only [hfun, hzero, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using hs

private lemma reflection_encoding_of_flat_frame {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hR : ∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) (hd : ∀ a, Fᴴ * tensorOp (R a) * F =
      diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)))
    (hf : ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1) :
    ∃ U, IsCommutingReflectionEncoding ψ U := by
  classical
  let e : Fin (2 ^ n) ≃ (Fin n → Fin 2) :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])).symm
  let c := Fᴴ *ᵥ ψ
  let χ (a x : Fin n → Fin 2) : ℂ := ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)
  have hFF : F * Fᴴ = 1 := hF.2
  have hFtF : Fᴴ * F = 1 := hF.1
  have hN : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hw (x) : star (c x) * c x = 1 / (2 ^ n : ℂ) := by
    apply (eq_div_iff hN).mpr
    simpa [c, mul_comm] using hf x
  have hs (a x) : star (χ a x) = χ a x := by simp [χ]
  have he (a : Fin n → Fin 2) : Fᴴ *ᵥ (tensorOp (R a) *ᵥ ψ) = fun x => c x * χ a x := by
    calc
      _ = (Fᴴ * tensorOp (R a) * F) *ᵥ c := by
        dsimp only [c]; simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]; ext x; simp [Matrix.mulVec, dotProduct, Matrix.diagonal, χ, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    exact D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.unitary_preserves_overlap
      Fᴴ (by simpa only [Matrix.conjTranspose_conjTranspose] using hFF) v w
  have horth (a b : Fin n → Fin 2) :
      (∑ x, star ((tensorOp (R a) *ᵥ ψ) x) * (tensorOp (R b) *ᵥ ψ) x) = if a = b then 1 else 0 := by
    rw [← hp, he, he]; have hm (x) : star (c x * χ a x) * (c x * χ b x) =
        (1 / (2 ^ n : ℂ)) * (χ a x * χ b x) := by
      rw [star_mul, hs]; calc
        _ = (star (c x) * c x) * (χ a x * χ b x) := by ring
        _ = _ := by rw [hw]
    simp_rw [hm]; rw [← Finset.mul_sum]; have hsum : (∑ x : Fin n → Fin 2, χ a x * χ b x) =
        if a = b then (2 ^ n : ℂ) else 0 := character_orthogonality a b
    rw [hsum]; by_cases hab : a = b <;> simp [hab, hN]
  have hi (a : Fin n → Fin 2) : tensorOp (R a) = F * diagonal (χ a) * Fᴴ := by
    have h := congrArg (fun A => F * A * Fᴴ) (hd a)
    have hu (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : F * (Fᴴ * A * F) * Fᴴ = A := by
      calc
        _ = (F * Fᴴ) * A * (F * Fᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFF, Matrix.one_mul, Matrix.mul_one]
    rw [hu] at h; exact h
  have hprod (d g : (Fin n → Fin 2) → ℂ) : (F * diagonal d * Fᴴ) * (F * diagonal g * Fᴴ) =
        F * (diagonal d * diagonal g) * Fᴴ := by
    calc
      _ = F * diagonal d * (Fᴴ * F) * diagonal g * Fᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFtF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨fun a => R (e a), ⟨?_, ?_, ?_⟩, fun a j => hR (e a) j⟩
  · intro a j; apply Matrix.mem_unitaryGroup_iff'.mpr
    change (R (e a) j)ᴴ * R (e a) j = 1; rw [(hR (e a) j).1.eq]; exact (hR (e a) j).2
  · intro a b; rw [hi, hi, hprod, hprod, (Matrix.commute_diagonal (χ (e a)) (χ (e b))).eq]
  · intro a b; simpa only [e.injective.eq_iff] using horth (e a) (e b)

private lemma product_encoding_to_reflections {n : ℕ} (hn : 1 ≤ n) (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : IsCommutingProductEncoding ψ U) :
    ∃ R, IsCommutingReflectionEncoding ψ R := by
  obtain ⟨V, F, eig, R, hV, hF, heig, hd, hR, hRd⟩ := spectral_frame_of_local_signs hn U hU.1 hU.2.1
      (local_commutation_signs U hU.1 hU.2.1)
  have hUV := product_encoding_conjugate ψ U hU V hV
  obtain ⟨S, hS⟩ := reflection_encoding_of_flat_frame (tensorOp V *ᵥ ψ) F hF R hR hRd
    (flat_of_diagonal_encoding (tensorOp V *ᵥ ψ) _ hUV F hF eig heig hd)
  have hback := reflection_encoding_conjugate (tensorOp V *ᵥ ψ) S hS
    (fun j => (V j)ᴴ) (fun j => Unitary.star_mem (hV j))
  have hstate : tensorOp (fun j => (V j)ᴴ) *ᵥ (tensorOp V *ᵥ ψ) = ψ := by
    rw [← tensor_adj, Matrix.mulVec_mulVec]
    rw [show (tensorOp V)ᴴ * tensorOp V = 1 from (tensor_unitary V hV).1]; exact Matrix.one_mulVec ψ
  rw [hstate] at hback; exact ⟨_, hback⟩

/-- Commuting product encodings admit commuting local-reflection replacements. -/
theorem result : claim := by
  intro n hn ψ _hψ; constructor
  · rintro ⟨U, hU⟩
    exact product_encoding_to_reflections hn ψ U hU
  · rintro ⟨U, hU⟩
    exact ⟨U, hU.1⟩

end D5.S3.Quantum.Information.CommutingEncodingReflectionClass
