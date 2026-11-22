/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRows
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameRows
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Swap-symmetric two-site readout. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameNative

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open PeriodicMPSUniformNativeTransferReadout (mixedTransfer_pow_eq_sum_wordProducts)
open SevenSiteTraceBase (Word)
open SevenSiteCriticalCertificate (observedRow)
open private pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private symmetricIntertwiner intertwiningEquation trace_word_reverse_of_det_ne_zero
  map_intertwiner map_wordProduct ofFn_rev wordProduct from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSExchangeSymmetry

noncomputable section

/-- The checked generic transpose intertwiner proves word reversal over the
universal polynomial ring. Specialization allows arbitrary dual-number cores. -/
private theorem trace_list_reverse {R : Type*} [CommRing R] (A : Core R) (w : List (Fin 2)) :
    (wordProduct A w).trace = (wordProduct A w.reverse).trace := by
  let G : Core (MvPolynomial (Fin 2 × TwoBits) ℤ) :=
    fun i => Matrix.of fun j k => X (i, j, k)
  let ref : Core ℤ := ![!![0, 0; 0, 1], !![0, 1; 1, 0]]
  have hd : (symmetricIntertwiner ref).det = 1 := by
    simp [Matrix.det_fin_two, symmetricIntertwiner, intertwiningEquation, ref]
  have hg : (symmetricIntertwiner G).det ≠ 0 := by
    intro h
    let f := MvPolynomial.eval (fun p : Fin 2 × TwoBits => ref p.1 p.2.1 p.2.2)
    have he := congrArg f h
    rw [RingHom.map_det, map_intertwiner, map_zero] at he
    have hG (i : Fin 2) : f.mapMatrix (G i) = ref i := by
      apply Matrix.ext
      intro j k
      exact MvPolynomial.eval_X _
    simp only [hG, hd, one_ne_zero] at he
  let f := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun p : Fin 2 × TwoBits => A p.1 p.2.1 p.2.2)
  have hG (i : Fin 2) : f.mapMatrix (G i) = A i := by
    apply Matrix.ext
    intro j k
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have he := congrArg f (trace_word_reverse_of_det_ne_zero G hg w)
  rw [AddMonoidHom.map_trace, AddMonoidHom.map_trace] at he
  change (f.mapMatrix (wordProduct G w)).trace = (f.mapMatrix (wordProduct G w.reverse)).trace at he
  rw [map_wordProduct, map_wordProduct] at he
  simpa only [hG] using he

def SwapSymmetric {R : Type*} (W : TransferMatrix R) : Prop :=
  ∀ p q, W p.swap q.swap = W p q

private theorem mixedRaw_word_sum {R : Type*} [CommRing R] (A B : Core R) (m : ℕ)
    (p q : TwoBits) :
    mixedRaw A B m p q = ∑ w : Word m, (A p.1 * A p.2 * SevenSiteTraceBase.wordProduct A w).trace *
      (B q.1 * B q.2 * SevenSiteTraceBase.wordProduct B w).trace := by
  simp only [mixedRaw, mixedTransfer_pow_eq_sum_wordProducts, Matrix.mul_sum, Matrix.trace_sum,
    PeriodicMPSUniformHardCoreTransferRecurrence.binaryInsertion, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_comm _ _

theorem mixedRaw_swapSymmetric {R : Type*} [CommRing R] (A B : Core R) (m : ℕ) :
    SwapSymmetric (mixedRaw A B m) := by
  intro p q
  rw [mixedRaw_word_sum, mixedRaw_word_sum]
  let e : Word m ≃ Word m := (Fin.revPerm (n := m)).arrowCongr (Equiv.refl (Fin 2))
  have h (C : Core R) (p : TwoBits) (w : Word m) :
      (C p.2 * C p.1 * SevenSiteTraceBase.wordProduct C (w ∘ Fin.rev)).trace =
        (C p.1 * C p.2 * SevenSiteTraceBase.wordProduct C w).trace := by
    have he := trace_list_reverse C (p.1 :: p.2 :: List.ofFn w)
    simp only [wordProduct, List.reverse_cons, List.map_cons, List.prod_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, Matrix.mul_one] at he
    change (C p.1 * (C p.2 * ((List.ofFn w).map C).prod)).trace =
      ((((List.ofFn w).reverse.map C).prod * C p.2) * C p.1).trace at he
    have hw (v : Word m) :
        SevenSiteTraceBase.wordProduct C v = ((List.ofFn v).map C).prod := by
      unfold SevenSiteTraceBase.wordProduct
      rw [List.map_ofFn]
      rfl
    rw [hw, hw, ofFn_rev, Matrix.mul_assoc (C p.1), he, Matrix.mul_assoc _ (C p.2),
      Matrix.trace_mul_comm (((List.ofFn w).reverse.map C).prod)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← e.sum_comp (fun w => (A p.2 * A p.1 * SevenSiteTraceBase.wordProduct A w).trace *
    (B q.2 * B q.1 * SevenSiteTraceBase.wordProduct B w).trace)]
  apply Finset.sum_congr rfl
  intro w _
  change (A p.2 * A p.1 * SevenSiteTraceBase.wordProduct A (w ∘ Fin.rev)).trace *
    (B q.2 * B q.1 * SevenSiteTraceBase.wordProduct B (w ∘ Fin.rev)).trace = _
  rw [h, h]

variable {E : Type*} [Field E] [Algebra ℂ E]

private theorem pauli_completeness (p q a b : Fin 2) :
    ∑ j : Fin 4, pauli (imaginary E) j p q * pauli (imaginary E) j a b =
      if p = b ∧ q = a then (2 : E) else 0 := by
  have hi : imaginary E * imaginary E = -1 := by
    rw [← pow_two, imaginary, ← map_pow, Complex.I_sq, map_neg, map_one]
  fin_cases p <;> fin_cases q <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_succ, pauli, hi] <;> ring

private theorem pauli_rebuild (W : TransferMatrix E) (p q : TwoBits) :
    (∑ a : Fin 4, ∑ b : Fin 4, pauliRead W (a, b) * pauliPair (a,b) p q) = 4 * W p q := by
  calc
    _ = ∑ u : TwoBits, ∑ v : TwoBits, W v u *
        ((∑ a : Fin 4, pauli (imaginary E) a p.1 q.1 * pauli (imaginary E) a u.1 v.1) *
         (∑ b : Fin 4, pauli (imaginary E) b p.2 q.2 * pauli (imaginary E) b u.2 v.2)) := by
      simp only [pauliRead, pauliPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4)))
        (t := (Finset.univ : Finset TwoBits))]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
      simp_rw [pauli_completeness]
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp <;> ring

private theorem pauliRead_exchange (W : TransferMatrix E) (hW : SwapSymmetric W)
    (a b : Fin 4) : pauliRead W (a, b) = pauliRead W (b, a) := by
  simp only [pauliRead, pauliPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply]
  let e : TwoBits ≃ TwoBits := Equiv.prodComm _ _
  rw [← e.sum_comp (fun u => ∑ v : TwoBits,
    pauli (imaginary E) b u.1 v.1 * pauli (imaginary E) a u.2 v.2 * W v u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← e.sum_comp (fun v =>
    pauli (imaginary E) b (e u).1 v.1 * pauli (imaginary E) a (e u).2 v.2 * W v (e u))]
  refine Finset.sum_congr rfl fun v _ => ?_
  change _ = pauli (imaginary E) b u.2 v.2 * pauli (imaginary E) a u.1 v.1 * W v.swap u.swap
  rw [hW, mul_comm (pauli (imaginary E) b u.2 v.2)]

private theorem observedRow_covers (a b : Fin 4) :
    (∃ j, observedRow j = (a, b)) ∨ (∃ j, observedRow j = (b, a)) := by
  fin_cases a <;> fin_cases b <;> decide

private def rowOf (a b : Fin 4) : Fin 10 :=
  Classical.choose (show ∃ j, observedRow j = (a,b) ∨ observedRow j = (b,a) from by
    rcases observedRow_covers a b with ⟨j, h⟩ | ⟨j, h⟩
    · exact ⟨j, Or.inl h⟩
    · exact ⟨j, Or.inr h⟩)

private theorem rowOf_spec (a b : Fin 4) :
    observedRow (rowOf a b) = (a,b) ∨ observedRow (rowOf a b) = (b,a) :=
  Classical.choose_spec (show ∃ j, observedRow j = (a,b) ∨ observedRow j = (b,a) from by
    rcases observedRow_covers a b with ⟨j, h⟩ | ⟨j, h⟩
    · exact ⟨j, Or.inl h⟩
    · exact ⟨j, Or.inr h⟩)

def unobserve (v : Fin 10 → E) : TransferMatrix E :=
  Matrix.of fun p q => (4 : E)⁻¹ *
    ∑ a : Fin 4, ∑ b : Fin 4, v (rowOf a b) * pauliPair (a,b) p q

/-- The ten native rows reconstruct the entire exchange-symmetric raw
direction. This supplies the row map used in determinant transport. -/
theorem unobserve_pauliRead (W : TransferMatrix E) (hW : SwapSymmetric W) :
    unobserve (fun j => pauliRead W (observedRow j)) = W := by
  have h (a b : Fin 4) :
      pauliRead W (observedRow (rowOf a b)) = pauliRead W (a,b) := by
    rcases rowOf_spec a b with he | he
    · rw [he]
    · rw [he, pauliRead_exchange _ hW b a]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  apply Matrix.ext
  intro p q
  simp only [unobserve, Matrix.of_apply, h, pauli_rebuild, ← mul_assoc]
  rw [inv_mul_cancel₀ (by norm_num : (4 : E) ≠ 0), one_mul]

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
