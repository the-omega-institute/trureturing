/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRows
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRows
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Literal Gram derivatives identify the native slice rows. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralSlice

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Matrix MvPolynomial
open scoped BigOperators Kronecker
open PeriodicMPSCommonSpectralJets (Bits Entry Core literalGram wordReadout suffixProduct)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open UniformMPSExpectedDimensionRefutation (traceWord)

open private joined_trace_swap traceWord_eq_wordProduct wordProduct from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSExchangeSymmetry
open SevenSiteCriticalCertificate (observedRow)

open private pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private pauliFrame frame_completeness from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private certificate_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative

noncomputable section

private theorem nativeFrame_completeness (a b c d : Fin 2) :
    ∑ i : Fin 4, pauli Complex.I i a b * pauli Complex.I i c d =
      if a = d ∧ b = c then (2 : ℂ) else 0 := by
  simp only [certificate_pauli, frame_completeness]

/-- Invert the full Pauli readout on independent complex Gram entries. -/
theorem pauliGram_rebuild (G : Entry → ℂ) (p q : Bits) :
    (∑ i : Fin 4, ∑ j : Fin 4, pauliGram Complex.I G (i, j) *
      (pauli Complex.I i ⊗ₖ pauli Complex.I j) p q) = 4 * G (p, q) := by
  calc
    _ = ∑ a : Bits, ∑ b : Bits, G (b, a) *
        ((∑ i : Fin 4, pauli Complex.I i p.1 q.1 * pauli Complex.I i a.1 b.1) *
         (∑ j : Fin 4, pauli Complex.I j p.2 q.2 * pauli Complex.I j a.2 b.2)) := by
      simp only [pauliGram, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4)))
        (t := (Finset.univ : Finset Bits))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
      simp_rw [nativeFrame_completeness]
      rcases p with ⟨p₁, p₂⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp <;> ring

/-- Simultaneous exchange on the two exposed ket and bra labels. -/
def GramExchangeSymmetric (G : Entry → ℂ) : Prop :=
  ∀ p q, G (p.swap, q.swap) = G (p, q)

theorem pauliGram_exchange {G : Entry → ℂ} (hG : GramExchangeSymmetric G) (i j : Fin 4) :
    pauliGram Complex.I G (i, j) = pauliGram Complex.I G (j, i) := by
  simp only [pauliGram, Matrix.kroneckerMap_apply]
  let e : Bits ≃ Bits := Equiv.prodComm _ _
  rw [← e.sum_comp (fun a => ∑ b : Bits,
    pauli Complex.I j a.1 b.1 * pauli Complex.I i a.2 b.2 * G (b, a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp (fun b =>
    pauli Complex.I j (e a).1 b.1 * pauli Complex.I i (e a).2 b.2 * G (b, e a))]
  refine Finset.sum_congr rfl fun b _ => ?_
  change _ = pauli Complex.I j a.2 b.2 * pauli Complex.I i a.1 b.1 * G (b.swap, a.swap)
  rw [hG, mul_comm (pauli Complex.I j a.2 b.2)]

private theorem observedRow_covers (i j : Fin 4) :
    (∃ a, observedRow a = (i, j)) ∨ (∃ a, observedRow a = (j, i)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- Ten actual Pauli rows retain all exchange-symmetric Gram directions
over the complex field, including the independent-block specialization. -/
theorem observedPauliGram_injective {G H : Entry → ℂ}
    (hG : GramExchangeSymmetric G) (hH : GramExchangeSymmetric H)
    (he : ∀ i, pauliGram Complex.I G (observedRow i) = pauliGram Complex.I H (observedRow i)) :
    G = H := by
  have hp (i j : Fin 4) : pauliGram Complex.I G (i, j) = pauliGram Complex.I H (i, j) := by
    rcases observedRow_covers i j with ⟨a, ha⟩ | ⟨a, ha⟩
    · simpa only [ha] using he a
    · rw [pauliGram_exchange hG, pauliGram_exchange hH]
      simpa only [ha] using he a
  funext ab
  obtain ⟨p, q⟩ := ab
  apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
  rw [← pauliGram_rebuild G, ← pauliGram_rebuild H]
  simp only [hp]

private theorem literalGram_exchange (K B : Fin 2 → Core ℂ) (m : ℕ) :
    GramExchangeSymmetric (literalGram K B m) := by
  have hw (A : Fin 2 → Core ℂ) (p : Bits) (b : Fin m → Fin 2) :
      wordReadout A p b = traceWord 2 2 (2 + m) A (Fin.append ![p.1, p.2] b) := by
    rw [traceWord_eq_wordProduct]
    unfold wordReadout suffixProduct wordProduct
    rw [List.ofFn_fin_append, List.map_append, List.prod_append, List.map_ofFn]
    simp [List.ofFn_succ, Function.comp_def]
  intro p q
  simp only [literalGram]
  let e : (Fin m → Fin 2) ≃ (Fin m → Fin 2) :=
    (Fin.revPerm (n := m)).arrowCongr (Equiv.refl (Fin 2))
  rw [← e.sum_comp (fun b => wordReadout K p.swap b * wordReadout B q.swap b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [hw]
  exact congrArg₂ (· * ·) (joined_trace_swap K m p b) (joined_trace_swap B m q b)

/-- Independent trace coordinates are realized on both complex blocks. -/
theorem coordinates_surjective (x : Coordinate → ℂ) :
    ∃ K B : Fin 2 → Core ℂ, coordinates K B = x := by
  obtain ⟨K, kt, ks, kd, ke, kk⟩ :=
    exists_trace_coordinates (x (0, 0)) (x (0, 1)) (x (0, 2)) (x (0, 3)) (x (0, 4))
  obtain ⟨B, bt, bs, bd, be, bk⟩ :=
    exists_trace_coordinates (x (1, 0)) (x (1, 1)) (x (1, 2)) (x (1, 3)) (x (1, 4))
  refine ⟨K, B, ?_⟩
  funext a
  obtain ⟨b, j⟩ := a
  fin_cases b <;> fin_cases j <;> simp [coordinates, invariants, kt, ks, kd, ke, kk,
    bt, bs, bd, be, bk]

theorem gramChart_exchange (m : ℕ) (x : Coordinate → ℂ) :
    GramExchangeSymmetric (gramChart m x) := by
  obtain ⟨K, B, rfl⟩ := coordinates_surjective x
  intro p q
  rw [← literalGram_eq_chart, ← literalGram_eq_chart]
  exact literalGram_exchange K B m p q

theorem gramDifferential_exchange (m : ℕ) (x v : Coordinate → ℂ) :
    GramExchangeSymmetric (gramDifferential m x v) := by
  intro p q
  have h : gramChart m X (p.swap, q.swap) = (gramChart m X (p, q) : MvPolynomial Coordinate ℂ) := by
    apply MvPolynomial.funext
    intro a
    simp only [map_gramChart, Function.comp_def, eval_X]
    exact gramChart_exchange m a p q
  change jetDifferential x (gramChart m X (p.swap, q.swap)) v =
    jetDifferential x (gramChart m X (p, q)) v
  rw [h]

theorem observedPauliGram_injective_on_differential (m : ℕ) (x v w : Coordinate → ℂ)
    (h : ∀ i, pauliGram Complex.I (gramDifferential m x v) (observedRow i) =
      pauliGram Complex.I (gramDifferential m x w) (observedRow i)) :
    gramDifferential m x v = gramDifferential m x w :=
  observedPauliGram_injective (gramDifferential_exchange m x v) (gramDifferential_exchange m x w) h

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
