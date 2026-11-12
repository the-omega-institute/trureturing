/- Source implementation only; no elaboration or native acceptance is claimed.
   Classical all-state skew symmetry is consumed from the pinned supplier.
   The raw exponent Q+k corresponds to mode -k-1, throughout this file.
   The original full VOA/CFT/fusion/string/AdS goal remains incomplete. -/
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetFusion
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.LatticeCosetRationalSkew
attribute [local instance] Classical.propDecidable
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeCosetInnerExpansion
open LatticeCosetCanonicalIntertwiner LatticeDualCosetConformal LatticeSugawaraCurrents
open LatticeSugawaraConformal LatticeDiscriminantTheta
open StateField.SkewSymmetry
open private compressedField_modes from D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion
open private shift_symmetric from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private lawful_smul from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetIntertwiner

variable (D : LatticeData) {e : ℕ} (B : Matrix (Fin D.rank) (Fin e) ℤ)

/-- Iteration of the accepted all-ambient-state projection identity. -/
theorem projection_translation_pow (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (d : Fin e → ℤ) (j : ℕ)
    (v : Carrier (ambient D e B 0 zeroSymm zeroEven)) :
    projection D B 0 zeroSymm zeroEven d
        ((LatticeSugawaraConformal.translation (ambient D e B 0 zeroSymm zeroEven) ^ j) v) =
      (moduleL D (Matrix.mulVec B d) H (-1) ^ j)
        (projection D B 0 zeroSymm zeroEven d v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, projection_translation D B hD H hHG hGH,
      ih, pow_succ', Module.End.mul_apply]

/-- Projection of ambient skew, on all original states and every signed mode. -/
theorem compressed_skew (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (n : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          (compressed D B 0 zeroSymm zeroEven b a v (n+j) u)) ∧
    compressed D B 0 zeroSymm zeroEven a b u n v = ∑ᶠ j : ℕ,
      (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          (compressed D B 0 zeroSymm zeroEven b a v (n+j) u) := by
  let E := ambient D e B 0 zeroSymm zeroEven
  let J := injection D B 0 zeroSymm zeroEven
  let P := projection D B 0 zeroSymm zeroEven (a+b)
  have hs := ((skew_symmetry (LatticeActualVertexAlgebra.actualVertexAlgebra E)
    (J a u) (J b v)).1 n)
  dsimp only [LatticeActualVertexAlgebra.actualVertexAlgebra] at hs
  have term (j : ℕ) :
      P (((( -1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
        (LatticeSugawaraConformal.translation E ^ j) (((Y E (J b v))[[n+j]]) (J a u))) =
      (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          (compressed D B 0 zeroSymm zeroEven b a v (n+j) u) := by
    rw [map_smul, projection_translation_pow D B hD H hHG hGH]
    congr 2
    simp only [compressed, LinearMap.comp_apply, add_comm b a]
  refine ⟨?_, ?_⟩
  · apply hs.1.subset
    intro j hj hz
    apply hj
    rw [← term j, hz, map_zero]
  · have h := congrArg P hs.2
    rw [map_finsum P hs.1] at h
    change compressed D B 0 zeroSymm zeroEven a b u n v = _ at h
    rw [h]
    exact finsum_congr term

/-- The literal raw rational coefficient, with the corrected integer index. -/
theorem raw_skew (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) (k : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (((-1 : ℂ) ^ (k-(j : ℤ))) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ)) u)) ∧
    (intertwiner D B a b u).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ)) v = ∑ᶠ j : ℕ,
      (((-1 : ℂ) ^ (k-(j : ℤ))) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ)) u) := by
  have h := compressed_skew D B hD H hHG hGH a b u v (-k-1)
  have term (j : ℕ) :
      (((-1 : ℂ) ^ (-k-1+(j : ℤ)+1)) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          (compressed D B 0 zeroSymm zeroEven b a v (-k-1+j) u) =
      (((-1 : ℂ) ^ (k-(j : ℤ))) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ)) u) := by
    have sign : (-1 : ℂ) ^ (-k-1+(j : ℤ)+1) = (-1 : ℂ) ^ (k-(j : ℤ)) := by
      rw [show -k-1+(j : ℤ)+1 = -(k-(j : ℤ)) by omega, zpow_neg, ← inv_zpow]
      norm_num
    rw [sign]
    congr 2
    change _ = HVertexOperator.coeff (field D B b a v) _ u
    rw [show LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ) =
      LatticeCosetCanonicalIntertwiner.shift D B b a + ((k-(j : ℤ) : ℤ) : ℚ) by
        rw [shift_symmetric D B a b]; push_cast; ring,
      field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
    congr 1 <;> omega
  rw [funext term] at h
  refine ⟨h.1, ?_⟩
  have hc := mode_integer D B a b u v (-k-1)
  unfold LatticeCosetCanonicalIntertwiner.mode at hc
  rw [show -(((-k-1 : ℤ) : ℚ)-LatticeCosetCanonicalIntertwiner.shift D B a b)-1 =
    LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) by push_cast; ring] at hc
  rw [hc]
  exact h.2

/-- One cutoff belongs to the particular reversed pair (v,u). Signed k and
    an empty range are covered by the same integer inequality. -/
theorem raw_pair_cutoff (a b : Fin e → ℤ) (u v : Carrier D) :
    ∃ N : ℕ, ∀ (k : ℤ) (j : ℕ), ((N : ℤ)+k+1).toNat ≤ j →
      (intertwiner D B b a v).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ)) u = 0 := by
  obtain ⟨N,hN⟩ := compressed_high_modes D B 0 zeroSymm zeroEven b a v u 0
  refine ⟨N, ?_⟩
  intro k j hj
  change HVertexOperator.coeff (field D B b a v) _ u = 0
  rw [show LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ) =
      LatticeCosetCanonicalIntertwiner.shift D B b a + ((k-(j : ℤ) : ℤ) : ℚ) by
        rw [shift_symmetric D B a b]; push_cast; ring,
    field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
  have hm : 0 ≤ -k+(j : ℤ)-1 := by omega
  have hn : N ≤ (-k+(j : ℤ)-1).toNat := by omega
  rw [show -(k-(j : ℤ))-1 = -k+(j : ℤ)-1 by omega]
  simpa only [zero_add, Int.toNat_of_nonneg hm] using hN _ hn

/-- A genuine reversal series on the original compressed integer Hahn series.
    This definition contains the finite convolution, not the desired field. -/
def reversedSeries (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a b : Fin e → ℤ) (u v : Carrier D) : HahnSeries ℚ (Carrier D) :=
  HahnSeries.embDomain (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B a b))
    (reversal (moduleL D (Matrix.mulVec B (a+b)) H (-1))
      ((HahnModule.of ℂ).symm (compressedField D B 0 zeroSymm zeroEven b a v u)))

theorem reversedSeries_eq (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) (u v : Carrier D) :
    reversedSeries D B H a b u v = (HahnModule.of ℂ).symm (intertwiner D B a b u v) := by
  apply HahnSeries.ext
  funext q
  by_cases hq : q ∈ Set.range (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B a b))
  · obtain ⟨k,rfl⟩ := hq
    change (HahnSeries.embDomain _ _).coeff (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B a b) k) = _
    rw [HahnSeries.embDomain_coeff]
    change (∑ᶠ j : ℕ, reversalTerm _ _ k j) =
      (intertwiner D B a b u).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ)) v
    rw [(raw_skew D B hD H hHG hGH a b u v k).2]
    apply finsum_congr
    intro j
    unfold reversalTerm
    congr 2
    change HVertexOperator.coeff (compressedField D B 0 zeroSymm zeroEven b a v)
      (k-(j : ℤ)) u = _
    rw [show LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) - (j : ℚ) =
      LatticeCosetCanonicalIntertwiner.shift D B b a + ((k-(j : ℤ) : ℤ) : ℚ) by
        rw [shift_symmetric D B a b]; push_cast; ring]
    exact (field_coeff D B b a v u (k-j)).symm
  · change (HahnSeries.embDomain _ _).coeff q = _
    rw [HahnSeries.embDomain_of_notMem_range hq]
    exact (field_coeff_off D B a b u v q hq).symm

def Omega (a b : Fin e → ℤ) : ℂ := Complex.exp (Real.pi * Complex.I * (LatticeCosetCanonicalIntertwiner.shift D B a b : ℂ))

theorem Omega_ne_zero (a b : Fin e → ℤ) : Omega D B a b ≠ 0 := Complex.exp_ne_zero _

theorem Omega_symm (a b : Fin e → ℤ) : Omega D B a b = Omega D B b a := by
  rw [Omega, Omega, shift_symmetric D B a b]

/-- The branch controls only the exponential phase. Both branches start from
    the actual finite reversal, before any field-equality proof. -/
def turnValue (positive : Bool) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a b : Fin e → ℤ) (u v : Carrier D) : HahnModule ℚ ℂ (Carrier D) :=
  HahnModule.of ℂ ((if positive then Omega D B a b else (Omega D B a b)⁻¹) •
    reversedSeries D B H a b u v)

theorem turnValue_eq (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Fin e → ℤ) (u v : Carrier D) :
    turnValue D B positive H a b u v =
      (if positive then Omega D B a b else (Omega D B a b)⁻¹) • intertwiner D B a b u v := by
  rw [turnValue, reversedSeries_eq D B hD H hHG hGH]
  apply (HahnModule.of ℂ).symm.injective
  simp only [Equiv.symm_apply_apply, HahnModule.of_symm_smul]

/-- Source and input linearity are proved after constructing the convolution.
    No uniqueness or Lawful assertion is used to establish this field. -/
def turn (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Fin e → ℤ) : LatticeDualCosetIntertwiner.Fields D where
  toFun u :=
    { toFun := turnValue D B positive H a b u
      map_add' v w := by simp only [turnValue_eq D B hD H hHG hGH, map_add, smul_add]
      map_smul' z v := by
        simp only [turnValue_eq D B hD H hHG hGH, map_smul, RingHom.id_apply]
        exact smul_comm _ _ _ }
  map_add' u w := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, turnValue_eq D B hD H hHG hGH,
      map_add, LinearMap.add_apply, smul_add]
  map_smul' z u := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, turnValue_eq D B hD H hHG hGH,
      map_smul, LinearMap.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem turn_eq (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Fin e → ℤ) :
    turn D B hD H hHG hGH positive a b =
      (if positive then Omega D B a b else (Omega D B a b)⁻¹) • intertwiner D B a b := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  exact turnValue_eq D B hD H hHG hGH positive a b u v

abbrev Rplus (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) : LatticeDualCosetIntertwiner.Fields D :=
  turn D B hD H hHG hGH true a b

abbrev Rminus (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : Fin e → ℤ) : LatticeDualCosetIntertwiner.Fields D :=
  turn D B hD H hHG hGH false a b

/-- Integer phases are evaluated by the usual exponential power identity. -/
private theorem exp_pi_int (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1 : ℂ)^n := by
  rw [mul_comm (Real.pi * Complex.I) (n : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem exp_phase (positive : Bool) (a b : Fin e → ℤ) (n : ℤ) :
    Complex.exp ((if positive then (1 : ℂ) else -1) *
      (Real.pi * Complex.I * ((LatticeCosetCanonicalIntertwiner.shift D B a b : ℂ)+(n : ℂ)))) =
      (if positive then Omega D B a b else (Omega D B a b)⁻¹) * (-1 : ℂ)^n := by
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [mul_add, neg_add, Complex.exp_add, Complex.exp_neg,
      Complex.exp_neg, exp_pi_int, ← inv_zpow]
    norm_num [Omega]
  · simp only [↓reduceIte, one_mul]
    rw [mul_add, Complex.exp_add, exp_pi_int]
    rfl

/-- Literal positive/negative half-turn coefficient formula at EVERY rational q.
    The proof explicitly separates the supported coset from its complement. -/
theorem turn_coeff (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Fin e → ℤ) (u v : Carrier D) (q : ℚ) :
    (turn D B hD H hHG hGH positive a b u).coeff q v = ∑ᶠ j : ℕ,
      (Complex.exp ((if positive then (1 : ℂ) else -1) *
        (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ)))) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (q-(j : ℚ)) u) := by
  by_cases hq : q ∈ Set.range (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B a b))
  · obtain ⟨k,rfl⟩ := hq
    rw [turn_eq D B hD H hHG hGH]
    change (if positive then Omega D B a b else (Omega D B a b)⁻¹) •
      (intertwiner D B a b u).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ)) v = _
    rw [(raw_skew D B hD H hHG hGH a b u v k).2,
      smul_finsum' _ (raw_skew D B hD H hHG hGH a b u v k).1]
    apply finsum_congr
    intro j
    rw [smul_smul]
    congr 1
    have hp := exp_phase D B positive a b (k-(j : ℤ))
    push_cast at hp
    rw [show ((LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) : ℚ) : ℂ) - (j : ℂ) =
      (LatticeCosetCanonicalIntertwiner.shift D B a b : ℂ) + ((k : ℂ)-(j : ℂ)) by push_cast; ring, hp]
    ring
  · rw [turn_eq D B hD H hHG hGH]
    change (if positive then Omega D B a b else (Omega D B a b)⁻¹) •
      (intertwiner D B a b u).coeff q v = _
    rw [field_coeff_off D B a b u v q hq, smul_zero]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hj : q-(j : ℚ) ∉ Set.range (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B b a)) := by
      rintro ⟨k,hk⟩
      apply hq
      refine ⟨k+(j : ℤ), ?_⟩
      dsimp [exponentEmbedding] at hk ⊢
      rw [shift_symmetric D B a b]
      push_cast
      linarith
    rw [field_coeff_off D B b a v u _ hj, map_zero, smul_zero]

/-- Explicit support witnesses for the literal convolution, not just a
    formal assertion that a finsum exists. No uniform bound on inputs occurs. -/
theorem turn_terms_support (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (positive : Bool) (a b : Fin e → ℤ) (u v : Carrier D) :
    ∃ N : ℕ, ∀ k : ℤ, Function.support (fun j : ℕ =>
      (Complex.exp ((if positive then (1 : ℂ) else -1) *
        (Real.pi * Complex.I * (((LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ) : ℚ) : ℂ)-(j : ℂ)))) /
          (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b + (k : ℚ)-(j : ℚ)) u)) ⊆
      Finset.range (((N : ℤ)+k+1).toNat) := by
  obtain ⟨N,hN⟩ := raw_pair_cutoff D B a b u v
  refine ⟨N, ?_⟩
  intro k j hj
  apply Finset.mem_range.mpr
  by_contra hn
  exact hj (by rw [hN k j (by omega), map_zero, smul_zero])

theorem turn_terms_finite (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (positive : Bool) (a b : Fin e → ℤ) (u v : Carrier D) (q : ℚ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (Complex.exp ((if positive then (1 : ℂ) else -1) *
        (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ)))) / (j.factorial : ℂ)) •
        (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
          ((intertwiner D B b a v).coeff (q-(j : ℚ)) u)) := by
  by_cases hq : q ∈ Set.range (exponentEmbedding (LatticeCosetCanonicalIntertwiner.shift D B a b))
  · obtain ⟨k,rfl⟩ := hq
    obtain ⟨N,hN⟩ := turn_terms_support D B H positive a b u v
    exact (Finset.finite_toSet _).subset (hN k)
  · have hz (j : ℕ) : (intertwiner D B b a v).coeff (q-(j : ℚ)) u = 0 := by
      apply field_coeff_off
      rintro ⟨k,hk⟩
      apply hq
      refine ⟨k+(j : ℤ), ?_⟩
      dsimp [exponentEmbedding] at hk ⊢
      rw [shift_symmetric D B a b]
      push_cast
      linarith
    have he : (fun j : ℕ =>
        (Complex.exp ((if positive then (1 : ℂ) else -1) *
          (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ)))) / (j.factorial : ℂ)) •
          (moduleL D (Matrix.mulVec B (a+b)) H (-1) ^ j)
            ((intertwiner D B b a v).coeff (q-(j : ℚ)) u)) = 0 := by
      funext j
      simp only [hz j, map_zero, smul_zero, Pi.zero_apply]
    rw [he]
    apply (Set.finite_empty : (∅ : Set ℕ).Finite).subset
    intro j hj
    exact False.elim (hj rfl)

/-- Full original Lawful follows only after the complete field equality.
    The private accepted closure lemma retains all THREE Jacobi supports. -/
theorem turn_lawful (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Charge D) :
    LatticeDualCosetIntertwiner.Lawful D a b H
      (turn D (1 : Matrix _ _ ℤ) hD H hHG hGH positive a b) := by
  rw [turn_eq D (1 : Matrix _ _ ℤ) hD H hHG hGH]
  exact lawful_smul D a b H _ _ (LatticeDualCosetFusion.canonical_lawful D hD a b H hHG hGH)

theorem turn_ground (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Fin e → ℤ) :
    (turn D B hD H hHG hGH positive a b (vacuum D)).coeff (LatticeCosetCanonicalIntertwiner.shift D B a b) (vacuum D) =
      (if positive then Omega D B a b else (Omega D B a b)⁻¹) • vacuum D := by
  rw [turn_eq D B hD H hHG hGH]
  change _ • (intertwiner D B a b (vacuum D)).coeff _ (vacuum D) = _
  rw [ground_coefficient]

/-- Only after full equality and Lawful status, use the original scalar
    equivalence. Its ground coordinate is the original normalized one. -/
theorem scalarEquiv_turn (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (positive : Bool) (a b : Charge D) (μ ν : Fin D.rank → ℚ)
    (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
    (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ)) :
    LatticeDualCosetFusion.scalarEquiv D hD a b H hHG hGH μ ν ha hb
      ⟨turn D (1 : Matrix _ _ ℤ) hD H hHG hGH positive a b,
        turn_lawful D hD H hHG hGH positive a b⟩ =
      (if positive then Omega D (1 : Matrix _ _ ℤ) a b else
        (Omega D (1 : Matrix _ _ ℤ) a b)⁻¹) := by
  let z := if positive then Omega D (1 : Matrix _ _ ℤ) a b else
    (Omega D (1 : Matrix _ _ ℤ) a b)⁻¹
  have he : (⟨turn D (1 : Matrix _ _ ℤ) hD H hHG hGH positive a b,
        turn_lawful D hD H hHG hGH positive a b⟩ :
      LatticeDualCosetIntertwiner.operatorSpace D a b H) =
      z • LatticeDualCosetFusion.canonicalOperator D hD a b H hHG hGH := by
    apply Subtype.ext
    exact turn_eq D (1 : Matrix _ _ ℤ) hD H hHG hGH positive a b
  rw [he]
  change LatticeDualCosetIntertwiner.groundEvaluation D a b H μ ν
    (z • LatticeDualCosetFusion.canonicalOperator D hD a b H hHG hGH) = z
  rw [map_smul, LatticeDualCosetFusion.canonical_groundEvaluation D hD a b H hHG hGH μ ν ha hb]
  simp

end D5.S3.VertexAlgebra.LatticeCosetRationalSkew
