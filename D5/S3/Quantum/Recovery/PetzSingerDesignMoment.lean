import D5.S3.Geometry.FiniteGeometry.SingerTracePlane
import D5.S3.Quantum.Recovery.PetzToricDesignMoment

/-!
# The Singer projective two-design

The trace-zero residues of a primitive element in the cubic field give the
coordinates of the character vectors. The unique ordered differences give
both the Sidon condition for the Haar moment and separation of the character
projectors.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace D5.S3.Quantum.Recovery.PetzSingerDesignMoment

open PetzToricDesignMoment
open D5.S3.Geometry.FiniteGeometry

variable {p : ℕ} [Fact p.Prime]

/-- The cyclic group, in the residue representation of the Singer theorem. -/
abbrev Residue (p : ℕ) := Fin (p ^ 2 + p + 1)

def traceZeroResidues (α : GaloisField p 3) : Finset (Residue p) := by
  classical
  exact Finset.univ.filter fun x =>
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ x.val) = 0

/-- A bijective enumeration of exactly the trace-zero residues. -/
def enumeration (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    Fin (p + 1) ≃ traceZeroResidues α :=
  (Finset.equivFinOfCardEq (SingerTracePlane.result α hα).1).symm

/-- The Singer coordinates viewed in the cyclic group. -/
def residue (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    Fin (p + 1) → Residue p := fun i => (enumeration α hα i).val

private theorem residue_injective {α : GaloisField p 3} {hα : orderOf α = p ^ 3 - 1} :
    Function.Injective (residue α hα) :=
  fun _ _ h => (enumeration α hα).injective (Subtype.ext h)

/-- Each nonzero residue occurs exactly once as first coordinate minus second. -/
private theorem ordered_difference (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1)
    (r : Residue p) (hr : r ≠ 0) :
    ∃! a : Fin (p + 1) × Fin (p + 1), residue α hα a.1 - residue α hα a.2 = r := by
  classical
  let T := Finset.univ.filter fun x : Residue p =>
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ x.val) = 0 ∧
    Algebra.trace (ZMod p) (GaloisField p 3) (α ^ (x + r).val) = 0
  obtain ⟨x, hx, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp
    (show T.card = 1 from (SingerTracePlane.result α hα).2.2.1 r hr)
  have memT (y : Residue p) :
      y ∈ T ↔ y ∈ traceZeroResidues α ∧ y + r ∈ traceZeroResidues α := by
    simp [T, traceZeroResidues]
  obtain ⟨hx₀, hx₁⟩ := (memT x).mp hx
  let e := enumeration α hα
  let a := (e.symm ⟨x + r, hx₁⟩, e.symm ⟨x, hx₀⟩)
  have ha₁ : residue α hα a.1 = x + r :=
    congrArg Subtype.val (e.apply_symm_apply ⟨x + r, hx₁⟩)
  have ha₂ : residue α hα a.2 = x :=
    congrArg Subtype.val (e.apply_symm_apply ⟨x, hx₀⟩)
  refine ⟨a, ?_, ?_⟩
  · change residue α hα a.1 - residue α hα a.2 = r
    rw [ha₁, ha₂]
    abel
  · intro b hb
    have hb₁ : residue α hα b.1 = residue α hα b.2 + r := by
      calc
        _ = (residue α hα b.1 - residue α hα b.2) + residue α hα b.2 :=
          (sub_add_cancel _ _).symm
        _ = _ := by rw [hb, add_comm r]
    have hb₁mem : residue α hα b.1 ∈ traceZeroResidues α := (e b.1).property
    have hx' : residue α hα b.2 = x := huniq _ ((memT _).mpr
      ⟨(e b.2).property, hb₁ ▸ hb₁mem⟩)
    apply Prod.ext
    · exact residue_injective (by rw [hb₁, hx', ha₁])
    · exact residue_injective (hx'.trans ha₂.symm)

private theorem sidon (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    Sidon (residue α hα) := by
  let s := residue α hα
  rintro ⟨i, j⟩ ⟨k, l⟩
  change s i + s j = s k + s l ↔ (i, j) = (k, l) ∨ (i, j) = (l, k)
  constructor
  · intro h
    by_cases hik : i = k
    · subst k
      exact Or.inl (congrArg (fun t => (i, t))
        (residue_injective (add_left_cancel h)))
    · have hr : s i - s k ≠ 0 := fun hz =>
        hik (residue_injective (sub_eq_zero.mp hz))
      have hdiff : s l - s j = s i - s k := by
        calc
          s l - s j = (s k + s l) - (s j + s k) := by abel
          _ = (s i + s j) - (s j + s k) := by rw [h]
          _ = s i - s k := by abel
      obtain ⟨a, _, ha⟩ := ordered_difference α hα (s i - s k) hr
      have hpair : (i, k) = (l, j) := (ha (i, k) rfl).trans (ha (l, j) hdiff).symm
      obtain ⟨hil, hkj⟩ := Prod.mk.inj hpair
      exact Or.inr (Prod.ext hil hkj.symm)
  · rintro (h | h)
    · exact congrArg (pairSum s) h
    · exact (congrArg (pairSum s) h).trans (add_comm (s l) (s k))

abbrev Label (p : ℕ) := AddChar (Residue p) ℂ ⊕ Fin (p + 1)

def projector (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    Label p → Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ
  | .inl χ => characterProjector (residue α hα) χ
  | .inr r => coordinateProjector r

def weight : Label p → ℝ
  | .inl _ => flatWeight (Residue p) (p + 1)
  | .inr _ => coordinateWeight (p + 1)

private theorem projector_injective (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1) :
    Function.Injective (projector α hα) := by
  classical
  have hd : ((p + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero p)
  haveI : Nontrivial (Fin (p + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by have := (Fact.out : p.Prime).two_le; omega)
  have cross (χ : AddChar (Residue p) ℂ) (r : Fin (p + 1)) :
      projector α hα (.inl χ) ≠ projector α hα (.inr r) := by
    intro h
    obtain ⟨i, hi⟩ := exists_ne r
    have hentry := congrArg (fun M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ => M i i) h
    exact (inv_ne_zero hd) (by
      simpa [projector, characterProjector, coordinateProjector, Matrix.single_apply,
        hi, Ne.symm hi] using hentry)
  intro a b h
  cases a with
  | inl χ =>
    cases b with
    | inl ψ =>
      apply congrArg Sum.inl
      ext r
      by_cases hr : r = 0
      · simp [hr]
      · obtain ⟨⟨i, j⟩, hij, _⟩ := ordered_difference α hα r hr
        have hentry := congrArg (fun M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ => M i j) h
        apply mul_left_cancel₀ (inv_ne_zero hd)
        simpa [projector, characterProjector, hij] using hentry
    | inr r => exact (cross χ r h).elim
  | inr r =>
    cases b with
    | inl χ => exact (cross χ r h.symm).elim
    | inr t =>
      apply congrArg Sum.inr
      by_contra hrt
      have hentry := congrArg (fun M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ => M r r) h
      have htr : t ≠ r := Ne.symm hrt
      exact (one_ne_zero : (1 : ℂ) ≠ 0) (by
        simpa [projector, coordinateProjector, Matrix.single_apply, htr] using hentry)

private theorem projector_unit_outer_product (α : GaloisField p 3)
    (hα : orderOf α = p ^ 3 - 1) (a : Label p) :
    ∃ v : Fin (p + 1) → ℂ, (∑ i, v i * star (v i)) = 1 ∧
      projector α hα a = Matrix.vecMulVec v (fun i => star (v i)) := by
  classical
  cases a with
  | inl χ =>
    let c : ℂ := (Real.sqrt ((p + 1 : ℕ) : ℝ) : ℂ)⁻¹
    have hcstar : star c = c := by simp [c]
    have hc : c * c = ((p + 1 : ℕ) : ℂ)⁻¹ := by
      dsimp only [c]
      rw [← mul_inv_rev, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
        Complex.ofReal_natCast]
    let s := residue α hα
    have hout : projector α hα (.inl χ) =
        Matrix.vecMulVec (fun i => c * χ (s i)) (fun i => star (c * χ (s i))) := by
      ext i j
      simp only [projector, characterProjector, Matrix.of_apply, Matrix.vecMulVec_apply,
        star_mul, hcstar]
      rw [Complex.star_def, ← χ.map_neg_eq_conj, ← hc, sub_eq_add_neg, χ.map_add_eq_mul]
      ring
    refine ⟨fun i => c * χ (s i), ?_, hout⟩
    have hdiag (i : Fin (p + 1)) : (c * χ (s i)) * star (c * χ (s i)) =
        ((p + 1 : ℕ) : ℂ)⁻¹ := by
      have he := congrArg (fun M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ => M i i) hout.symm
      simpa [Matrix.vecMulVec_apply, projector, characterProjector] using he
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero p))
  | inr r =>
    let v : Fin (p + 1) → ℂ := fun i => if i = r then 1 else 0
    refine ⟨v, ?_, ?_⟩
    · calc
        ∑ i, v i * star (v i) = v r * star (v r) := by
          apply Finset.sum_eq_single r
          · intro i _ hi
            simp [v, hi]
          · simp
        _ = 1 := by simp [v]
    · ext i j
      by_cases hi : i = r <;> by_cases hj : j = r <;>
        simp [projector, coordinateProjector, Matrix.vecMulVec_apply, v, hi, hj, Ne.symm]

private theorem exists_primitive : ∃ α : GaloisField p 3, orderOf α = p ^ 3 - 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (GaloisField p 3)ˣ)
  refine ⟨(u : GaloisField p 3), ?_⟩
  rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units,
    GaloisField.card p 3 (by decide)]

/-- The actual Singer character and coordinate projectors form a positive weighted
projective two-design with exactly `(p + 1)^2 + 1` distinct projections. -/
theorem result :
    ∃ (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1),
      Sidon (residue α hα) ∧
      Fintype.card (Label p) = (p + 1) ^ 2 + 1 ∧
      Function.Injective (projector α hα) ∧
      (∀ a : Label p, ∃ v : Fin (p + 1) → ℂ, (∑ i, v i * star (v i)) = 1 ∧
        projector α hα a = Matrix.vecMulVec v (fun i => star (v i))) ∧
      (∀ a : Label p, 0 < weight a) ∧ (∑ a : Label p, weight a) = 1 ∧
      (∑ a : Label p, (weight a : ℂ) • (projector α hα a ⊗ₖ projector α hα a)) =
        haarMoment (p + 1) := by
  classical
  obtain ⟨α, hα⟩ := exists_primitive (p := p)
  have hs := sidon α hα
  have hd : 0 < p + 1 := Nat.succ_pos p
  obtain ⟨hflat, hcoord, htotal⟩ :=
    weights_positive_and_sum (G := Residue p) hd
  refine ⟨α, hα, hs, ?_, projector_injective α hα, projector_unit_outer_product α hα,
    ?_, ?_, ?_⟩
  · simp only [Label, Fintype.card_sum, AddChar.card_eq, Residue, Fintype.card_fin]
    ring
  · rintro (χ | r)
    · exact hflat
    · exact hcoord
  · simpa only [Fintype.sum_sum_type, weight] using htotal
  · simpa only [Fintype.sum_sum_type, projector, weight, weightedMoment, flatSum,
      coordinateSum, Finset.smul_sum] using weightedMoment_eq_haar hd (residue α hα) hs

end D5.S3.Quantum.Recovery.PetzSingerDesignMoment
