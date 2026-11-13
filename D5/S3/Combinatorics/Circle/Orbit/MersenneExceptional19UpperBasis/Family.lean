/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Family
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Result]
   utility: none
   digest: Integral exceptional19 UpperBasis Family on original physical labels. -/
/- UNCOMPILED source preparation. No basis theorem is asserted in this module.
   Requires the sealed additive-helper delta, with original declaration names. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Result
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base seed place total)
open MersenneExceptional19PermutationStabilizer
  (aa bb eighth eighth_facts parameter_margins physical qLow qMid q8Low q8Mid q_zero)
open MersenneExceptional19ZeroLattice (integerWeightedSum coordinateGenerator)
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent (row)
open private affine affine_zero
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
open private gPoint fPoint hPoint gPoint_data fPoint_data hPoint_data
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
open private triple triple_total triples_disjoint
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.NormalForm
open private weighted_sum_row
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Result

/-- The G, F, H upper rows, followed by the eight terminal actual masks.
G-small uses j=1,...,d-4; F-small and H use j=2,...,d-3.
The two G extras are at j=d-2,d-1; the F extra is at j=d-2. -/
abbrev UpperIndex (r : ℕ) :=
  (Fin (degree r-4) ⊕ Fin 2) ⊕
    ((Fin (degree r-4) ⊕ Fin 1) ⊕ (Fin (degree r-4) ⊕ Fin 8))

theorem card_upperIndex (r : ℕ) : Fintype.card (UpperIndex r)=3*degree r-1 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  simp only [UpperIndex,Fintype.card_sum,Fintype.card_fin]
  omega

/-- The fourth mask is ONE disjoint-union indicator, not two rows or a
signed relation. The last two masks are the sealed base-B digits of Q,8Q. -/
def terminalMask (r : ℕ) : Fin 8 → Finset (Fin (3*degree r)) :=
  ![triple ⟨0,by dsimp [degree]; omega⟩,
    triple ⟨1,by dsimp [degree]; omega⟩,
    triple ⟨degree r-2,by dsimp [degree]; omega⟩,
    triple ⟨degree r-3,by dsimp [degree]; omega⟩ ∪
      triple ⟨degree r-1,by dsimp [degree]; omega⟩,
    affine r (aa r), affine r (3*eighth r),
    physical (degree r) (qLow r) (qMid r) 0,
    physical (degree r) (q8Low r) (q8Mid r) 0]

/-- Precisely the selected UPPER actual endpoints; no lower endpoint occurs. -/
def selectedMask (r : ℕ) : UpperIndex r → Finset (Fin (3*degree r)) :=
  Sum.elim
    (Sum.elim
      (fun j => affine r (gPoint r (j.val+1)))
      (fun k => if k=0 then affine r (gPoint r (degree r-2))
        else affine r (gPoint r (degree r-1))))
    (Sum.elim
      (Sum.elim
        (fun j => affine r (fPoint r (j.val+2)))
        (fun _ => affine r (fPoint r (degree r-2))))
      (Sum.elim (fun j => affine r (hPoint r (j.val+2))) (terminalMask r)))

private theorem terminal_zero (r : ℕ) (k : Fin 8) :
    total r (terminalMask r k)=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  have triple_zero (j : Fin (degree r))
      (h3 : j.val≠degree r-3) (h1 : j.val≠degree r-1) :
      total r (triple j)=0 := by
    rw [triple_total]
    simp [h3,h1]
  fin_cases k
  · exact triple_zero ⟨0,by omega⟩ (by change (0 : ℕ)≠degree r-3; omega) (by change (0 : ℕ)≠degree r-1; omega)
  · exact triple_zero ⟨1,by omega⟩ (by change (1 : ℕ)≠degree r-3; omega) (by change (1 : ℕ)≠degree r-1; omega)
  · exact triple_zero ⟨degree r-2,by omega⟩ (by change degree r-2≠degree r-3; omega) (by change degree r-2≠degree r-1; omega)
  · let j : Fin (degree r) := ⟨degree r-3,by omega⟩
    let k : Fin (degree r) := ⟨degree r-1,by omega⟩
    have hjk : j≠k := by
      intro he
      have := congrArg Fin.val he
      dsimp [j,k] at this
      omega
    change total r (triple j ∪ triple k)=0
    unfold total
    rw [Finset.sum_union (triples_disjoint (by omega) j k hjk)]
    change total r (triple j)+total r (triple k)=0
    rw [triple_total,triple_total]
    simp [j,k,show degree r-3≠degree r-1 by omega,
      show degree r-1≠degree r-3 by omega]
  · exact affine_zero r (aa r) (Or.inl rfl)
  · refine affine_zero r _ (Or.inr (Or.inl ⟨le_rfl,?_⟩))
    obtain ⟨hB,hq,hm⟩ := eighth_facts r
    obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ := parameter_margins r
    omega
  · exact (q_zero r).1
  · exact (q_zero r).2

/-- Every selected mask has literal integer actualSource sum zero, for every
natural r including zero. This establishes membership, not selected spanning. -/
theorem selected_literal_zero (r : ℕ) (k : UpperIndex r) :
    (∑ i ∈ selectedMask r k, SourceWidth.actualSource (3*(18*r+12))
      ((2^(18*r+12)-1)*(2^((18*r+12)+1)-3)) i)=0 := by
  change total r (selectedMask r k)=0
  have hd : 12≤degree r := by dsimp [degree]; omega
  cases k with
  | inl k =>
    cases k with
    | inl j =>
      change total r (affine r (gPoint r (j.val+1)))=0
      exact affine_zero r _ (gPoint_data r (j.val+1)
        ⟨by omega,by omega,by omega⟩).1
    | inr k =>
      change total r (if k=0 then affine r (gPoint r (degree r-2))
        else affine r (gPoint r (degree r-1)))=0
      by_cases hk : k=0
      · rw [if_pos hk]
        exact affine_zero r _ (gPoint_data r (degree r-2)
          ⟨by omega,by omega,by omega⟩).1
      · rw [if_neg hk]
        exact affine_zero r _ (gPoint_data r (degree r-1)
          ⟨by omega,by omega,by omega⟩).1
  | inr k =>
    cases k with
    | inl k =>
      cases k with
      | inl j =>
        change total r (affine r (fPoint r (j.val+2)))=0
        exact affine_zero r _ (fPoint_data r (j.val+2) ⟨by omega,by omega⟩).1
      | inr k =>
        change total r (affine r (fPoint r (degree r-2)))=0
        exact affine_zero r _ (fPoint_data r (degree r-2) ⟨by omega,by omega⟩).1
    | inr k =>
      cases k with
      | inl j =>
        change total r (affine r (hPoint r (j.val+2)))=0
        exact affine_zero r _ (hPoint_data r (j.val+2) ⟨by omega,by omega⟩).1
      | inr k => exact terminal_zero r k

/-- The actual selected family as elements of the ORIGINAL integer kernel. -/
def selectedRow (r : ℕ) (k : UpperIndex r) : Fin (3*degree r) → ℤ :=
  row (selectedMask r k)

/-- No coordinate change is used in this subtype. -/
def selectedKernelRow (r : ℕ) (k : UpperIndex r) :
    LinearMap.ker (integerWeightedSum r) :=
  ⟨selectedRow r k, by
    change integerWeightedSum r (row (selectedMask r k))=0
    rw [weighted_sum_row]
    exact selected_literal_zero r k⟩

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
