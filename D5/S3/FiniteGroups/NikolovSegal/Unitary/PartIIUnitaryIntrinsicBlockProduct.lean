/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicBlockProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryIntrinsicBlockProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryIntrinsicPrescribedProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PrescribedProductComposition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.PartIIUnitaryIntrinsicBlockProduct
open PartIIUnitriangularLayers UnitarySylow UnitaryField
open PartIIUnitaryIntrinsicPrescribedProduct PrescribedProductComposition
open scoped Pointwise
universe u
variable {F : Type u} [Field F] {n : ℕ}

def positiveSet (ι : RingAut F) : Set (specialUnitary n ι) :=
  {g | LayerDepth 1 (g.val.val-1)}

def negativeSet (ι : RingAut F) : Set (specialUnitary n ι) :=
  {g | SLnUnipotentWidth.Lower g.val}

/-- One uniform length and cutoff cover every ordered U L U L U target,
with original divisor powers and one correction chosen before all targets.
Whole-SU width is consumed separately, through its proved factorization. -/
theorem actual_uniform_intrinsic_five_block_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F) (hinv : Function.Involutive ι)
      (hne : ι≠RingEquiv.refl F), ∀ n : ℕ, 6≤n →
      ∀ (a : Fin N → Fin n → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      ∀ ha : ∀ j i, ι (a j i:F)*(a j i.rev:F)=((c j:fixedField ι):F),
      ∀ (phi : Fin N → RingAut F) (e : Fin N → ℕ),
      (∀ j, 0<e j ∧ e j∣q) →
      Covers q (fun j => action ι (phi j) hinv hne (a j) (c j) (ha j)) e
        (positiveSet ι * (negativeSet ι *
          (positiveSet ι * (negativeSet ι * positiveSet ι)))) := by
  obtain ⟨P,CP,hP,hpos⟩ := actual_uniform_intrinsic_positive_q_over_e_product q hq
  obtain ⟨L,CL,hL,hneg⟩ := actual_uniform_intrinsic_negative_q_over_e_product q hq
  let N := P+(L+(P+(L+P)))
  refine ⟨N,max CP CL,by omega,?_⟩
  intro F _ _ _ hF ι hinv hne n hn a c ha phi e he
  have hFP : CP<Fintype.card F := lt_of_le_of_lt (le_max_left _ _) hF
  have hFL : CL<Fintype.card F := lt_of_le_of_lt (le_max_right _ _) hF
  let beta := fun j => action ι (phi j) hinv hne (a j) (c j) (ha j)
  have hp : ∀ f : Fin P → Fin N,
      Covers q (fun j => beta (f j)) (fun j => e (f j)) (positiveSet ι) := by
    intro f
    obtain ⟨y,hy⟩ := hpos F hFP ι hinv hne n hn (fun j => a (f j))
      (fun j => c (f j)) (fun j => ha (f j)) (fun j => phi (f j))
      (fun j => e (f j)) (fun j => he (f j))
    refine ⟨y,?_⟩
    intro b hb
    obtain ⟨x,_,hx⟩ := hy b hb
    exact ⟨x,hx⟩
  have hl : ∀ f : Fin L → Fin N,
      Covers q (fun j => beta (f j)) (fun j => e (f j)) (negativeSet ι) := by
    intro f
    obtain ⟨y,hy⟩ := hneg F hFL ι hinv hne n hn (fun j => a (f j))
      (fun j => c (f j)) (fun j => ha (f j)) (fun j => phi (f j))
      (fun j => e (f j)) (fun j => he (f j))
    refine ⟨y,?_⟩
    intro b hb
    obtain ⟨x,_,hx⟩ := hy b hb
    exact ⟨x,hx⟩
  apply covers_append q beta e
  · exact hp (fun j => j.castAdd (L+(P+(L+P))))
  · apply covers_append q (fun j => beta (j.natAdd P)) (fun j => e (j.natAdd P))
    · exact hl (fun j => (j.castAdd (P+(L+P))).natAdd P)
    · apply covers_append q (fun j => beta ((j.natAdd L).natAdd P))
        (fun j => e ((j.natAdd L).natAdd P))
      · exact hp (fun j => ((j.castAdd (L+P)).natAdd L).natAdd P)
      · apply covers_append q (fun j => beta (((j.natAdd P).natAdd L).natAdd P))
          (fun j => e (((j.natAdd P).natAdd L).natAdd P))
        · exact hl (fun j => (((j.castAdd P).natAdd P).natAdd L).natAdd P)
        · exact hp (fun j => (((j.natAdd L).natAdd P).natAdd L).natAdd P)

end NikolovSegal.PartIIUnitaryIntrinsicBlockProduct
