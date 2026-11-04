/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Root partial transpose transports actual fully PPT star extensions. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-! The transpose transport uses the original product basis. Full Bose support
is asserted only for the inverse-transposed Bose witness, never for its
CLDUI companion. The empty and full cuts are retained explicitly. -/

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

open private Q Q_mulVec Local.R Local.mem_H_iff Average.avg_left from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

private lemma leaf_conjugation_invariance (root : I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.IsHermitian)
    (hs : leafProjector root * E * leafProjector root = E)
    (σ : Equiv.Perm I) (hσ : σ root = root) :
    ∀ x y, E (x ∘ σ) (y ∘ σ) = E x y := by
  let H := MulAction.stabilizer (Equiv.Perm I) ({root} : Finset I)
  let g : H := ⟨σ, (Local.mem_H_iff {root} σ).mpr (fun i => by
    simp only [Finset.mem_singleton]
    constructor
    · intro hi
      exact σ.injective (hi.trans hσ.symm)
    · rintro rfl
      exact hσ)⟩
  have hfix : Q (L := L) σ * leafProjector root = leafProjector root := by
    exact Average.avg_left ((Local.R I L).comp H.subtype) g
  have hl : leafProjector root * E = E := by
    calc
      leafProjector root * E = leafProjector root *
          (leafProjector root * E * leafProjector root) :=
        congrArg (fun M => leafProjector root * M) hs.symm
      _ = (leafProjector root * leafProjector root) * E * leafProjector root := by
        simp only [Matrix.mul_assoc]
      _ = E := by rw [show leafProjector root * leafProjector root = leafProjector root
          from PiS_idempotent {root}, hs]
  have hrow (x y : I → L) : E (x ∘ σ) y = E x y := by
    have hQ : Q (L := L) σ * E = E := by
      calc
        _ = Q (L := L) σ * (leafProjector root * E) := by rw [hl]
        _ = E := by rw [← Matrix.mul_assoc, hfix, hl]
    have h := congrArg (fun A => A x y) hQ
    change (Q σ *ᵥ (fun z => E z y)) x = E x y at h
    simpa only [Q_mulVec, Function.comp_apply] using h
  intro x y
  calc
    E (x ∘ σ) (y ∘ σ) = E x (y ∘ σ) := hrow x _
    _ = star (E (y ∘ σ) x) := (hE.apply x _).symm
    _ = star (E y x) := congrArg star (hrow y x)
    _ = E x y := hE.apply x y

/-- Positivity at every cut, including the ordinary and full-transpose cuts. -/
def AllCutsPPT (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  ∀ S : Finset I, (partialTransposeOn S E).PosSemidef

private lemma partialTranspose_empty (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn ∅ E = E := by
  ext x y
  simp [partialTransposeOn]

private lemma partialTranspose_univ (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn Finset.univ E = Eᵀ := by
  ext x y
  simp [partialTransposeOn]

private lemma allCuts_iff (E : Matrix (I → L) (I → L) ℂ) :
    AllCutsPPT E ↔ E.PosSemidef ∧ FullyPPT E := by
  constructor
  · intro h
    exact ⟨by simpa only [partialTranspose_empty] using h ∅, fun S _ _ => h S⟩
  · rintro ⟨hE, hppt⟩ S
    by_cases hS : S = ∅
    · simpa only [hS, partialTranspose_empty] using hE
    by_cases hfull : S = Finset.univ
    · simpa only [hfull, partialTranspose_univ] using hE.transpose
    exact hppt S (Finset.nonempty_iff_ne_empty.mpr hS) hfull

/-- Transposing twice replaces the cuts by their symmetric difference. -/
theorem partialTranspose_composition (S T : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (partialTransposeOn T E) = partialTransposeOn (S ∆ T) E := by
  ext x y
  unfold partialTransposeOn
  congr 1 <;> funext i <;> by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.piecewise, hS, hT]

private lemma partialTranspose_involution (S : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (partialTransposeOn S E) = E := by
  rw [partialTranspose_composition, symmDiff_self, partialTranspose_empty]

private lemma allCuts_transpose (T : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : AllCutsPPT E) :
    AllCutsPPT (partialTransposeOn T E) := by
  intro S
  rw [partialTranspose_composition]
  exact hE _

private lemma partialTranspose_complement (S : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn Sᶜ E = (partialTransposeOn S E)ᵀ := by
  ext x y
  unfold partialTransposeOn
  congr 1 <;> funext i <;> by_cases hi : i ∈ S <;>
    simp [Finset.piecewise, hi]

private lemma allCuts_of_leafCuts (root : I)
    (E : Matrix (I → L) (I → L) ℂ)
    (hE : ∀ S : Finset I, root ∉ S → (partialTransposeOn S E).PosSemidef) :
    AllCutsPPT E := by
  intro S
  by_cases hr : root ∈ S
  · have hh := (hE Sᶜ (by simpa using hr)).transpose
    simpa only [partialTranspose_complement, Matrix.transpose_transpose] using hh
  · exact hE S hr

/-- Actual partial transpose of the first member of an ordered pair. -/
def pairRootTranspose (ρ : Matrix (L × L) (L × L) ℂ) :
    Matrix (L × L) (L × L) ℂ :=
  fun x y => ρ (y.1, x.2) (x.1, y.2)

private lemma pairRootTranspose_involution (ρ : Matrix (L × L) (L × L) ℂ) :
    pairRootTranspose (pairRootTranspose ρ) = ρ := by
  ext x y
  rfl

private lemma root_split (root leaf : I) (hne : root ≠ leaf)
    (v w : L × L) (c : {i : I // i ≠ root ∧ i ≠ leaf} → L) :
    ({root} : Finset I).piecewise ((edgeSplit root leaf hne).symm (w,c))
      ((edgeSplit root leaf hne).symm (v,c)) =
        (edgeSplit root leaf hne).symm ((w.1,v.2),c) := by
  funext i
  by_cases hr : i = root
  · subst i
    simp [Finset.piecewise, edgeSplit]
  by_cases hl : i = leaf
  · subst i
    simp [Finset.piecewise, edgeSplit, hne.symm]
  · simp [Finset.piecewise, edgeSplit, hr, hl]

/-- Root transposition commutes with every root--leaf marginal. -/
theorem marginal_rootTranspose (root leaf : I) (hne : root ≠ leaf)
    (E : Matrix (I → L) (I → L) ℂ) :
    edgeMarginal root leaf hne (partialTransposeOn {root} E) =
      pairRootTranspose (edgeMarginal root leaf hne E) := by
  ext v w
  simp only [edgeMarginal,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.submatrix_apply, partialTransposeOn, pairRootTranspose,
    root_split]

private lemma star_rootTranspose_forward (root : I)
    (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : StarExtension root ρ E) :
    StarExtension root (pairRootTranspose ρ) (partialTransposeOn {root} E) := by
  have hp := (allCuts_iff E).mpr ⟨hE.1, hE.2.2.2⟩
  have hpt := (allCuts_iff _).mp (allCuts_transpose {root} E hp)
  refine ⟨hpt.1, ?_, ?_, hpt.2⟩
  · change Local.localP {root} * partialTransposeOn {root} E *
        Local.localP {root} = partialTransposeOn {root} E
    rw [← partialTranspose_PiS_sandwich]
    exact congrArg (partialTransposeOn {root}) hE.2.1
  · intro leaf hne
    rw [marginal_rootTranspose, hE.2.2.1 leaf hne]

/-- Root partial transpose is an involutive transport of fully PPT star witnesses.
Its cuts include the ordinary and full-transpose positivity endpoints. -/
theorem star_rootTranspose_iff (root : I)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ) :
    StarExtension root (pairRootTranspose ρ) (partialTransposeOn {root} E) ↔
      StarExtension root ρ E := by
  constructor
  · intro h
    have hh := star_rootTranspose_forward root _ _ h
    simpa only [partialTranspose_involution, pairRootTranspose_involution] using hh
  · exact star_rootTranspose_forward root ρ E

#print axioms star_rootTranspose_iff

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
