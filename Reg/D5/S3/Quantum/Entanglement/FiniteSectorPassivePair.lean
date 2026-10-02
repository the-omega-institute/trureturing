import D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
import Reg.Support.DependentFamily
import Reg.Support.FiniteSectorSingleton

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℂ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => star x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} {EX : Type u} {EY : Type u} [Fintype Sector] [DecidableEq Sector]
    [Fintype EX] [DecidableEq EX] [Fintype EY] [DecidableEq EY]
    {J : ℕ} (M : Model Sector J)
    (VX : Matrix (EX × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (VY : Matrix (EY × TargetLocal M.d) (SourceLocal (Coord := Fin J) M.d) ℂ)
    (hVX : VXᴴ * VX = 1) (hVY : VYᴴ * VY = 1),
    let C : Sector → Matrix (SourceLocal (Coord := Fin J) M.d)
        (SourceLocal (Coord := Fin J) M.d) ℂ := fun s => Matrix.diagonal fun u =>
      if u.1 = s then (Real.sqrt (M.spectrum s u.2.2 / (M.d s : ℝ)) : ℂ) else 0
    let Q := fun s => VX * C s * VY.transpose
    let Z : Sector → Matrix EX EY ℂ := fun s ex ey =>
      (((Real.sqrt (M.d s : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a : Fin (M.d s), Q s (ex, ⟨s, a⟩) (ey, ⟨s, a⟩)
    ∀ s t, (∑ ex, ∑ ey, R.readout ⟨()⟩ () (Z s ex ey) * Z t ex ey).re ≤ kernel M s t

theorem actual_law : arena.{u}.Law actual := by
  intro Sector EX EY _ _ _ _ _ _ J M VX VY hVX hVY
  exact sector_pair M VX VY hVX hVY

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let M := Reg.Support.FiniteSectorSingleton.model (ULift.{u} Unit)
  let V : Matrix (ULift.{u} Unit × TargetLocal M.d)
      (SourceLocal (Coord := Fin 1) M.d) ℂ := fun _ _ => 1
  have index_eq : ∀ i j : SourceLocal (Coord := Fin 1) M.d, i = j := by
    change ∀ i j : (Σ _ : ULift.{u} Unit, Fin 1 × Fin 1), i = j
    intro ⟨s, a, b⟩ ⟨t, c, d⟩
    have hs : s = t := Subsingleton.elim _ _
    subst t
    have ha : a = c := Subsingleton.elim _ _
    have hb : b = d := Subsingleton.elim _ _
    subst c
    subst d
    rfl
  have hV : Vᴴ * V = 1 := by
    ext i j
    change (∑ _ : ULift.{u} Unit × TargetLocal M.d, star (1 : ℂ) * 1) =
      (1 : Matrix (SourceLocal (Coord := Fin 1) M.d) _ ℂ) i j
    rw [Matrix.one_apply, if_pos (index_eq i j)]
    simp only [star_one, mul_one]
    simp [M, Fintype.sum_sigma, Fintype.sum_prod_type]
  have hb := h M V V hV hV (⟨()⟩ : ULift.{u} Unit) (⟨()⟩ : ULift.{u} Unit)
  dsimp only [rejected, realize] at hb
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at hb
  norm_num [V, M, kernel, Matrix.diagonal_apply, Fintype.sum_sigma,
    Fintype.sum_prod_type] at hb


theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

#print axioms registration

register_information_theorem sector_pair in arena
  readout via (realize signature.{u} (fun _ _ x => star x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
    coordinates := #[]
    readouts := #[{path := #[ "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "arg", "arg",
        "body", "arg", "body", "fn", "arg" ], stateOperand := some #["arg"]}] })
  escape continues (open)


end Reg.D5.S3.Quantum.Entanglement.FiniteSectorPassivePair
