import D5.S3.Estimation.TimeArrow.ParityAffinityPerron
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.ParityAffinityPerron
open _root_.D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
open LeanInformationAudit
open Lean Elab Command
open Finset

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.ParityAffinityPerron

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.ParityAffinityPerron
  let owner := `D5.S3.Estimation.TimeArrow.ParityAffinityPerron
  let rootRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `rootArena
    theoremName := owner ++ `affinityEquation_unique_root
    statementIdentity :=
      "sha256:e9d5c8460e6ee93739e4706342cbb5d4d42b19295094568633fdd86cf4ddfdde"
    registrationModuleName := root }
  let perronRow : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `perronArena
    theoremName := owner ++ `affinity_perronVector
    statementIdentity :=
      "sha256:91e316660e659b414bda7c2d6c99979b0b6decf8ec8d9d50dfa44c5fc1350e10"
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[rootRow, perronRow], source := #[rootRow, perronRow],
    companionPrefix := some root }

@[reducible] def rootSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature :=
  realize rootSignature
    (fun role p z => match role with
      | false => (z ^ 2 * (1 + z) ^ 2 : ℝ)
      | true => ((z + p.1 ^ 2) * (z + p.2 ^ 2) : ℝ))
    (fun e => nomatch e)

def rootLeftRejected : Realization rootSignature :=
  realize rootSignature
    (fun role p z => match role with
      | false => (0 : ℝ)
      | true => rootActual.readout true p z)
    (fun e => nomatch e)

def rootRightRejected : Realization rootSignature :=
  realize rootSignature
    (fun role p z => match role with
      | false => rootActual.readout false p z
      | true => (0 : ℝ))
    (fun e => nomatch e)

def rootArena : Arena where
  signature := rootSignature
  Law R := ∀ {etaPlus etaMinus : ℝ},
    0 < etaPlus → etaPlus ≤ 1 → 0 < etaMinus → etaMinus ≤ 1 →
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧
      R.readout false ⟨etaPlus, etaMinus⟩ z =
        R.readout true ⟨etaPlus, etaMinus⟩ z ∧
      ∀ w : ℝ, 0 < w →
        R.readout false ⟨etaPlus, etaMinus⟩ w =
          R.readout true ⟨etaPlus, etaMinus⟩ w → w = z

theorem rootActual_law : rootArena.Law rootActual := by
  intro etaPlus etaMinus hp0 hp1 hm0 hm1
  exact affinityEquation_unique_root hp0 hp1 hm0 hm1

theorem rootLeftRejected_law : ¬ rootArena.Law rootLeftRejected := by
  intro h
  obtain ⟨z, hz0, _hz1, hzroot, _hunique⟩ :=
    h (etaPlus := 1) (etaMinus := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (0 : ℝ) = (z + 1 ^ 2) * (z + 1 ^ 2) at hzroot
  nlinarith [sq_nonneg (z + 1)]

theorem rootRightRejected_law : ¬ rootArena.Law rootRightRejected := by
  intro h
  obtain ⟨z, hz0, _hz1, hzroot, _hunique⟩ :=
    h (etaPlus := 1) (etaMinus := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change z ^ 2 * (1 + z) ^ 2 = (0 : ℝ) at hzroot
  nlinarith [sq_pos_of_pos hz0, sq_pos_of_pos (by linarith : 0 < 1 + z)]

theorem rootSensitivity : Sensitivity rootArena rootActual := by
  constructor
  · intro i
    cases i
    · refine ⟨rootLeftRejected, ?_, rfl, rootLeftRejected_law⟩
      intro j hji
      cases j
      · exact (hji rfl).elim
      · rfl
    · refine ⟨rootRightRejected, ?_, rfl, rootRightRejected_law⟩
      intro j hji
      cases j
      · rfl
      · exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem rootDependence : ObservationalDependence rootSignature rootActual := by
  intro i
  cases i
  · refine ⟨⟨(1 : ℝ), (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    norm_num [rootActual, realize]
  · refine ⟨⟨(1 : ℝ), (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    norm_num [rootActual, realize]

def rootRegistration : Registration rootArena (rootArena.Law rootActual) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨rootActual_law, rootLeftRejected, rootLeftRejected_law⟩
  sensitivity := rootSensitivity
  dependence := rootDependence

@[reducible] def perronSignature : Signature where
  Params := Σ d : ℕ, Σ _ : (Fin d → ℤˣ) → ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State p := Fin p.1 → ℤˣ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def perronActual : Realization perronSignature :=
  realize perronSignature
    (fun role p x =>
      let b := p.2.1
      let etaPlus := p.2.2.1
      let etaMinus := p.2.2.2.1
      let z := p.2.2.2.2
      match role with
      | false => (affinityPerronVector b etaPlus etaMinus z x : ℝ)
      | true =>
          (∑ y, affinityKernel b x y * affinityPerronVector b etaPlus etaMinus z y : ℝ))
    (fun e => nomatch e)

def perronVectorRejected : Realization perronSignature :=
  realize perronSignature
    (fun role p x => match role with
      | false => (0 : ℝ)
      | true => perronActual.readout true p x)
    (fun e => nomatch e)

def perronActionRejected : Realization perronSignature :=
  realize perronSignature
    (fun role p x => match role with
      | false => perronActual.readout false p x
      | true => (0 : ℝ))
    (fun e => nomatch e)

def perronArena : Arena where
  signature := perronSignature
  Law R := ∀ {d : ℕ} (_hd : 1 ≤ d) (b : (Fin d → ℤˣ) → ℝ)
    (_hb : ∀ x, |b x| < 1)
    (_hzeroPlus : ∑ x ∈ parityClass 1, b x = 0)
    (_hzeroMinus : ∑ x ∈ parityClass (-1), b x = 0)
    (etaPlus etaMinus z : ℝ)
    (_hetaPlus : etaPlus = classAffinity b 1)
    (_hetaMinus : etaMinus = classAffinity b (-1))
    (_hetaPlus0 : 0 < etaPlus) (_hetaPlus1 : etaPlus ≤ 1)
    (_hetaMinus0 : 0 < etaMinus) (_hetaMinus1 : etaMinus ≤ 1)
    (_hz0 : 0 < z)
    (_hzroot : z ^ 2 * (1 + z) ^ 2 =
      (z + etaPlus ^ 2) * (z + etaMinus ^ 2)),
    (∀ x, 0 < R.readout false ⟨d, b, etaPlus, etaMinus, z⟩ x) ∧
      ∀ x, R.readout true ⟨d, b, etaPlus, etaMinus, z⟩ x =
        ((1 + z) / 2) * R.readout false ⟨d, b, etaPlus, etaMinus, z⟩ x

def plusVertex : Fin 1 → ℤˣ := fun _ => 1

def minusVertex : Fin 1 → ℤˣ := fun _ => -1

theorem parityClass_one_zeroProfile :
    classAffinity (d := 1) (fun _ => 0) 1 = 1 := by
  have hClass : parityClass (d := 1) 1 = {plusVertex} := by
    ext x
    constructor
    · intro hx
      have hp : parity x = 1 := by simpa [parityClass] using hx
      have hx0 : x 0 = 1 := by
        rcases Int.units_eq_one_or (x 0) with h | h
        · exact h
        · norm_num [parity, h] at hp
      have : x = plusVertex := by
        funext i
        fin_cases i
        exact hx0
      simp [this]
    · intro hx
      have : x = plusVertex := by simpa using hx
      subst x
      simp [parityClass, plusVertex, parity]
  rw [classAffinity, hClass]
  norm_num

theorem parityClass_neg_one_zeroProfile :
    classAffinity (d := 1) (fun _ => 0) (-1) = 1 := by
  have hClass : parityClass (d := 1) (-1) = {minusVertex} := by
    ext x
    constructor
    · intro hx
      have hp : parity x = -1 := by simpa [parityClass] using hx
      have hx0 : x 0 = -1 := by
        rcases Int.units_eq_one_or (x 0) with h | h
        · norm_num [parity, h] at hp
        · exact h
      have : x = minusVertex := by
        funext i
        fin_cases i
        exact hx0
      simp [this]
    · intro hx
      have : x = minusVertex := by simpa using hx
      subst x
      simp [parityClass, minusVertex, parity]
  rw [classAffinity, hClass]
  norm_num

theorem perronActual_law : perronArena.Law perronActual := by
  intro d hd b hb hzeroPlus hzeroMinus etaPlus etaMinus z hetaPlus hetaMinus
    hetaPlus0 hetaPlus1 hetaMinus0 hetaMinus1 hz0 hzroot
  exact affinity_perronVector hd b hb hzeroPlus hzeroMinus etaPlus etaMinus z
    hetaPlus hetaMinus hetaPlus0 hetaPlus1 hetaMinus0 hetaMinus1 hz0 hzroot

theorem perronVectorRejected_law : ¬ perronArena.Law perronVectorRejected := by
  intro h
  have hfalse := h (d := 1) (by omega) (fun _ => 0) (by intro x; norm_num)
    (by simp) (by simp) 1 1 1 parityClass_one_zeroProfile.symm
    parityClass_neg_one_zeroProfile.symm (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := hfalse.1 plusVertex
  norm_num [perronVectorRejected, realize] at this

theorem perronActionRejected_law : ¬ perronArena.Law perronActionRejected := by
  intro h
  have hfalse := h (d := 1) (by omega) (fun _ => 0) (by intro x; norm_num)
    (by simp) (by simp) 1 1 1 parityClass_one_zeroProfile.symm
    parityClass_neg_one_zeroProfile.symm (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have := hfalse.2 plusVertex
  norm_num [perronActionRejected, perronActual, realize, affinityPerronVector,
    classU, classV, plusVertex, parity] at this

theorem perronSensitivity : Sensitivity perronArena perronActual := by
  constructor
  · intro i
    cases i
    · refine ⟨perronVectorRejected, ?_, rfl, perronVectorRejected_law⟩
      intro j hji
      cases j
      · exact (hji rfl).elim
      · rfl
    · refine ⟨perronActionRejected, ?_, rfl, perronActionRejected_law⟩
      intro j hji
      cases j
      · rfl
      · exact (hji rfl).elim
  · intro i
    exact nomatch i

def edgeProfile (x : Fin 1 → ℤˣ) : ℝ := if parity x = 1 then 1 else 0

theorem sum_fin_one_units (f : (Fin 1 → ℤˣ) → ℝ) :
    ∑ x, f x = f plusVertex + f minusVertex := by
  have huniv : (Finset.univ : Finset (Fin 1 → ℤˣ)) = {plusVertex, minusVertex} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases Int.units_eq_one_or (x 0) with h | h
    · left
      funext i
      fin_cases i
      exact h
    · right
      funext i
      fin_cases i
      exact h
  rw [huniv]
  have hne : plusVertex ≠ minusVertex := by
    intro h
    have := congrFun h 0
    norm_num [plusVertex, minusVertex] at this
  simp [hne]

theorem perronDependence : ObservationalDependence perronSignature perronActual := by
  intro i
  cases i
  · refine ⟨⟨1, fun _ => 0, 0, 0, 1⟩, plusVertex, minusVertex, ?_⟩
    norm_num [perronActual, realize, affinityPerronVector, classU, classV,
      plusVertex, minusVertex, parity]
  · refine ⟨⟨1, fun x => if parity x = 1 then 1 else 0, 0, 0, 1⟩,
      plusVertex, minusVertex, ?_⟩
    change (∑ y, affinityKernel edgeProfile plusVertex y *
        affinityPerronVector edgeProfile 0 0 1 y) ≠
      ∑ y, affinityKernel edgeProfile minusVertex y *
        affinityPerronVector edgeProfile 0 0 1 y
    rw [sum_fin_one_units, sum_fin_one_units]
    norm_num [affinityKernel, parityKernel, affinityPerronVector, classU, classV,
      edgeProfile, plusVertex, minusVertex, parity]

def perronRegistration : Registration perronArena (perronArena.Law perronActual) where
  actual := perronActual
  bridge := Iff.rfl
  variation := ⟨perronActual_law, perronVectorRejected, perronVectorRejected_law⟩
  sensitivity := perronSensitivity
  dependence := perronDependence

register_information_theorem affinityEquation_unique_root in rootArena
  readout via (realize rootSignature
    (fun role p z => match role with
      | false => (z ^ 2 * (1 + z) ^ 2 : ℝ)
      | true => ((z + p.1 ^ 2) * (z + p.2 ^ 2) : ℝ))
    (fun e => nomatch e))
  realizes rootRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityAffinityPerron
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "arg", "body",
          "arg", "arg", "fn", "arg", "arg"], stateBinder := 6 },
      { path := #["body", "body", "body", "body", "body", "body", "arg", "body",
          "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 6 }] })
  escape continues (open)

register_information_theorem affinity_perronVector in perronArena
  readout via (realize perronSignature
    (fun role p x =>
      let b := p.2.1
      let etaPlus := p.2.2.1
      let etaMinus := p.2.2.2.1
      let z := p.2.2.2.2
      match role with
      | false => (affinityPerronVector b etaPlus etaMinus z x : ℝ)
      | true =>
          (∑ y, affinityKernel b x y * affinityPerronVector b etaPlus etaMinus z y : ℝ))
    (fun e => nomatch e))
  realizes perronRegistration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.ParityAffinityPerron
    coordinates := #[0, 2, 6, 7, 8]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "body", "fn", "arg"], stateBinder := 17 },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "body", "arg"], stateBinder := 17 }] })
  escape continues (open)

#print axioms rootLeftRejected_law
#print axioms rootRightRejected_law
#print axioms rootSensitivity
#print axioms rootDependence
#print axioms perronVectorRejected_law
#print axioms perronActionRejected_law
#print axioms perronSensitivity
#print axioms perronDependence

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Estimation.TimeArrow.ParityAffinityPerron
