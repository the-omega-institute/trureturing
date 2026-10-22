/- GID: D5/S3/VertexAlgebra/BcGhostSuperGenerators
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostSuperGenerators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unchanged complex algebraic ghost Fock carrier, vacuum, b/c modes and original L(-1) translation. B_n=b(n-1) and C_n=c(n+2) are physical shifts, not replacements of the original operators. Concrete parity projectors split arbitrary finite mixed states; the four signed CAR cases are proved from the original operators. -/

import D5.S3.VertexAlgebra.BcGhostStressCurrent
import D5.S3.VertexAlgebra.BcGhostVacuum
import D5.S3.VertexAlgebra.SuperFieldProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostSuperGenerators

open BcGhostFockSupport BcGhostStressCurrent BcGhostVacuum
open FieldNormalProduct SuperFieldProducts
open scoped VertexOperator

noncomputable section

abbrev Carrier := Fock ℂ

def subsetParity (sites : Finset ℕ) : ℕ := sites.card % 2

def homogeneous (parity : ℕ) : Submodule ℂ Carrier where
  carrier := {vector | ∀ sites : Finset ℕ, subsetParity sites ≠ parity % 2 → vector sites = 0}
  zero_mem' := by intro sites mismatch; rfl
  add_mem' := by
    intro first second firstHomogeneous secondHomogeneous sites mismatch
    simp only [Finsupp.add_apply, firstHomogeneous sites mismatch,
      secondHomogeneous sites mismatch, add_zero]
  smul_mem' := by
    intro scalar vector vectorHomogeneous sites mismatch
    simp only [Finsupp.smul_apply, vectorHomogeneous sites mismatch, smul_zero]

def parityPart (parity : ℕ) : Module.End ℂ Carrier :=
  Finsupp.linearCombination ℂ (fun sites =>
    if subsetParity sites = parity % 2 then Finsupp.single sites 1 else 0)

theorem parityPart_coeff (parity : ℕ) (vector : Carrier) (sites : Finset ℕ) :
    parityPart parity vector sites =
      if subsetParity sites = parity % 2 then vector sites else 0 := by
  classical
  induction vector using Finsupp.induction_linear with
  | zero => simp
  | add first second firstLaw secondLaw =>
    simp only [map_add, Finsupp.add_apply, firstLaw, secondLaw]
    split <;> simp
  | single support scalar =>
    by_cases same : support = sites
    · subst support
      by_cases grade : subsetParity sites = parity % 2 <;>
        simp [parityPart, Finsupp.linearCombination_single, grade]
    · by_cases grade : subsetParity support = parity % 2 <;>
        simp [parityPart, Finsupp.linearCombination_single, grade,
          Finsupp.single_apply, same, Ne.symm same]

theorem parityPart_mem (parity : ℕ) (vector : Carrier) :
    parityPart parity vector ∈ homogeneous parity := by
  intro sites mismatch
  rw [parityPart_coeff, if_neg mismatch]

theorem parity_decomposition (vector : Carrier) :
    parityPart 0 vector + parityPart 1 vector = vector := by
  ext sites
  rw [Finsupp.add_apply, parityPart_coeff, parityPart_coeff]
  have bound : subsetParity sites < 2 := Nat.mod_lt _ (by decide)
  have alternative : subsetParity sites = 0 ∨ subsetParity sites = 1 := by omega
  rcases alternative with zeroGrade | oneGrade
  · simp [zeroGrade]
  · simp [oneGrade]

theorem parityPart_identity (parity : ℕ) (vector : Carrier) (member : vector ∈ homogeneous parity) :
    parityPart parity vector = vector := by
  ext sites
  rw [parityPart_coeff]
  split
  · rfl
  · rename_i mismatch
    exact (member sites mismatch).symm

theorem homogeneous_intersection_zero (vector : Carrier)
    (even : vector ∈ homogeneous 0) (odd : vector ∈ homogeneous 1) : vector = 0 := by
  ext sites
  have bound : subsetParity sites < 2 := Nat.mod_lt _ (by decide)
  by_cases zeroGrade : subsetParity sites = 0
  · exact odd sites (by simp [zeroGrade])
  · have oneGrade : subsetParity sites = 1 := by omega
    exact even sites (by simp [oneGrade])

theorem single_mem (parity : ℕ) (sites : Finset ℕ) (scalar : ℂ)
    (grade : subsetParity sites = parity % 2) :
    Finsupp.single sites scalar ∈ homogeneous parity := by
  classical
  intro support mismatch
  have different : sites ≠ support := by
    intro equality
    subst support
    exact mismatch grade
  simp [Finsupp.single_apply, different, Ne.symm different]

theorem support_parity (parity : ℕ) (vector : Carrier)
    (vectorHomogeneous : vector ∈ homogeneous parity)
    (sites : Finset ℕ) (member : sites ∈ vector.support) :
    subsetParity sites = parity % 2 := by
  by_contra mismatch
  exact (Finsupp.mem_support_iff.mp member) (vectorHomogeneous sites mismatch)

theorem create_mem (parity site : ℕ) (vector : Carrier)
    (vectorHomogeneous : vector ∈ homogeneous parity) :
    create site vector ∈ homogeneous (parity + 1) := by
  classical
  rw [create, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (homogeneous (parity + 1)).sum_mem
  intro sites member
  apply (homogeneous (parity + 1)).smul_mem
  by_cases occupied : site ∈ sites
  · simp [createBasis, occupied]
  · rw [createBasis, if_neg occupied]
    apply single_mem
    have grade := support_parity parity vector vectorHomogeneous sites member
    dsimp [subsetParity] at grade ⊢
    rw [Finset.card_insert_of_notMem occupied]
    omega

theorem annihilate_mem (parity site : ℕ) (vector : Carrier)
    (vectorHomogeneous : vector ∈ homogeneous parity) :
    annihilate site vector ∈ homogeneous (parity + 1) := by
  classical
  rw [annihilate, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (homogeneous (parity + 1)).sum_mem
  intro sites member
  apply (homogeneous (parity + 1)).smul_mem
  by_cases occupied : site ∈ sites
  · rw [annihilateBasis, if_pos occupied]
    apply single_mem
    have grade := support_parity parity vector vectorHomogeneous sites member
    have cardinal := Finset.card_erase_of_mem occupied
    have positive : 0 < sites.card := Finset.card_pos.mpr ⟨site, occupied⟩
    dsimp [subsetParity] at grade ⊢
    omega
  · simp [annihilateBasis, occupied]

def HomogeneousOperator (parity : ℕ) (operator : Module.End ℂ Carrier) : Prop :=
  ∀ inputParity : ℕ, ∀ vector ∈ homogeneous inputParity,
    operator vector ∈ homogeneous (parity + inputParity)

inductive Current where
  | b
  | c
  deriving DecidableEq

def currentMode (current : Current) (mode : ℤ) : Module.End ℂ Carrier :=
  match current with
  | .b => b (mode - 1)
  | .c => c (mode + 2)

def translation : Module.End ℂ Carrier := L (-1)

theorem currentMode_high (current : Current) (vector : Carrier) (mode : ℤ)
    (high : (((occupied vector).sup id : ℕ) : ℤ) + 1 < mode) :
    currentMode current mode vector = 0 := by
  have nonnegative : (0 : ℤ) ≤ (((occupied vector).sup id : ℕ) : ℤ) := Int.natCast_nonneg _
  cases current with
  | b =>
    have branch : ¬ mode - 1 ≤ -2 := by omega
    rw [currentMode, b, if_neg branch]
    apply annihilate_eq_zero_of_sup_lt
    have cast := Int.toNat_of_nonneg (show 0 ≤ mode - 1 + 1 by omega)
    omega
  | c =>
    have branch : ¬ mode + 2 ≤ 1 := by omega
    rw [currentMode, c, if_neg branch]
    apply annihilate_eq_zero_of_sup_lt
    have cast := Int.toNat_of_nonneg (show 0 ≤ mode + 2 - 2 by omega)
    omega

def currentField (current : Current) : VertexOperator ℂ Carrier :=
  VertexOperator.of_coeff (fun power => currentMode current (-power - 1)) (by
    intro vector
    refine ⟨-(((occupied vector).sup id : ℕ) : ℤ) - 2, ?_⟩
    intro power member
    by_contra below
    exact member (currentMode_high current vector (-power - 1) (by omega)))

theorem currentField_modes (current : Current) (mode : ℤ) :
    ((currentField current)[[mode]]) = currentMode current mode := by
  rw [currentField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-mode - 1) - 1 = mode by omega]

theorem currentMode_mem (current : Current) (mode : ℤ) :
    HomogeneousOperator 1 (currentMode current mode) := by
  intro parity vector vectorHomogeneous
  cases current with
  | b =>
    dsimp only [currentMode, b]
    split
    · simpa only [Nat.add_comm 1 parity] using create_mem parity _ vector vectorHomogeneous
    · simpa only [Nat.add_comm 1 parity] using annihilate_mem parity _ vector vectorHomogeneous
  | c =>
    dsimp only [currentMode, c]
    split
    · simpa only [Nat.add_comm 1 parity] using create_mem parity _ vector vectorHomogeneous
    · simpa only [Nat.add_comm 1 parity] using annihilate_mem parity _ vector vectorHomogeneous

theorem current_creative (current : Current) (mode : ℤ) (nonnegative : 0 ≤ mode) :
    ((currentField current)[[mode]]) (vacuum : Carrier) = 0 := by
  rw [currentField_modes]
  cases current with
  | b =>
    have branch : ¬ mode - 1 ≤ -2 := by omega
    simp [currentMode, b, branch, vacuum, annihilate,
      Finsupp.linearCombination_single, annihilateBasis]
  | c =>
    have branch : ¬ mode + 2 ≤ 1 := by omega
    simp [currentMode, c, branch, vacuum, annihilate,
      Finsupp.linearCombination_single, annihilateBasis]

theorem current_creation_b : ((currentField .b)[[-1]]) (vacuum : Carrier) =
    Finsupp.single {0} 1 := by
  rw [currentField_modes]
  simp [currentMode, b, vacuum, create, createBasis, sign, Finsupp.linearCombination_single]

theorem current_creation_c : ((currentField .c)[[-1]]) (vacuum : Carrier) =
    Finsupp.single {1} 1 := by
  rw [currentField_modes]
  simp [currentMode, c, vacuum, create, createBasis, sign, Finsupp.linearCombination_single]

theorem current_translation (current : Current) (mode : ℤ) :
    translation * ((currentField current)[[mode]]) -
      ((currentField current)[[mode]]) * translation =
        -(mode : ℂ) • ((currentField current)[[mode - 1]]) := by
  rw [currentField_modes, currentField_modes]
  cases current with
  | b =>
    have law := L_b_commutator (K := ℂ) (-1) (mode - 1)
    rw [show (-1 : ℤ) + (mode - 1) = mode - 1 - 1 by omega] at law
    change L (-1) * b (mode - 1) - b (mode - 1) * L (-1) =
      -(mode : ℂ) • b (mode - 1 - 1)
    rw [law]
    congr 1
    push_cast
    ring
  | c =>
    have law := L_c_commutator (K := ℂ) (-1) (mode + 2)
    rw [show (-1 : ℤ) + (mode + 2) = mode - 1 + 2 by omega] at law
    change L (-1) * c (mode + 2) - c (mode + 2) * L (-1) =
      -(mode : ℂ) • c (mode - 1 + 2)
    rw [law]
    congr 1
    push_cast
    ring

theorem translation_vacuum : translation (vacuum : Carrier) = 0 :=
  L_vacuum_annihilation (-1) le_rfl

theorem current_CAR (left right : Current) (first second : ℤ) :
    currentMode left first * currentMode right second +
      currentMode right second * currentMode left first =
        if left = right then 0 else if first + second = -1 then 1 else 0 := by
  cases left <;> cases right
  · simpa [currentMode] using b_b (K := ℂ) (first - 1) (second - 1)
  · have law := b_c (K := ℂ) (first - 1) (second + 2)
    simp only [show first - 1 + (second + 2) = 0 ↔ first + second = -1 by omega] at law
    simpa [currentMode] using law
  · have law := b_c (K := ℂ) (second - 1) (first + 2)
    simp only [show second - 1 + (first + 2) = 0 ↔ first + second = -1 by omega] at law
    simpa [currentMode, add_comm] using law
  · simpa [currentMode] using c_c (K := ℂ) (first + 2) (second + 2)

theorem current_superCommutator (left right : Current) (first second : ℤ) :
    superCommutator (koszul 1 1) (currentField left) (currentField right) first second =
      if left = right then 0 else if first + second = -1 then 1 else 0 := by
  simpa [superCommutator, koszul, currentField_modes] using current_CAR left right first second

theorem current_super_locality (left right : Current) :
    SuperLocal 1 1 (currentField left) (currentField right) := by
  refine ⟨1, ?_⟩
  funext first second
  change superCommutator (koszul 1 1) (currentField left) (currentField right) (first + 1) second -
    superCommutator (koszul 1 1) (currentField left) (currentField right) first (second + 1) = 0
  rw [current_superCommutator, current_superCommutator,
    show first + 1 + second = first + (second + 1) by omega, sub_self]

def kindAt (site : ℕ) : Current := if site % 2 = 0 then .b else .c

def siteField (site : ℕ) : VertexOperator ℂ Carrier :=
  dividedDerivative (site / 2) (currentField (kindAt site))

theorem site_creation_mode (site : ℕ) : ((siteField site)[[-1]]) = create site := by
  rw [siteField, derivative_modes, currentField_modes]
  have coefficient : integerBinomial (-(-1 : ℤ) - 1 + (site / 2 : ℕ)) (site / 2) = 1 := by
    rw [show -(-1 : ℤ) - 1 + (site / 2 : ℕ) = ((site / 2 : ℕ) : ℤ) by omega,
      integerBinomial, Ring.choose_natCast, Nat.choose_self]
    norm_num
  rw [coefficient, one_smul]
  by_cases even : site % 2 = 0
  · have branch : (-1 : ℤ) - (site / 2 : ℕ) - 1 ≤ -2 := by omega
    have index : 2 * (-((-1 : ℤ) - (site / 2 : ℕ) - 1) - 2).toNat = site := by omega
    simp only [kindAt, if_pos even, currentMode, b, if_pos branch, index]
  · have branch : (-1 : ℤ) - (site / 2 : ℕ) + 2 ≤ 1 := by omega
    have index : 2 * (1 - ((-1 : ℤ) - (site / 2 : ℕ) + 2)).toNat + 1 = site := by omega
    simp only [kindAt, if_neg even, currentMode, c, if_pos branch, index]

theorem site_creative (site : ℕ) (mode : ℤ) (nonnegative : 0 ≤ mode) :
    ((siteField site)[[mode]]) (vacuum : Carrier) = 0 :=
  derivative_creative (site / 2) (currentField (kindAt site)) vacuum
    (current_creative (kindAt site)) mode nonnegative

theorem site_translation (site : ℕ) (mode : ℤ) :
    translation * ((siteField site)[[mode]]) - ((siteField site)[[mode]]) * translation =
      -(mode : ℂ) • ((siteField site)[[mode - 1]]) :=
  derivative_translation translation (currentField (kindAt site))
    (current_translation (kindAt site)) (site / 2) mode

theorem site_mem (site : ℕ) (mode : ℤ) : HomogeneousOperator 1 (((siteField site)[[mode]])) := by
  intro parity vector vectorHomogeneous
  rw [siteField, derivative_modes, LinearMap.smul_apply, currentField_modes]
  exact (homogeneous (1 + parity)).smul_mem _
    (currentMode_mem (kindAt site) (mode - (site / 2 : ℕ)) parity vector vectorHomogeneous)

end
end D5.S3.VertexAlgebra.BcGhostSuperGenerators
