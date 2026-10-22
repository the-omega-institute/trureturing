import D5.S3.VertexAlgebra.SuperFieldProducts

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.FormalDeltaDistribution

open SuperFieldProducts

noncomputable section

@[ext] structure Exponent where
  zero : ℤ
  first : ℤ
  second : ℤ
  deriving DecidableEq

abbrev Distribution (Space : Type*) := Exponent → Space

def modeExponent (parameter first last : ℤ) : Exponent :=
  ⟨-parameter - 1, -first - 1, -last - 1⟩

def exponentAdd (left right : Exponent) : Exponent :=
  ⟨left.zero + right.zero, left.first + right.first, left.second + right.second⟩

inductive Region where
  | forward
  | reverse
  | iterate
  deriving DecidableEq

@[ext] structure Atom where
  power : ℤ
  offset : ℕ
  inner : ℤ
  outer : ℤ
  deriving DecidableEq

def deltaExponent (region : Region) (power : ℤ) (offset : ℕ) : Exponent :=
  match region with
  | .forward => ⟨-power - 1, power - offset, offset⟩
  | .reverse => ⟨-power - 1, offset, power - offset⟩
  | .iterate => ⟨offset, power - offset, -power - 1⟩

theorem epsilon_neg (power : ℤ) : epsilon (-power) = epsilon power := by
  simp [epsilon, neg_one_zpow_eq_ite]
  split <;> norm_num

def deltaWeight (region : Region) (power : ℤ) (offset : ℕ) : ℂ :=
  match region with
  | .forward => weight power offset
  | .reverse => epsilon (-power) * weight power offset
  | .iterate => weight power offset

theorem deltaExponent_injective (region : Region) : Function.Injective
    (fun index : ℤ × ℕ => deltaExponent region index.1 index.2) := by
  intro left right equality
  have zeroEquality := congrArg Exponent.zero equality
  have firstEquality := congrArg Exponent.first equality
  have secondEquality := congrArg Exponent.second equality
  cases region <;>
    simp only [deltaExponent] at zeroEquality firstEquality secondEquality <;>
    apply Prod.ext <;> omega

abbrev deltaFiber (region : Region) (exponent : Exponent) :=
  {index : ℤ × ℕ // deltaExponent region index.1 index.2 = exponent}

instance deltaFiber_subsingleton (region : Region) (exponent : Exponent) :
    Subsingleton (deltaFiber region exponent) := by
  constructor
  intro left right
  apply Subtype.ext
  apply deltaExponent_injective region
  exact left.property.trans right.property.symm

theorem delta_fiber_finite (region : Region) (exponent : Exponent) :
    Function.HasFiniteSupport (fun index : deltaFiber region exponent =>
      deltaWeight region index.val.1 index.val.2) := by
  exact Set.toFinite _

def deltaDistribution (region : Region) : Distribution ℂ :=
  fun exponent => ∑ index ∈ (delta_fiber_finite region exponent).toFinset,
    deltaWeight region index.val.1 index.val.2

theorem delta_coefficient (region : Region) (power : ℤ) (offset : ℕ) :
    deltaDistribution region (deltaExponent region power offset) =
      deltaWeight region power offset := by
  have finite := delta_fiber_finite region (deltaExponent region power offset)
  unfold deltaDistribution
  rw [← finsum_eq_sum_of_support_subset _ (fun index member => finite.mem_toFinset.mpr member)]
  rw [finsum_eq_single _ (⟨(power, offset), rfl⟩ : deltaFiber region
    (deltaExponent region power offset))]
  intro index distinct
  exact (distinct (Subsingleton.elim _ _)).elim

def fieldExponent (region : Region) (inner outer : ℤ) : Exponent :=
  match region with
  | .forward => ⟨0, -inner - 1, -outer - 1⟩
  | .reverse => ⟨0, -inner - 1, -outer - 1⟩
  | .iterate => ⟨-inner - 1, 0, -outer - 1⟩

def atomExponent (region : Region) (atom : Atom) : Exponent :=
  exponentAdd (deltaExponent region atom.power atom.offset)
    (fieldExponent region atom.inner atom.outer)

def resolvedAtom (region : Region) (exponent : Exponent) (offset : ℕ) : Atom :=
  match region with
  | .forward =>
      ⟨-exponent.zero - 1, offset,
        -exponent.zero - 1 - offset - exponent.first - 1,
        offset - exponent.second - 1⟩
  | .reverse =>
      ⟨-exponent.zero - 1, offset, offset - exponent.first - 1,
        -exponent.zero - 1 - offset - exponent.second - 1⟩
  | .iterate =>
      ⟨exponent.first + offset, offset, offset - exponent.zero - 1,
        -(exponent.first + offset) - exponent.second - 2⟩

theorem resolved_exponent (region : Region) (exponent : Exponent) (offset : ℕ) :
    atomExponent region (resolvedAtom region exponent offset) = exponent := by
  cases region <;> apply Exponent.ext <;>
    simp [atomExponent, exponentAdd, deltaExponent, fieldExponent, resolvedAtom] <;> omega

theorem exponent_fiber_unique (region : Region) (exponent : Exponent) (atom : Atom)
    (membership : atomExponent region atom = exponent) :
    resolvedAtom region exponent atom.offset = atom := by
  have zeroEquality := congrArg Exponent.zero membership
  have firstEquality := congrArg Exponent.first membership
  have secondEquality := congrArg Exponent.second membership
  cases region <;>
    simp only [atomExponent, exponentAdd, deltaExponent, fieldExponent] at zeroEquality firstEquality secondEquality <;>
    apply Atom.ext <;> simp [resolvedAtom] <;> omega

def coefficientFiber (region : Region) (exponent : Exponent) :=
  {atom : Atom // atomExponent region atom = exponent}

def fiberEquiv (region : Region) (exponent : Exponent) :
    ℕ ≃ coefficientFiber region exponent where
  toFun offset := ⟨resolvedAtom region exponent offset, resolved_exponent region exponent offset⟩
  invFun atom := atom.val.offset
  left_inv offset := by cases region <;> rfl
  right_inv atom := by
    apply Subtype.ext
    exact exponent_fiber_unique region exponent atom.val atom.property

variable {Space : Type*} [AddCommGroup Space]

def coefficientAction (region : Region) (amplitude : Atom → Space) : Distribution Space :=
  fun exponent => ∑ᶠ atom : coefficientFiber region exponent, amplitude atom.val

theorem coefficient_support (region : Region) (amplitude : Atom → Space) (exponent : Exponent)
    (finite : Function.HasFiniteSupport (fun offset => amplitude (resolvedAtom region exponent offset))) :
    Function.HasFiniteSupport (fun atom : coefficientFiber region exponent => amplitude atom.val) := by
  have transported : Function.HasFiniteSupport (fun atom : coefficientFiber region exponent =>
      amplitude (resolvedAtom region exponent atom.val.offset)) :=
    finite.fun_comp_of_injective
      (g := fun atom : coefficientFiber region exponent => atom.val.offset)
      (fiberEquiv region exponent).symm.injective
  have functions : (fun atom : coefficientFiber region exponent =>
      amplitude (resolvedAtom region exponent atom.val.offset)) =
        (fun atom : coefficientFiber region exponent => amplitude atom.val) := by
    funext atom
    rw [exponent_fiber_unique region exponent atom.val atom.property]
  rw [functions] at transported
  exact transported

theorem coefficient_extract (region : Region) (amplitude : Atom → Space) (exponent : Exponent)
    (finite : Function.HasFiniteSupport (fun offset => amplitude (resolvedAtom region exponent offset))) :
    coefficientAction region amplitude exponent =
      ∑ᶠ offset : ℕ, amplitude (resolvedAtom region exponent offset) := by
  exact (finsum_comp_equiv (fiberEquiv region exponent)).symm

theorem resolved_forward (parameter first last : ℤ) (offset : ℕ) :
    resolvedAtom .forward (modeExponent parameter first last) offset =
      ⟨parameter, offset, first + parameter - offset, last + offset⟩ := by
  apply Atom.ext <;> simp [resolvedAtom, modeExponent] <;> omega

theorem resolved_reverse (parameter first last : ℤ) (offset : ℕ) :
    resolvedAtom .reverse (modeExponent parameter first last) offset =
      ⟨parameter, offset, first + offset, last + parameter - offset⟩ := by
  apply Atom.ext <;> simp [resolvedAtom, modeExponent] <;> omega

theorem resolved_iterate (parameter first last : ℤ) (offset : ℕ) :
    resolvedAtom .iterate (modeExponent parameter first last) offset =
      ⟨(offset : ℤ) - first - 1, offset, parameter + offset, first + last - offset⟩ := by
  apply Atom.ext <;> simp [resolvedAtom, modeExponent] <;> omega

theorem signed_negative_binomial (first : ℤ) (offset : ℕ) :
    weight ((offset : ℤ) - first - 1) offset = integerBinomial first offset := by
  have conversion := Ring.choose_neg (first + 1 - offset) offset
  have argument : -(first + 1 - (offset : ℤ)) = (offset : ℤ) - first - 1 := by omega
  have restored : first + 1 - (offset : ℤ) + offset - 1 = first := by omega
  rw [argument, restored] at conversion
  simp only [Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul] at conversion
  unfold weight integerBinomial
  rw [conversion]
  push_cast
  have squared : (-1 : ℂ) ^ offset * (-1 : ℂ) ^ offset = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, squared, one_mul]

theorem modeExponent_surjective : Function.Surjective
    (fun indices : ℤ × ℤ × ℤ => modeExponent indices.1 indices.2.1 indices.2.2) := by
  intro exponent
  refine ⟨(-exponent.zero - 1, -exponent.first - 1, -exponent.second - 1), ?_⟩
  apply Exponent.ext <;> simp [modeExponent]

theorem distribution_eq_iff_modes (left right : Distribution Space) :
    left = right ↔ ∀ parameter first last : ℤ,
      left (modeExponent parameter first last) = right (modeExponent parameter first last) := by
  constructor
  · intro equality parameter first last
    rw [equality]
  · intro equality
    funext exponent
    obtain ⟨indices, rfl⟩ := modeExponent_surjective exponent
    exact equality indices.1 indices.2.1 indices.2.2

end

end D5.S3.VertexAlgebra.FormalDeltaDistribution
