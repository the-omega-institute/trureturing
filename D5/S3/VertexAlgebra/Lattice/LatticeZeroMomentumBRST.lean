/- GID: D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST
   mirror-E: none(waiver:algebraic-original-zero-momentum-shell)
   anchors: []
   utility: none
   digest: Exhaustive original zero-momentum relative shell and actual BRST/number actions. -/

/- The carrier, total charge and unshifted shell are the original frozen suppliers.
The two inverse-Gram equations are explicit; no rank, signature or nilpotence
assumption is used. Repository suppliers retain their authorship.
Basis reindexing and coordinate equivalences reuse Mathlib (Apache 2.0).
This prerequisite asserts neither cohomology nor positivity. -/

import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree

/-! Exhaustion and actual operator actions on the original zero-momentum relative shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeZeroMomentumBRST

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeMatterGhostCoupling LatticeRelativeMassShell
open D5.S3.Quantum.Fermionic
open CountableOccupationFock
open BcGhostFock (b c)
open LatticeMatterGhostDegree (tensorNumber)
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section

/- Literal ghost levels. Only sites 1 and 5 can occur below relative level two. -/

private theorem small_positive_site (j : ℕ) (h1 : j ≠ 1) (h3 : j ≠ 3)
    (hE : BcGhostRelativeEnergy.siteEnergy j ≤ 1) : j = 5 := by
  by_cases he : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    rw [hj, BcGhostRelativeEnergy.siteEnergy_even] at hE
    omega
  · have hj : j = 2 * (j / 2) + 1 := by omega
    rw [hj, BcGhostRelativeEnergy.siteEnergy_odd] at hE
    omega

private theorem low_occupation_subset (S : Finset ℕ) (h3 : 3 ∉ S)
    (hE : BcGhostRelativeEnergy.relativeEnergy S ≤ 1) : S ⊆ {1,5} := by
  classical
  intro j hj
  by_cases hj1 : j = 1
  · simp [hj1]
  · have hj3 : j ≠ 3 := by rintro rfl; exact h3 hj
    have hjerase : j ∈ (S.erase 1).erase 3 := by simp [hj, hj1, hj3]
    have hsum : BcGhostRelativeEnergy.siteEnergy j ≤ ∑ k ∈ (S.erase 1).erase 3,
      BcGhostRelativeEnergy.siteEnergy k := by
      apply Finset.single_le_sum _ hjerase
      intro k hk
      have hk3 := (Finset.mem_erase.mp hk).1
      have hk1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      exact (BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three hk1 hk3).le
    have hsplit := BcGhostRelativeEnergy.relativeEnergy_split S
    have hbase : (0 : ℤ) ≤ (if 1 ∉ S then 1 else 0) := by
      split_ifs <;> norm_num
    have hsite : BcGhostRelativeEnergy.siteEnergy j ≤ 1 := by omega
    simp [small_positive_site j hj1 hj3 hsite]

private theorem subset_pair_cases (S : Finset ℕ) (hS : S ⊆ {1,5}) :
    S = ∅ ∨ S = {1} ∨ S = {5} ∨ S = {1,5} := by
  classical
  by_cases h1 : 1 ∈ S <;> by_cases h5 : 5 ∈ S
  · right; right; right
    ext j
    constructor
    · exact fun hj => hS hj
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> assumption
  · right; left
    ext j
    have hj := fun h : j ∈ S => hS h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
    constructor
    · intro h
      rcases hj h with h | h
      · exact h
      · subst j; exact (h5 h).elim
    · rintro rfl; exact h1
  · right; right; left
    ext j
    have hj := fun h : j ∈ S => hS h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
    constructor
    · intro h
      rcases hj h with h' | h'
      · subst j; exact (h1 h).elim
      · exact h'
    · rintro rfl; exact h5
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have := hS hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl <;> contradiction

@[simp] theorem relativeEnergy_empty : BcGhostRelativeEnergy.relativeEnergy ∅ = 1 := by
  simp [BcGhostRelativeEnergy.relativeEnergy, BcGhostRelativeEnergy.energy]

@[simp] theorem relativeEnergy_down : BcGhostRelativeEnergy.relativeEnergy {1} = 0 := by
  norm_num [BcGhostRelativeEnergy.relativeEnergy, BcGhostRelativeEnergy.energy,
    BcGhostRelativeEnergy.siteEnergy_one]

@[simp] theorem relativeEnergy_top : BcGhostRelativeEnergy.relativeEnergy {1,5} = 1 := by
  norm_num [BcGhostRelativeEnergy.relativeEnergy, BcGhostRelativeEnergy.energy,
    BcGhostRelativeEnergy.siteEnergy, BcGhostCharge.siteMode, BcGhostCharge.siteSign]

/-- Exhaustive on the literal b-zero kernel, by positive site energies. -/
theorem ghost_level_zero_iff (S : Finset ℕ) (h3 : 3 ∉ S) :
    BcGhostRelativeEnergy.relativeEnergy S = 0 ↔ S = {1} := by
  constructor
  · intro hE
    have hv : BcGhostRelativeEnergy.RelativeLevel 0 (ket S) := by
      apply (BcGhostRelativeEnergy.relative_level_coeff_iff 0 (ket S)).mpr
      constructor
      · intro T hT
        by_cases hTS : T = S
        · subst T
          exact (h3 hT).elim
        · simp [ket, hTS]
      · intro T hT
        by_cases hTS : T = S
        · simpa [hTS] using hE
        · simp [ket, hTS] at hT
    obtain ⟨a, ha⟩ := (BcGhostRelativeEnergy.relative_ground_line (ket S)).mp
      ⟨hv.1, by simpa using hv.2⟩
    by_contra hne
    have hc := congrArg (fun w : Fock => w S) ha
    simp [ket, hne] at hc
  · rintro rfl; exact relativeEnergy_down

/-- At relative level one the actual c(-1) site is 5. -/
theorem ghost_level_one_iff (S : Finset ℕ) (h3 : 3 ∉ S) :
    BcGhostRelativeEnergy.relativeEnergy S = 1 ↔ S = ∅ ∨ S = {1,5} := by
  constructor
  · intro hE
    rcases subset_pair_cases S (low_occupation_subset S h3 hE.le) with
      rfl | rfl | rfl | rfl <;>
      norm_num [BcGhostRelativeEnergy.relativeEnergy, BcGhostRelativeEnergy.energy,
        BcGhostRelativeEnergy.siteEnergy,
      BcGhostCharge.siteMode, BcGhostCharge.siteSign] at hE <;> simp_all
  · rintro (rfl | rfl) <;> simp

/- Actual oscillator weight one is precisely one original frequency-zero variable. -/

theorem oscillatorEnergy_one_iff (D : LatticeData) (d : Exponent D) :
    oscillatorEnergy d = 1 ↔ ∃ i : Fin D.rank, d = Finsupp.single (i,0) 1 := by
  classical
  constructor
  · intro hd
    have hex : ∃ x : Index D, d x ≠ 0 := by
      by_contra h
      push Not at h
      have hz : d = 0 := Finsupp.ext h
      simp [hz, oscillatorEnergy] at hd
    obtain ⟨⟨i,k⟩, hik⟩ := hex
    have hk := Finsupp.le_weight_of_ne_zero' (fun x : Index D => x.2 + 1) hik
    change k + 1 ≤ oscillatorEnergy d at hk
    have hk0 : k = 0 := by omega
    subst k
    have hi := Finsupp.le_weight (fun x : Index D => x.2 + 1)
      (s := (i,0)) (by omega) d
    change d (i,0) ≤ oscillatorEnergy d at hi
    have hi1 : d (i,0) = 1 := by omega
    have hdecomp : d = Finsupp.single (i,0) 1 + d.erase (i,0) := by
      ext x
      by_cases hx : x = (i,0)
      · subst x; simp [hi1]
      · simp [hx]
    have hw := congrArg oscillatorEnergy hdecomp
    change oscillatorEnergy d =
      Finsupp.weight (fun x : Index D => x.2 + 1)
        (Finsupp.single (i,0) 1 + d.erase (i,0)) at hw
    rw [map_add, Finsupp.weight_single] at hw
    have he : oscillatorEnergy (d.erase (i,0)) = 0 := by
      change oscillatorEnergy d = 1 + oscillatorEnergy (d.erase (i,0)) at hw
      omega
    have he0 := (oscillatorEnergy_eq_zero_iff D _).mp he
    exact ⟨i, by simpa [he0] using hdecomp⟩
  · rintro ⟨i,rfl⟩
    simp [oscillatorEnergy, Finsupp.weight_single]

abbrev ZeroIndex (D : LatticeData) := Unit ⊕ (Fin D.rank ⊕ Unit)

def zeroLabel (D : LatticeData) : ZeroIndex D → TensorLabel D
  | .inl _ => ((0,0),∅)
  | .inr (.inl i) => ((0,Finsupp.single (i,0) 1),{1})
  | .inr (.inr _) => ((0,0),{1,5})

/-- Exact labels of the original zero-momentum mass shell. -/
theorem allowed_zero_iff (D : LatticeData) (l : TensorLabel D) :
    l ∈ allowedLabels D 0 ↔ ∃ k : ZeroIndex D, l = zeroLabel D k := by
  classical
  constructor
  · rcases l with ⟨⟨a,d⟩,S⟩
    rintro ⟨ha,h3,hE⟩
    dsimp at ha h3 hE
    subst a
    simp only [chargeEnergy_zero, sub_zero] at hE
    have hnonneg := BcGhostRelativeEnergy.relativeEnergy_nonneg S
    have hdle : oscillatorEnergy d ≤ 1 := by omega
    have hdcases : oscillatorEnergy d = 0 ∨ oscillatorEnergy d = 1 := by omega
    rcases hdcases with hd | hd
    · have hd0 := (oscillatorEnergy_eq_zero_iff D d).mp hd
      have hg : BcGhostRelativeEnergy.relativeEnergy S = 1 := by omega
      rcases (ghost_level_one_iff S h3).mp hg with rfl | rfl
      · exact ⟨.inl (), by simp [zeroLabel, hd0]⟩
      · exact ⟨.inr (.inr ()), by simp [zeroLabel, hd0]⟩
    · obtain ⟨i,rfl⟩ := (oscillatorEnergy_one_iff D d).mp hd
      have hg : BcGhostRelativeEnergy.relativeEnergy S = 0 := by omega
      have hS := (ghost_level_zero_iff S h3).mp hg
      exact ⟨.inr (.inl i), by simp [zeroLabel, hS]⟩
  · rintro ⟨k,rfl⟩
    rcases k with u | (i | u)
    all_goals simp [zeroLabel, allowedLabels, oscillatorEnergy,
      Finsupp.weight_single, relativeEnergy_empty, relativeEnergy_down,
      relativeEnergy_top]

private theorem zeroLabel_injective (D : LatticeData) : Function.Injective (zeroLabel D) := by
  classical
  intro k l h
  rcases k with ⟨⟩ | (i | ⟨⟩) <;> rcases l with ⟨⟩ | (j | ⟨⟩)
  all_goals try rfl
  all_goals try
    have hS := congrArg (fun t : TensorLabel D => (1 ∈ t.2, 5 ∈ t.2)) h
    norm_num [zeroLabel] at hS
  have he : Finsupp.single (i,0) (1 : ℕ) = Finsupp.single (j,0) 1 :=
    congrArg (fun t : TensorLabel D => t.1.2) h
  have hc := congrArg (fun d : Exponent D => d (i,0)) he
  by_cases hij : i = j
  · simp [hij]
  · simp [hij] at hc

/-- Derived equivalence, including its genuine surjectivity proof. -/
def zeroIndexEquiv (D : LatticeData) : ZeroIndex D ≃ ShellIndex D 0 :=
  Equiv.ofBijective
    (fun k => ⟨zeroLabel D k, (allowed_zero_iff D _).mpr ⟨k,rfl⟩⟩)
    ⟨by
      intro k l h
      exact zeroLabel_injective D (congrArg Subtype.val h), by
      intro l
      obtain ⟨k,hk⟩ := (allowed_zero_iff D l.1).mp l.2
      exact ⟨k, Subtype.ext hk.symm⟩⟩

/-- The original zero-charge polynomial vacuum. -/
abbrev ground (D : LatticeData) : Carrier D := LatticeAllStateField.vacuum D

/-- This frequency-zero polynomial variable has oscillator energy ONE. -/
abbrev current (D : LatticeData) (i : Fin D.rank) : Carrier D :=
  LatticeActualConformalState.currentState D i

def zeroVector (D : LatticeData) : ZeroIndex D → State D
  | .inl _ => ground D ⊗ₜ[ℂ] ket ∅
  | .inr (.inl i) => current D i ⊗ₜ[ℂ] ket {1}
  | .inr (.inr _) => ground D ⊗ₜ[ℂ] ket {1,5}

private theorem zeroVector_eq_tensorBasis (D : LatticeData) (k : ZeroIndex D) :
    zeroVector D k = tensorBasis D (zeroLabel D k) := by
  rcases k with u | (i | u)
  all_goals simp [zeroVector, zeroLabel, tensorBasis_apply, ground, current,
    LatticeAllStateField.vacuum, LatticeActualConformalState.currentState, MvPolynomial.X]

section Shell

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- An exact basis of the literal original kernel intersection. -/
def zeroBasis : Module.Basis (ZeroIndex D) ℂ (relativeMassShell D H 0) :=
  (shellBasis D H hHG hGH 0).reindex (zeroIndexEquiv D).symm

theorem zeroBasis_coe (k : ZeroIndex D) :
    (zeroBasis D H hHG hGH k : State D) = zeroVector D k := by
  rw [zeroBasis, Module.Basis.reindex_apply, shellBasis_coe]
  exact (zeroVector_eq_tensorBasis D k).symm

abbrev Coordinates := ℂ × ((Fin D.rank → ℂ) × ℂ)

private def splitCoordinates : (ZeroIndex D → ℂ) ≃ₗ[ℂ] Coordinates D where
  toFun f := (f (.inl ()), (fun i => f (.inr (.inl i)), f (.inr (.inr ()))))
  invFun z := fun k => match k with
    | .inl _ => z.1
    | .inr (.inl i) => z.2.1 i
    | .inr (.inr _) => z.2.2
  left_inv f := by
    funext k
    rcases k with ⟨⟩ | (i | ⟨⟩) <;> rfl
  right_inv z := by rcases z with ⟨A,v,C⟩; rfl
  map_add' f g := rfl
  map_smul' a f := rfl

/-- Coefficients of the actual original shell, with inverse supplied by its basis. -/
def shellEquiv : relativeMassShell D H 0 ≃ₗ[ℂ] Coordinates D :=
  (zeroBasis D H hHG hGH).equivFun.trans (splitCoordinates D)

/-- Psi lands in the original shell; no replacement carrier is introduced. -/
def Psi : Coordinates D →ₗ[ℂ] State D :=
  (relativeMassShell D H 0).subtype.comp (shellEquiv D H hHG hGH).symm.toLinearMap

theorem Psi_formula (z : Coordinates D) :
    Psi D H hHG hGH z = z.1 • (ground D ⊗ₜ[ℂ] ket ∅) +
      (∑ i : Fin D.rank, z.2.1 i • current D i) ⊗ₜ[ℂ] ket {1} +
      z.2.2 • (ground D ⊗ₜ[ℂ] ket {1,5}) := by
  classical
  have h := (zeroBasis D H hHG hGH).equivFun_symm_apply
    ((splitCoordinates D).symm z)
  have hc := congrArg (fun x : relativeMassShell D H 0 => (x : State D)) h
  change Psi D H hHG hGH z = _ at hc
  rw [hc]
  change (relativeMassShell D H 0).subtype
    (∑ k, (splitCoordinates D).symm z k • zeroBasis D H hHG hGH k) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ k, (splitCoordinates D).symm z k •
    (zeroBasis D H hHG hGH k : State D)) = _
  simp only [zeroBasis_coe, Fintype.sum_sum_type, Fintype.sum_unique]
  change z.1 • (ground D ⊗ₜ[ℂ] ket ∅) +
    ((∑ i, z.2.1 i • (current D i ⊗ₜ[ℂ] ket {1})) +
      z.2.2 • (ground D ⊗ₜ[ℂ] ket {1,5})) = _
  rw [TensorProduct.sum_tmul]
  simp only [TensorProduct.smul_tmul']
  abel

end Shell

/- Actual ghost charge calculations. The all-integer R sum is captured by CAR. -/

private theorem c_high_odd (S : Finset ℕ) (hS : ∀ j ∈ S, j % 2 = 1)
    (p : ℤ) (hp : 2 ≤ p) : c p (ket S) = 0 := by
  have hcut : ¬ p ≤ 1 := by omega
  have hj : 2 * (p-2).toNat ∉ S := by
    intro hj
    have := hS _ hj
    omega
  simp [c, hcut, annihilate_ket, hj]

private theorem cc_swap (p q : ℤ) : c p * c q = -(c q * c p) :=
  eq_neg_of_add_eq_zero_left (BcGhostFock.ghost_c_car p q)

private theorem R_odd_capture (S : Finset ℕ) (hS : ∀ j ∈ S, j % 2 = 1)
    (r : ℤ) :
    BcGhostBRST.R r (ket S) =
      ∑ p ∈ Finset.Icc (r-1) 1, BcGhostBRST.rTerm r p (ket S) := by
  change (∑ᶠ p : ℤ, BcGhostBRST.rTerm r p (ket S)) = _
  apply finsum_eq_sum_of_support_subset
  intro p hp
  by_contra hn
  have hout : p < r-1 ∨ 1 < p := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn
  apply hp
  rcases hout with h | h
  · have hz := c_high_odd S hS (r-p) (by omega)
    simp [BcGhostBRST.rTerm, Module.End.mul_apply, hz]
  · have hz := c_high_odd S hS p (by omega)
    simp [BcGhostBRST.rTerm, cc_swap p (r-p), Module.End.mul_apply, hz]

private theorem R_one_vacuum :
    BcGhostBRST.R 1 vacuum = -(c 0 (ket {1})) := by
  change BcGhostBRST.R 1 (ket ∅) = _
  rw [R_odd_capture ∅ (by simp)]
  have hI : Finset.Icc (1-1 : ℤ) 1 = {0,1} := by
    ext p; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hI, Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)), Finset.sum_singleton]
  have hs := LinearMap.congr_fun (BcGhostFock.ghost_c_car 0 1) vacuum
  change c 0 (c 1 vacuum) + c 1 (c 0 vacuum) = 0 at hs
  have hswap : c 1 (c 0 vacuum) = -(c 0 (c 1 vacuum)) :=
    eq_neg_of_add_eq_zero_right hs
  norm_num only [BcGhostBRST.rTerm, LinearMap.smul_apply, Module.End.mul_apply,
    Int.reduceMul, Int.reduceSub, Int.cast_neg, Int.cast_one, Int.cast_zero]
  change -(1 / 2 : ℂ) • c 0 (c 1 vacuum) +
    (1 / 2 : ℂ) • c 1 (c 0 vacuum) = -(c 0 (ket {1}))
  rw [hswap, BcGhostFock.ghost_vacuum.2.2.1]
  module

/-- The original cubic on c_1 vacuum; its sign is forced by the occupied-site phase. -/
theorem Qg_down : BcGhostBRST.Qg (ket {1}) = -(c 0 (ket {1})) := by
  have h := LinearMap.congr_fun (BcGhostBRST.ward_c 1) vacuum
  simpa only [LinearMap.add_apply, Module.End.mul_apply, BcGhostBRST.Qg_vacuum,
    map_zero, add_zero, BcGhostFock.ghost_vacuum.2.2.1, R_one_vacuum] using h

private theorem R_minus_one_down :
    BcGhostBRST.R (-1) (ket {1}) = -(c (-1) (c 0 (ket {1}))) := by
  rw [R_odd_capture {1} (by simp)]
  have hI : Finset.Icc (-1-1 : ℤ) 1 = {-2,-1,0,1} := by
    ext p; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hI]
  norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, c, create_ket,
    annihilate_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton,
      Finset.insert_comm]
  module

theorem c_minus_one_down : c (-1) (ket {1}) = -ket {1,5} := by
  norm_num [c, create_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton,
    Finset.pair_comm]

/-- Explicit ghost Ward calculation; no stability or ghost-degree assumption is used. -/
theorem Qg_top : BcGhostBRST.Qg (ket {1,5}) = 0 := by
  have h := LinearMap.congr_fun (BcGhostBRST.ward_c (-1)) (ket {1})
  simp only [LinearMap.add_apply, Module.End.mul_apply, Qg_down,
    R_minus_one_down, map_neg, c_minus_one_down] at h
  have hzero : -BcGhostBRST.Qg (ket {1,5}) = 0 := by
    exact add_right_cancel (h.trans (zero_add _).symm)
  exact neg_eq_zero.mp hzero

/- Actual matter calculations on original charge-zero polynomials. -/

private theorem neutral_ground_nonneg (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) (hm : 0 ≤ m) : neutralMode D i m (ground D) = 0 := by
  by_cases hm0 : m = 0
  · subst m
    simp [ground, LatticeAllStateField.vacuum, neutralMode_single, neutralPolynomialMode, bilinear]
  · have hmneg : ¬ m < 0 := by omega
    simp [ground, LatticeAllStateField.vacuum, neutralMode_single, neutralPolynomialMode,
      hmneg, hm0,
      LinearMap.sum_apply]

private theorem neutral_minus_one_ground (D : LatticeData) (i : Fin D.rank) :
    neutralMode D i (-1) (ground D) = current D i := by
  simp [ground, current, LatticeAllStateField.vacuum,
    LatticeActualConformalState.currentState, neutralMode_single, neutralPolynomialMode]

/-- Every nonnegative or minus-one actual Sugawara mode kills this neutral ground. -/
theorem sugawara_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (hm : -1 ≤ m) :
    sugawaraMode D H m (ground D) = 0 := by
  by_cases hp : 0 < m
  · exact LatticeSugawaraVirasoro.sugawaraMode_ground_positive D H 0 m hp
  by_cases hz : m = 0
  · subst m
    simpa [ground, LatticeAllStateField.vacuum,
      LatticeSugawaraVirasoro.chargeQuadratic,
      LatticeSugawaraVirasoro.chargeScalar, bilinear] using
      LatticeSugawaraVirasoro.sugawaraMode_ground_zero D H 0
  have hmone : m = -1 := by omega
  subst m
  classical
  rw [sugawaraMode_finsum]
  have hn (i j : Fin D.rank) (k : ℤ) :
      normalSummand D i j k (-1-k) (ground D) = 0 := by
    by_cases hk : k < 0
    · simp [normalSummand, hk, Module.End.mul_apply,
        neutral_ground_nonneg D j (-1-k) (by omega)]
    · simp [normalSummand, hk, Module.End.mul_apply,
        neutral_ground_nonneg D i k (by omega)]
  simp only [hn, finsum_zero, smul_zero, Finset.sum_const_zero]

private theorem sugawara_current (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (m : ℤ) (hm : -1 ≤ m) :
    sugawaraMode D H m (current D i) = neutralMode D i (m-1) (ground D) := by
  have h := LinearMap.congr_fun
    (sugawaraMode_current_commutator D H hHG hGH i m (-1)) (ground D)
  simpa [LinearMap.sub_apply, Module.End.mul_apply, neutral_minus_one_ground,
    sugawara_ground D H m hm, LinearMap.smul_apply, sub_eq_add_neg] using h

private theorem T_ground_odd (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j % 2 = 1) :
    T D H (ground D ⊗ₜ[ℂ] ket S) = 0 := by
  change (∑ᶠ m : ℤ, summand D H m (ground D ⊗ₜ[ℂ] ket S)) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : -1 ≤ m
  · simp [summand, TensorProduct.map_tmul, sugawara_ground D H m hm]
  · simp [summand, TensorProduct.map_tmul, c_high_odd S hS (-m) (by omega)]

/-- The m=0 matter term is exactly the c-zero term needed for cancellation. -/
theorem T_current_down (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) :
    T D H (current D i ⊗ₜ[ℂ] ket {1}) = current D i ⊗ₜ[ℂ] c 0 (ket {1}) := by
  have hterm (m : ℤ) (hm : m ≠ 0) :
      summand D H m (current D i ⊗ₜ[ℂ] ket {1}) = 0 := by
    by_cases hmlo : m < -1
    · simp [summand, TensorProduct.map_tmul,
        c_high_odd {1} (by simp) (-m) (by omega)]
    by_cases hmeq : m = -1
    · subst m
      norm_num [summand, TensorProduct.map_tmul, c, create_ket]
    · have hmhi : 1 ≤ m := by omega
      simp [summand, TensorProduct.map_tmul,
        sugawara_current D H hHG hGH i m (by omega),
        neutral_ground_nonneg D i (m-1) (by omega)]
  change (∑ᶠ m : ℤ, summand D H m (current D i ⊗ₜ[ℂ] ket {1})) = _
  rw [finsum_eq_single _ 0 hterm]
  simp [summand, TensorProduct.map_tmul, sugawara_current D H hHG hGH i 0 (by omega),
    neutral_minus_one_ground]

/- Compute the ORIGINAL total charge on the complete, independently derived basis. -/

theorem totalCharge_zeroVector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ZeroIndex D) : LatticeBRST.totalCharge D H (zeroVector D k) = 0 := by
  rcases k with u | (i | u)
  · have hg : BcGhostBRST.Qg (ket ∅) = 0 := BcGhostBRST.Qg_vacuum
    simp [zeroVector, LatticeBRST.totalCharge, LatticeBRST.ghostCharge,
      T_ground_odd D H ∅ (by simp), TensorProduct.map_tmul, hg]
  · simp only [zeroVector, LatticeBRST.totalCharge, LinearMap.add_apply,
      T_current_down D H hHG hGH i, LatticeBRST.ghostCharge,
      TensorProduct.map_tmul, LinearMap.id_apply, Qg_down,
      TensorProduct.tmul_neg, add_neg_cancel]
  · simp [zeroVector, LatticeBRST.totalCharge, LatticeBRST.ghostCharge,
      T_ground_odd D H {1,5} (by simp), TensorProduct.map_tmul, Qg_top]

/-- No rank restriction and no global Q-square premise: this is a direct basis calculation. -/
theorem totalCharge_on_zero_shell (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : x ∈ relativeMassShell D H 0) :
    LatticeBRST.totalCharge D H x = 0 := by
  let y : relativeMassShell D H 0 := ⟨x,hx⟩
  have hlinear : (LatticeBRST.totalCharge D H).comp
      (relativeMassShell D H 0).subtype = 0 := by
    apply (zeroBasis D H hHG hGH).ext
    intro k
    change LatticeBRST.totalCharge D H (zeroBasis D H hHG hGH k : State D) = 0
    rw [zeroBasis_coe, totalCharge_zeroVector D H hHG hGH]
  exact LinearMap.congr_fun hlinear y

/- Actual ghost number on the same original basis. -/

def shellGhostDegree (D : LatticeData) : ZeroIndex D → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem totalGhostNumber_zeroVector (D : LatticeData) (k : ZeroIndex D) :
    tensorNumber D (zeroVector D k) =
      (shellGhostDegree D k : ℂ) • zeroVector D k := by
  rcases k with u | (i | u)
  all_goals norm_num [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    zeroVector, shellGhostDegree,
    TensorProduct.map_tmul, number_ket, BcGhostCharge.charge, Finset.filter_insert,
      Finset.filter_singleton, TensorProduct.tmul_smul]

/-- Exact requested action: G Psi(A,v,C) = Psi(0,v,2C). -/
theorem totalGhostNumber_Psi (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (z : Coordinates D) :
    tensorNumber D (Psi D H hHG hGH z) =
      Psi D H hHG hGH (0,(z.2.1,2*z.2.2)) := by
  classical
  simp only [Psi_formula, map_add, map_smul, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul', map_sum]
  have h0 := totalGhostNumber_zeroVector D (.inl ())
  have h1 := fun i : Fin D.rank => totalGhostNumber_zeroVector D (.inr (.inl i))
  have h2 := totalGhostNumber_zeroVector D (.inr (.inr ()))
  simp only [zeroVector, shellGhostDegree, Nat.cast_zero, zero_smul,
    Nat.cast_one, one_smul, Nat.cast_ofNat] at h0 h1 h2
  simp only [h0, h1, h2, smul_zero, zero_add, smul_smul]
  module

/- Public output stops at the actual shell basis, Q action and G action.
No restricted complex or homology object is substituted by a coordinate complex.
An actual library kernel/range/homology construction is a separate remaining task.
-/

end
end D5.S3.VertexAlgebra.LatticeZeroMomentumBRST
