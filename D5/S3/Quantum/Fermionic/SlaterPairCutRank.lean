/- GID: D5/S3/Quantum/Fermionic/SlaterPairCutRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterPairCutRank
   mirror-E: none(waiver:binary-alternation-phase-and-rank)
   anchors: []
   utility: none
   digest: The ordinary occupation spectrum of Slater orbitals supported on disjoint site pairs. -/

import D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic.NormNum

/-! # Ordered Slater marginals of disjoint two-site orbitals -/

open scoped BigOperators Matrix
open Polynomial

namespace D5.S3.Quantum.Fermionic.SlaterPairCutRank

private def inversion {ι : Type*} [LinearOrder ι] (p q : ι) : ZMod 2 :=
  if q < p then 1 else 0

private def endpointsAlternate {ι : Type*} [LinearOrder ι]
    (p₀ p₁ q₀ q₁ : ι) : Prop :=
  (p₀ < q₀ ∧ q₀ < p₁ ∧ p₁ < q₁) ∨ (q₀ < p₀ ∧ p₀ < q₁ ∧ q₁ < p₁)

open Classical in
private theorem mixed_inversion {ι : Type*} [LinearOrder ι]
    {p₀ p₁ q₀ q₁ : ι} (hp : p₀ < p₁) (hq : q₀ < q₁)
    (h00 : p₀ ≠ q₀) (h01 : p₀ ≠ q₁) (h10 : p₁ ≠ q₀) (h11 : p₁ ≠ q₁) :
    inversion p₀ q₀ + inversion p₀ q₁ + inversion p₁ q₀ + inversion p₁ q₁ =
      if endpointsAlternate p₀ p₁ q₀ q₁ then 1 else 0 := by
  classical
  rcases lt_or_gt_of_ne h00 with h | h
  · rcases lt_or_gt_of_ne h10 with h' | h'
    · simp [inversion, endpointsAlternate, not_lt_of_gt h, not_lt_of_gt (h.trans hq),
        not_lt_of_gt h', not_lt_of_gt (h'.trans hq)]
    · rcases lt_or_gt_of_ne h11 with h'' | h''
      · simp [inversion, endpointsAlternate, h, h', h'', not_lt_of_gt h,
          not_lt_of_gt (h.trans hq), not_lt_of_gt h'']
      · norm_num [inversion, endpointsAlternate, h, h', h'', not_lt_of_gt h,
          not_lt_of_gt (h.trans hq), not_lt_of_gt h'']
        decide
  · rcases lt_or_gt_of_ne h01 with h' | h'
    · rcases lt_or_gt_of_ne h11 with h'' | h''
      · norm_num [inversion, endpointsAlternate, h, h', h'', h.trans hp,
          not_lt_of_gt h, not_lt_of_gt h', not_lt_of_gt h'']
        decide
      · norm_num [inversion, endpointsAlternate, h, h', h'', h.trans hp,
          not_lt_of_gt h, not_lt_of_gt h']
        decide
    · norm_num [inversion, endpointsAlternate, h, h', h.trans hp, h'.trans hp,
        not_lt_of_gt h, not_lt_of_gt h']
      decide

private def bit (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private theorem two_bit_expansion (f : Bool → Bool → ZMod 2) (x y : Bool) :
    f x y = f x false + f false y - f false false +
      bit x * bit y * (f true true - f true false - f false true + f false false) := by
  cases x <;> cases y <;> simp [bit]

private theorem cross_phase_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (cross : ι → κ → Bool → Bool → ZMod 2)
    (x : ι → Bool) (y : κ → Bool) :
    (∑ i, ∑ j, cross i j (x i) (y j)) =
      (∑ i, ∑ j, cross i j (x i) false) +
      (∑ i, ∑ j, cross i j false (y j)) -
      (∑ i, ∑ j, cross i j false false) +
        ∑ i, ∑ j, bit (x i) * bit (y j) *
          (cross i j true true - cross i j true false - cross i j false true +
            cross i j false false) := by
  calc
    _ = ∑ i, ∑ j, (cross i j (x i) false + cross i j false (y j) - cross i j false false +
        bit (x i) * bit (y j) *
          (cross i j true true - cross i j true false - cross i j false true +
            cross i j false false)) := by
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => two_bit_expansion (cross i j) (x i) (y j)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

open Classical in
private theorem alternation_phase {α ι κ : Type*} [LinearOrder α] [Fintype ι] [Fintype κ]
    (p : ι → Bool → α) (q : κ → Bool → α)
    (hp : ∀ i, p i false < p i true) (hq : ∀ j, q j false < q j true)
    (hsep : ∀ i j x y, p i x ≠ q j y)
    (x : ι → Bool) (y : κ → Bool) :
    (∑ i, ∑ j, inversion (p i (x i)) (q j (y j))) =
      (∑ i, ∑ j, inversion (p i (x i)) (q j false)) +
      (∑ i, ∑ j, inversion (p i false) (q j (y j))) -
      (∑ i, ∑ j, inversion (p i false) (q j false)) +
      ∑ i, ∑ j, bit (x i) * bit (y j) *
        (if endpointsAlternate (p i false) (p i true) (q j false) (q j true) then 1 else 0) := by
  rw [cross_phase_expansion (fun i j xb yb => inversion (p i xb) (q j yb)) x y]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := mixed_inversion (hp i) (hq j) (hsep i j false false) (hsep i j false true)
    (hsep i j true false) (hsep i j true true)
  rw [← h]
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ac_rfl


private def inversionSum {α : Type*} [LinearOrder α] {k : ℕ} (p : Fin k → α) : ZMod 2 :=
  ∑ i, ∑ j, if i < j then inversion (p i) (p j) else 0

private theorem inversionSum_append {α : Type*} [LinearOrder α] {m n : ℕ}
    (p : Fin m → α) (q : Fin n → α) :
    inversionSum (Fin.addCases p q) =
      inversionSum p + inversionSum q + ∑ i, ∑ j, inversion (p i) (q j) := by
  have hcross (i : Fin m) (j : Fin n) : Fin.castAdd n i < Fin.natAdd m j := by
    change i.val < m + j.val
    omega
  have hleft (i j : Fin m) : Fin.castAdd n i < Fin.castAdd n j ↔ i < j := Iff.rfl
  simp only [inversionSum, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    hleft, Fin.natAdd_lt_natAdd_iff, hcross, ite_true,
    not_lt_of_gt (hcross _ _), ite_false, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  ac_rfl

private def binarySign : AddChar (ZMod 2) ℂ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℂ)) (by simp)

private def dotHom {ι : Type*} [Fintype ι] (d : ι → ZMod 2) :
    (ι → ZMod 2) →+ ZMod 2 where
  toFun y := d ⬝ᵥ y
  map_zero' := dotProduct_zero _
  map_add' _ _ := dotProduct_add _ _ _

open Classical in
private theorem binary_orthogonality {ι : Type*} [Fintype ι] (d : ι → ZMod 2) :
    (∑ y : ι → ZMod 2, binarySign (d ⬝ᵥ y)) =
      if d = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  split_ifs with h
  · subst d
    simp
  · let ψ := binarySign.compAddMonoidHom (dotHom d)
    change (∑ y, ψ y) = 0
    apply AddChar.sum_eq_zero_of_ne_one
    apply AddChar.ne_one_iff.mpr
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! hall
      exact h (funext hall)
    have hi_one : d i = 1 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (d i) with hz | ho
      · exact False.elim (hi hz)
      · exact ho
    refine ⟨Pi.single i 1, ?_⟩
    change binarySign (d ⬝ᵥ Pi.single i 1) ≠ 1
    rw [dotProduct_single_one, hi_one]
    have hval : (1 : ZMod 2).val = 1 := rfl
    norm_num [binarySign, AddChar.zmodChar_apply, hval]

open Classical in
private theorem fiber_gram_charpoly {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Surjective f) (c : ℂ) (m : ℕ)
    (hcard : ∀ b, (Finset.univ.filter fun a => f a = b).card = m) :
    (Matrix.of fun a a' => if f a = f a' then c else 0 : Matrix α α ℂ).charpoly =
      X ^ (Fintype.card α - Fintype.card β) *
        (X - C ((m : ℂ) * c)) ^ Fintype.card β := by
  let L : Matrix α β ℂ := fun a b => if f a = b then (1 : ℂ) else 0
  let R : Matrix β α ℂ := fun b a => if f a = b then c else 0
  have hLR : L * R = (Matrix.of fun a a' => if f a = f a' then c else 0 : Matrix α α ℂ) := by
    ext a a'
    rw [Matrix.mul_apply]
    simp [L, R, ite_mul, eq_comm]
  have hRL : R * L = Matrix.diagonal (fun _ : β => (m : ℂ) * c) := by
    ext b b'
    by_cases heq : b = b'
    · subst b'
      calc
        (R * L) b b = ∑ a : α, if f a = b then c else 0 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases h : f a = b <;> simp [R, L, h]
        _ = ∑ a ∈ Finset.univ.filter (fun a : α => f a = b), c := by
          rw [Finset.sum_filter]
        _ = Matrix.diagonal (fun _ : β => (m : ℂ) * c) b b := by simp [hcard]
    · rw [Matrix.diagonal_apply_ne _ heq]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases h : f a = b'
      · simp [R, L, h, Ne.symm heq]
      · simp [R, L, h]
  rw [← hLR, Matrix.charpoly_mul_comm_of_le L R (Fintype.card_le_of_surjective f hf),
    hRL, Matrix.charpoly_diagonal]
  simp

open Classical in
private theorem binary_fiber_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (b : LinearMap.range f) :
    (Finset.univ.filter fun a => f a = b.val).card =
      2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (LinearMap.range f)) := by
  obtain ⟨a₀, ha₀⟩ := b.property
  let equiv : {a // f a = b.val} ≃ LinearMap.ker f :=
    { toFun := fun a => ⟨a.val - a₀, by
        rw [LinearMap.mem_ker, map_sub, a.property, ha₀, sub_self]⟩
      invFun := fun k => ⟨k.val + a₀, by
        rw [map_add, LinearMap.mem_ker.mp k.property, ha₀, zero_add]⟩
      left_inv := fun a => Subtype.ext (sub_add_cancel a.val a₀)
      right_inv := fun k => Subtype.ext (add_sub_cancel_right k.val a₀) }
  let : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  rw [← Fintype.card_subtype (fun a => f a = b.val), Fintype.card_congr equiv,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  congr 1
  omega

private theorem binarySign_star (z : ZMod 2) : star (binarySign z) = binarySign z := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) z with rfl | rfl
  · simp
  · have hval : (1 : ZMod 2).val = 1 := rfl
    norm_num [binarySign, AddChar.zmodChar_apply, hval]

open Classical in
private theorem character_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : (ι → ZMod 2) →ₗ[ZMod 2] (κ → ZMod 2)) (c : ℂ) :
    let M : Matrix (ι → ZMod 2) (κ → ZMod 2) ℂ :=
      Matrix.of fun x y => c * binarySign (f x ⬝ᵥ y)
    M * M.conjTranspose =
      Matrix.of fun x x' => if f x = f x' then c * star c * (2 : ℂ) ^ Fintype.card κ else 0 := by
  dsimp only
  ext x x'
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.conjTranspose_apply, star_mul', binarySign_star]
  have hm : ∀ y : κ → ZMod 2,
      (c * binarySign (f x ⬝ᵥ y)) * (star c * binarySign (f x' ⬝ᵥ y)) =
        (c * star c) * binarySign ((f x + f x') ⬝ᵥ y) := by
    intro y
    rw [add_dotProduct, AddChar.map_add_eq_mul]
    ac_rfl
  rw [Finset.sum_congr rfl (fun y _ => hm y), ← Finset.mul_sum, binary_orthogonality]
  have hzero : f x + f x' = 0 ↔ f x = f x' := by
    rw [add_eq_zero_iff_eq_neg]
    simp only [funext_iff, Pi.neg_apply, ZMod.neg_eq_self_mod_two]
  rw [if_congr hzero rfl rfl, mul_ite]
  simp [ZMod.card]


open Classical in
private theorem character_gram_charpoly {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ (ZMod 2)) (c : ℂ)
    (hnorm : c * star c = ((2 : ℂ) ^ (Fintype.card ι + Fintype.card κ))⁻¹) :
    let M : Matrix (ι → ZMod 2) (κ → ZMod 2) ℂ :=
      Matrix.of fun x y => c * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y)
    (M * M.conjTranspose).charpoly =
      X ^ (2 ^ Fintype.card ι - 2 ^ A.rank) *
        (X - C (((2 : ℂ) ^ A.rank)⁻¹)) ^ (2 ^ A.rank) := by
  classical
  let f := Aᵀ.toLin'
  let : Fintype (LinearMap.range f) := Fintype.ofFinite _
  let g : (ι → ZMod 2) → LinearMap.range f :=
    fun x => ⟨f x, ⟨x, rfl⟩⟩
  have hg : Function.Surjective g := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) = A.rank := by
    change Module.finrank (ZMod 2) (LinearMap.range Aᵀ.toLin') = A.rank
    rw [Matrix.toLin'_apply', ← Matrix.rank, Matrix.rank_transpose]
  have hcard : Fintype.card (LinearMap.range f) = 2 ^ A.rank := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hr]
  have hle : A.rank ≤ Fintype.card ι := by
    have hdim := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fintype_fun_eq_card, hr] at hdim
    omega
  have hfilter (b : LinearMap.range f) :
      (Finset.univ.filter fun x => g x = b).card = 2 ^ (Fintype.card ι - A.rank) := by
    have hsets : Finset.univ.filter (fun x => g x = b) =
        Finset.univ.filter (fun x => f x = b.val) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext_iff
    rw [hsets, binary_fiber_card, hr]
  dsimp only
  change (let M : Matrix (ι → ZMod 2) (κ → ZMod 2) ℂ :=
      Matrix.of fun x y => c * binarySign (f x ⬝ᵥ y)
    (M * M.conjTranspose).charpoly) = _
  dsimp only
  rw [character_gram f c]
  have hiff (x x' : ι → ZMod 2) : f x = f x' ↔ g x = g x' :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [hiff]
  have hpoly := fiber_gram_charpoly g hg (c * star c * (2 : ℂ) ^ Fintype.card κ)
    (2 ^ (Fintype.card ι - A.rank)) (fun b => by convert hfilter b)
  trans X ^ (Fintype.card (ι → ZMod 2) - Fintype.card (LinearMap.range f)) *
    (X - C ((↑(2 ^ (Fintype.card ι - A.rank) : ℕ) : ℂ) *
      (c * star c * (2 : ℂ) ^ Fintype.card κ))) ^ Fintype.card (LinearMap.range f)
  · convert hpoly using 2
    ext x x'
    simp only [Matrix.of_apply]
    by_cases h : g x = g x' <;> simp [h]
  rw [hcard]
  have hcoeff : (↑(2 ^ (Fintype.card ι - A.rank) : ℕ) : ℂ) *
       (c * star c * (2 : ℂ) ^ Fintype.card κ) = ((2 : ℂ) ^ A.rank)⁻¹ := by
    push_cast
    rw [hnorm, pow_add, mul_inv_rev]
    rw [pow_sub₀ _ (by norm_num : (2 : ℂ) ≠ 0) hle]
    field_simp
  rw [hcoeff]
  simp [ZMod.card]

variable {ι : Type*} [LinearOrder ι]

private def selectedSites {k : ℕ} (sites : (Fin k × Bool) ↪ ι) (pick : Fin k → Bool) : Finset ι :=
  Finset.univ.image fun j => sites (j, pick j)

private theorem selectedSites_card {k : ℕ} (sites : (Fin k × Bool) ↪ ι) (pick : Fin k → Bool) :
    (selectedSites sites pick).card = k := by
  rw [selectedSites, Finset.card_image_of_injective]
  · simp
  · intro j j' he
    exact congrArg Prod.fst (sites.injective he)

private theorem selectedSites_injective {k : ℕ} (sites : (Fin k × Bool) ↪ ι) :
    Function.Injective (selectedSites sites) := by
  intro a b hab
  funext i
  have ha : sites (i, a i) ∈ selectedSites sites a := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [hab] at ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
  have hij := sites.injective hj
  cases congrArg Prod.fst hij
  exact (congrArg Prod.snd hij).symm

private theorem eq_selectedSites_of_hits {k : ℕ} (sites : (Fin k × Bool) ↪ ι) (s : Finset ι)
    (hs : s.card = k) (hits : ∀ i, ∃ e, sites (i, e) ∈ s) :
    ∃ pick, selectedSites sites pick = s := by
  classical
  choose pick hpick using hits
  refine ⟨pick, Finset.eq_of_subset_of_card_le ?_ (by rw [hs, selectedSites_card])⟩
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact hpick i

private def pairedEntries {k : ℕ} (sites : (Fin k × Bool) ↪ ι) (weight : Fin k → Bool → ℂ) :
    Matrix ι (Fin k) ℂ :=
  fun p j => if p = sites (j, false) then weight j false
    else if p = sites (j, true) then weight j true else 0

private theorem minor_zero_of_no_selection {k : ℕ} (sites : (Fin k × Bool) ↪ ι)
    (weight : Fin k → Bool → ℂ) (s : Finset ι) (hs : s.card = k)
    (h : ¬ ∃ pick, selectedSites sites pick = s) :
    ((pairedEntries sites weight).submatrix (s.orderEmbOfFin hs) id).det = 0 := by
  classical
  have hmiss : ∃ j : Fin k, ∀ e, sites (j, e) ∉ s := by
    by_contra! hall
    exact h (eq_selectedSites_of_hits sites s hs hall)
  obtain ⟨j, hj⟩ := hmiss
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  have hi := s.orderEmbOfFin_mem hs i
  have hne (e : Bool) : s.orderEmbOfFin hs i ≠ sites (j, e) := by
    intro he
    exact hj e (he ▸ hi)
  simp [pairedEntries, hne]


private noncomputable def selectedEquiv {k : ℕ} (sites : (Fin k × Bool) ↪ ι)
    (pick : Fin k → Bool) : Fin k ≃ (selectedSites sites pick : Set ι) :=
  Equiv.ofBijective (fun j => ⟨sites (j, pick j), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩) <| by
    constructor
    · intro i j h
      exact congrArg Prod.fst (sites.injective (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      exact ⟨i, Subtype.ext hi⟩

private theorem pairedEntries_selected {k : ℕ} (sites : (Fin k × Bool) ↪ ι)
    (weight : Fin k → Bool → ℂ) (pick : Fin k → Bool) (i j : Fin k) :
    pairedEntries sites weight (sites (i, pick i)) j =
      (Matrix.diagonal fun j => weight j (pick j)) i j := by
  by_cases hij : i = j
  · subst j
    cases h : pick i <;> simp [pairedEntries, h, sites.injective.eq_iff]
  · have hne (b : Bool) : sites (i, pick i) ≠ sites (j, b) :=
      fun h => hij (congrArg Prod.fst (sites.injective h))
    simp [pairedEntries, Matrix.diagonal_apply_ne _ hij, hne]

private theorem selected_minor_det {k : ℕ} (sites : (Fin k × Bool) ↪ ι)
    (weight : Fin k → Bool → ℂ) (pick : Fin k → Bool) :
    let selected := selectedSites sites pick
    let sorted := (selected.orderIsoOfFin (selectedSites_card sites pick)).toEquiv
    let permutation := sorted.trans (selectedEquiv sites pick).symm
    ((pairedEntries sites weight).submatrix
      (selected.orderEmbOfFin (selectedSites_card sites pick)) id).det =
      (↑(Equiv.Perm.sign permutation : ℤ) : ℂ) * ∏ j, weight j (pick j) := by
  intro selected sorted permutation
  let diagonal := Matrix.diagonal fun j => weight j (pick j)
  have hrows (i : Fin k) :
      selected.orderEmbOfFin (selectedSites_card sites pick) i =
        sites (permutation i, pick (permutation i)) := by
    change (sorted i : ι) = _
    exact (congrArg Subtype.val ((selectedEquiv sites pick).apply_symm_apply (sorted i))).symm
  have hm : (pairedEntries sites weight).submatrix
      (selected.orderEmbOfFin (selectedSites_card sites pick)) id =
        diagonal.submatrix permutation id := by
    ext i j
    simpa only [Matrix.submatrix_apply, id_eq, hrows] using
       pairedEntries_selected sites weight pick (permutation i) j
  rw [hm, Matrix.det_permute, Matrix.det_diagonal]


private theorem sign_eq_selected_inversions {k : ℕ}
    (sites : (Fin k × Bool) ↪ ι) (pick : Fin k → Bool) :
    let selected := selectedSites sites pick
    let sorted := (selected.orderIsoOfFin (selectedSites_card sites pick)).toEquiv
    let permutation := sorted.trans (selectedEquiv sites pick).symm
    Equiv.Perm.sign permutation = (-1 : ℤˣ) ^
      (∑ i : Fin k, ∑ j : Fin k, if i < j ∧ sites (j, pick j) < sites (i, pick i) then 1 else 0) := by
  classical
  intro selected sorted permutation
  rw [← Equiv.Perm.sign_inv permutation]
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have hval (i : Fin k) : (sorted (permutation⁻¹ i) : ι) = sites (i, pick i) := by
    change (sorted (sorted.symm (selectedEquiv sites pick i)) : ι) = _
    rw [sorted.apply_symm_apply]
    rfl
  have hcmp (i j : Fin k) : permutation⁻¹ j < permutation⁻¹ i ↔
      sites (j, pick j) < sites (i, pick i) := by
    let order := selected.orderIsoOfFin (selectedSites_card sites pick)
    change permutation⁻¹ j < permutation⁻¹ i ↔ _
    rw [← order.strictMono.lt_iff_lt]
    change (sorted (permutation⁻¹ j) : ι) < (sorted (permutation⁻¹ i) : ι) ↔ _
    rw [hval, hval]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Fintype.prod_ite_mem, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · have hne := permutation.symm.injective.ne hij.ne
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hij, h, (hcmp i j).not.mp (not_lt_of_gt h)]
    · simp [hij, (hcmp i j).mp h, not_lt_of_gt h]
  · simp [hij]

private def inversionCount {k : ℕ} (p : Fin k → ι) : ℕ :=
  ∑ i, ∑ j, if i < j ∧ p j < p i then 1 else 0

private theorem inversionSum_eq_natCast {k : ℕ} (p : Fin k → ι) :
    inversionSum p = (inversionCount p : ZMod 2) := by
  classical
  unfold inversionCount inversionSum
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> by_cases hp : p j < p i <;> simp [inversion, hij, hp]

private theorem binarySign_natCast (n : ℕ) : binarySign (n : ZMod 2) = (-1 : ℂ) ^ n := by
  rw [binarySign, AddChar.zmodChar_apply, ZMod.val_natCast]
  exact (pow_eq_pow_mod n (by norm_num : (-1 : ℂ) ^ 2 = 1)).symm

private theorem selected_minor_phase {k : ℕ} (sites : (Fin k × Bool) ↪ ι)
    (weight : Fin k → Bool → ℂ) (pick : Fin k → Bool) :
    ((pairedEntries sites weight).submatrix
      ((selectedSites sites pick).orderEmbOfFin (selectedSites_card sites pick)) id).det =
      binarySign (inversionSum (fun j => sites (j, pick j))) * ∏ j, weight j (pick j) := by
  rw [selected_minor_det, sign_eq_selected_inversions, inversionSum_eq_natCast, binarySign_natCast]
  simp [inversionCount]


private def pickEndpoint (z : ZMod 2) : Bool := decide (z = 1)

private theorem bit_pickEndpoint (z : ZMod 2) : bit (pickEndpoint z) = z := by
  exact (show ∀ z : ZMod 2, bit (pickEndpoint z) = z by decide) z

open Classical in
noncomputable def alternationMatrix {m n : ℕ}
    (p : Fin m → Bool → ι) (q : Fin n → Bool → ι) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.of fun i j =>
    if endpointsAlternate (p i false) (p i true) (q j false) (q j true) then 1 else 0

private theorem alternation_phase_bilinear {m n : ℕ}
    (p : Fin m → Bool → ι) (q : Fin n → Bool → ι)
    (hp : ∀ i, p i false < p i true) (hq : ∀ j, q j false < q j true)
    (hsep : ∀ i j x y, p i x ≠ q j y) :
    ∃ left : (Fin m → ZMod 2) → ZMod 2, ∃ right : (Fin n → ZMod 2) → ZMod 2,
      ∀ x y, inversionSum (Fin.addCases (fun i => p i (pickEndpoint (x i)))
        (fun j => q j (pickEndpoint (y j)))) =
        left x + right y + (((alternationMatrix p q)ᵀ *ᵥ x) ⬝ᵥ y) := by
  refine ⟨fun x => inversionSum (fun i => p i (pickEndpoint (x i))) +
      (∑ i, ∑ j, inversion (p i (pickEndpoint (x i))) (q j false)) -
      (∑ i, ∑ j, inversion (p i false) (q j false)),
    fun y => inversionSum (fun j => q j (pickEndpoint (y j))) +
      ∑ i, ∑ j, inversion (p i false) (q j (pickEndpoint (y j))), ?_⟩
  intro x y
  rw [inversionSum_append, alternation_phase p q hp hq hsep]
  simp only [bit_pickEndpoint]
  have hbilin : (((alternationMatrix p q)ᵀ *ᵥ x) ⬝ᵥ y) =
      ∑ i, ∑ j, x i * y j * (alternationMatrix p q) i j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbilin]
  simp only [alternationMatrix, Matrix.of_apply]
  abel


private def cutPairSites {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) :
    (Fin (m + n) × Bool) ↪ ι where
  toFun w := Fin.addCases (fun i => (p (i, w.2) : ι))
    (fun j => (q (j, w.2) : ι)) w.1
  inj' := by
    rintro ⟨i, e⟩ ⟨j, d⟩ h
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left] at h
        exact congrArg (fun w : Fin m × Bool => (Fin.castAdd n w.1, w.2))
          (p.injective (Subtype.ext h))
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        exact False.elim ((q (j, d)).property (h ▸ (p (i, e)).property))
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        exact False.elim ((q (i, e)).property (h.symm ▸ (p (j, d)).property))
      | right j =>
        simp only [Fin.addCases_right] at h
        exact congrArg (fun w : Fin n × Bool => (Fin.natAdd m w.1, w.2))
          (q.injective (Subtype.ext h))

omit [LinearOrder ι] in
private theorem cutPairSites_left {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (i : Fin m) (e : Bool) :
    cutPairSites p q (Fin.castAdd n i, e) = p (i, e) := by
  change Fin.addCases (motive := fun _ => ι) (fun i => (p (i, e) : ι)) (fun j => (q (j, e) : ι))
    (Fin.castAdd n i) = _
  rw [Fin.addCases_left]

omit [LinearOrder ι] in
private theorem cutPairSites_right {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (j : Fin n) (e : Bool) :
    cutPairSites p q (Fin.natAdd m j, e) = q (j, e) := by
  change Fin.addCases (motive := fun _ => ι) (fun i => (p (i, e) : ι)) (fun j => (q (j, e) : ι))
    (Fin.natAdd m j) = _
  rw [Fin.addCases_right]

private def sideSites {m : ℕ} {I : Set ι} (p : (Fin m × Bool) ↪ I) :
    (Fin m × Bool) ↪ ι :=
  p.trans (Function.Embedding.subtype _)

private theorem selectedSites_cut {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (x : Fin m → Bool) (y : Fin n → Bool) :
    selectedSites (cutPairSites p q) (Fin.addCases x y) =
      selectedSites (sideSites p) x ∪ selectedSites (sideSites q) y := by
  ext a
  simp only [selectedSites, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simpa [sideSites, cutPairSites_left] using hi⟩
    | right j => exact Or.inr ⟨j, by simpa [sideSites, cutPairSites_right] using hi⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨Fin.castAdd n i, by simpa [sideSites, cutPairSites_left] using hi⟩
    · exact ⟨Fin.natAdd m j, by simpa [sideSites, cutPairSites_right] using hj⟩


open D5.S3.Quantum.Fermionic.OrderedSlaterCut
open D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
open D5.S3.Quantum.Fermionic.OrderedSlaterFixedFilling

private theorem selectedSites_subset {m : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (x : Fin m → Bool) :
    (↑(selectedSites (sideSites p) x) : Set ι) ⊆ I := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact (p (i, x i)).property

private def pairOccupation {m : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) : (Fin m → Bool) ↪ Occupation I where
  toFun x := ⟨selectedSites (sideSites p) x, selectedSites_subset p x⟩
  inj' := fun _ _ h => selectedSites_injective (sideSites p) (congrArg Subtype.val h)

private theorem union_occupation_injective {I : Set ι}
    {a a' : Occupation I} {b b' : Occupation Iᶜ}
    (h : a.val ∪ b.val = a'.val ∪ b'.val) : a = a' ∧ b = b' := by
  have side {s t : Finset ι} (hs : (s : Set ι) ⊆ I) (ht : (t : Set ι) ⊆ Iᶜ)
      {i : ι} : i ∈ s ↔ i ∈ s ∪ t ∧ i ∈ I := by
    constructor
    · intro hi
      exact ⟨Finset.mem_union_left _ hi, hs hi⟩
    · rintro ⟨hu, hi⟩
      exact (Finset.mem_union.mp hu).elim id fun hx => False.elim (ht hx hi)
  have hleft : a = a' := by
    apply Subtype.ext
    ext i
    rw [side a.property b.property, side a'.property b'.property, h]
  refine ⟨hleft, Subtype.ext ?_⟩
  ext i
  have hr {s t : Finset ι} (hs : (s : Set ι) ⊆ I) (ht : (t : Set ι) ⊆ Iᶜ) :
      i ∈ t ↔ i ∈ s ∪ t ∧ i ∉ I := by
    constructor
    · intro hi
      exact ⟨Finset.mem_union_right _ hi, ht hi⟩
    · rintro ⟨hu, hi⟩
      exact (Finset.mem_union.mp hu).elim (fun hx => False.elim (hi (hs hx))) id
  rw [hr a.property b.property, hr a'.property b'.property, h]

omit [LinearOrder ι] in
private theorem cutPairSites_pick {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (x : Fin m → Bool) (y : Fin n → Bool) :
    (fun j => cutPairSites p q (j, Fin.addCases x y j)) =
      Fin.addCases (fun i => (p (i, x i) : ι)) (fun j => (q (j, y j) : ι)) := by
  funext j
  induction j using Fin.addCases with
  | left i => simp only [Fin.addCases_left, cutPairSites_left]
  | right j => simp only [Fin.addCases_right, cutPairSites_right]


private theorem orderedCut_pairs_zero {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (weight : Fin (m + n) → Bool → ℂ)
    (a : Occupation I) (b : Occupation Iᶜ)
    (h : ¬ (∃ x, pairOccupation p x = a) ∨ ¬ (∃ y, pairOccupation q y = b)) :
    orderedCut I (pairedEntries (cutPairSites p q) weight) a b = 0 := by
  classical
  rw [orderedCut_eq_minor]
  unfold occupiedMinor
  split_ifs with hcard <;> try rfl
  apply minor_zero_of_no_selection _ _ _ hcard
  rintro ⟨pick, hpick⟩
  let x : Fin m → Bool := fun i => pick (Fin.castAdd n i)
  let y : Fin n → Bool := fun j => pick (Fin.natAdd m j)
  have hxy : Fin.addCases x y = pick := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [x]
    | right j => simp [y]
  rw [← hxy, selectedSites_cut] at hpick
  have heq : pairOccupation p x = a ∧ pairOccupation q y = b :=
    union_occupation_injective hpick
  exact h.elim (fun hx => hx ⟨x, heq.1⟩) (fun hy => hy ⟨y, heq.2⟩)

private theorem orderedCut_pairs_selected {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (weight : Fin (m + n) → Bool → ℂ) (x : Fin m → Bool) (y : Fin n → Bool) :
    orderedCut I (pairedEntries (cutPairSites p q) weight) (pairOccupation p x) (pairOccupation q y) =
      binarySign (inversionSum (Fin.addCases (fun i => (p (i, x i) : ι))
        (fun j => (q (j, y j) : ι)))) *
        ∏ j, weight j (Fin.addCases x y j) := by
  rw [orderedCut_eq_minor]
  change occupiedMinor _ (selectedSites (sideSites p) x ∪ selectedSites (sideSites q) y) = _
  rw [← selectedSites_cut, occupiedMinor, dite_eq_left (selectedSites_card _ _), selected_minor_phase,
    cutPairSites_pick]


private theorem orderedCut_pairs_character {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (w : ℂ)
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true)) :
    ∃ left : (Fin m → ZMod 2) → ZMod 2, ∃ right : (Fin n → ZMod 2) → ZMod 2,
      ∀ (x : Fin m → ZMod 2) (y : Fin n → ZMod 2),
        orderedCut I (pairedEntries (cutPairSites p q) fun _ _ => w)
          (pairOccupation p fun i => pickEndpoint (x i))
          (pairOccupation q fun j => pickEndpoint (y j)) =
        binarySign (left x) * (binarySign (right y) *
          (w ^ (m + n) * binarySign
            (((alternationMatrix (fun i e => (p (i, e) : ι))
              (fun j e => (q (j, e) : ι)))ᵀ *ᵥ x) ⬝ᵥ y))) := by
  have hsep (i : Fin m) (j : Fin n) (e d : Bool) : (p (i, e) : ι) ≠ q (j, d) :=
    fun h => (q (j, d)).property (h ▸ (p (i, e)).property)
  obtain ⟨left, right, hphase⟩ := alternation_phase_bilinear _ _ hp hq hsep
  refine ⟨left, right, fun x y => ?_⟩
  rw [orderedCut_pairs_selected, hphase x y]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, AddChar.map_add_eq_mul]
  ring

private theorem pairedEntries_orthonormal {k : ℕ} [Fintype ι] (sites : (Fin k × Bool) ↪ ι)
    (weight : Fin k → Bool → ℂ)
    (hnorm : ∀ j, star (weight j false) * weight j false +
      star (weight j true) * weight j true = 1) :
    (pairedEntries sites weight).conjTranspose * pairedEntries sites weight = 1 := by
  classical
  ext i j : 1
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    have hsite : sites (i, false) ≠ sites (i, true) := by
      simp [sites.injective.eq_iff]
    have hsum (r : ι) :
        star (pairedEntries sites weight r i) * pairedEntries sites weight r i =
          (if r = sites (i, false) then star (weight i false) * weight i false else 0) +
          (if r = sites (i, true) then star (weight i true) * weight i true else 0) := by
      by_cases hf : r = sites (i, false)
      · subst r
        simp [pairedEntries, hsite]
      · by_cases ht : r = sites (i, true) <;> simp [pairedEntries, hf, ht]
    simp only [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hnorm i
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hsep (e d : Bool) : sites (i, e) ≠ sites (j, d) :=
      fun h => hij (congrArg Prod.fst (sites.injective h))
    by_cases hf : r = sites (i, false)
    · subst r
      simp [pairedEntries, hsep]
    · by_cases ht : r = sites (i, true)
      · subst r
        simp [pairedEntries, hsep]
      · simp [pairedEntries, hf, ht]


noncomputable local instance [Fintype ι] (I : Set ι) : Fintype (Occupation I) :=
  Fintype.ofFinite _

private theorem pickEndpoint_bit (b : Bool) : pickEndpoint (bit b) = b := by
  cases b <;> decide

private def pairBitOccupation {m : ℕ} {I : Set ι} (p : (Fin m × Bool) ↪ I) :
    (Fin m → ZMod 2) ↪ Occupation I where
  toFun x := pairOccupation p fun i => pickEndpoint (x i)
  inj' := by
    intro x y h
    have hpick := (pairOccupation p).injective h
    funext i
    simpa only [bit_pickEndpoint] using congrArg (fun f : Fin m → Bool => bit (f i)) hpick

private theorem pairBitOccupation_apply_bits {m : ℕ} {I : Set ι} (p : (Fin m × Bool) ↪ I)
    (x : Fin m → Bool) : pairBitOccupation p (fun i => bit (x i)) = pairOccupation p x := by
  change pairOccupation p (fun i => pickEndpoint (bit (x i))) = pairOccupation p x
  simp only [pickEndpoint_bit]

/-- Each column is supported on its own pair, with the retained orbitals ordered first. -/
def cutPairOrbitals {m n : ℕ} {I : Set ι} (p : (Fin m × Bool) ↪ I)
    (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (weight : Fin (m + n) → Bool → ℂ) :
    Matrix ι (Fin (m + n)) ℂ := pairedEntries (cutPairSites p q) weight


private theorem not_pairOccupation_of_not_bit {m : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) {a : Occupation I} (h : ¬ ∃ x, pairBitOccupation p x = a) :
    ¬ ∃ x, pairOccupation p x = a := by
  rintro ⟨x, hx⟩
  exact h ⟨fun i => bit (x i), (pairBitOccupation_apply_bits p x).trans hx⟩

open Classical in
private theorem charpoly_of_signed_character_padding
    {α β u v : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Fintype u] [Fintype v]
    (e : (u → ZMod 2) ↪ α) (f : (v → ZMod 2) ↪ β)
    (A : Matrix u v (ZMod 2)) (c : ℂ)
    (hnorm : c * star c = ((2 : ℂ) ^ (Fintype.card u + Fintype.card v))⁻¹)
    (left : (u → ZMod 2) → ZMod 2) (right : (v → ZMod 2) → ZMod 2)
    (B : Matrix α β ℂ)
    (active : ∀ x y, B (e x) (f y) =
      (-1 : ℂ) ^ (left x).val * ((-1 : ℂ) ^ (right y).val *
        (c * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y))))
    (row : ∀ a b, (¬ ∃ x, e x = a) → B a b = 0)
    (col : ∀ a b, (¬ ∃ y, f y = b) → B a b = 0) :
    (B * B.conjTranspose).charpoly =
      X ^ (Fintype.card α - 2 ^ A.rank) * (X - C (((2 : ℂ) ^ A.rank)⁻¹)) ^ (2 ^ A.rank) := by
  let M : Matrix (u → ZMod 2) (v → ZMod 2) ℂ :=
    Matrix.of fun x y => c * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y)
  let N : Matrix (u → ZMod 2) (v → ZMod 2) ℂ :=
    fun x y => (-1 : ℂ) ^ (left x).val * ((-1 : ℂ) ^ (right y).val * M x y)
  have heq := eq_padding e f B N active row col
  have hsign : (N * N.conjTranspose).charpoly = (M * M.conjTranspose).charpoly :=
    signed_reindexed_gram (Equiv.refl _) (Equiv.refl _) M
      (fun x => (left x).val) (fun y => (right y).val)
  have hpoly : (M * M.conjTranspose).charpoly =
      X ^ (2 ^ Fintype.card u - 2 ^ A.rank) *
        (X - C (((2 : ℂ) ^ A.rank)⁻¹)) ^ (2 ^ A.rank) :=
    character_gram_charpoly A c hnorm
  have he : Fintype.card (u → ZMod 2) ≤ Fintype.card α :=
    Fintype.card_le_of_injective e e.injective
  have hr : 2 ^ A.rank ≤ 2 ^ Fintype.card u :=
    Nat.pow_le_pow_right (by decide) (Matrix.rank_le_card_height A)
  simp only [Fintype.card_fun, ZMod.card] at he
  have hpad :
      ((embedMatrix e * N * (embedMatrix f).conjTranspose) *
        (embedMatrix e * N * (embedMatrix f).conjTranspose).conjTranspose).charpoly =
      X ^ (Fintype.card α - Fintype.card (u → ZMod 2)) *
        (N * N.conjTranspose).charpoly :=
    paddedGram_charpoly e f N
  have hparts :
      (B * B.conjTranspose).charpoly = X ^ (Fintype.card α - Fintype.card (u → ZMod 2)) *
        (X ^ (2 ^ Fintype.card u - 2 ^ A.rank) *
          (X - C (((2 : ℂ) ^ A.rank)⁻¹)) ^ (2 ^ A.rank)) :=
    (congrArg (fun B : Matrix α β ℂ => (B * B.conjTranspose).charpoly) heq).trans
      (hpad.trans (congrArg
        (fun Q : ℂ[X] => X ^ (Fintype.card α - Fintype.card (u → ZMod 2)) * Q)
        (hsign.trans hpoly)))
  apply hparts.trans
  simp only [Fintype.card_fun, ZMod.card]
  have hexponent : Fintype.card α - 2 ^ Fintype.card u + (2 ^ Fintype.card u - 2 ^ A.rank) =
      Fintype.card α - 2 ^ A.rank := by omega
  rw [← mul_assoc, ← pow_add, hexponent]

open Classical in
theorem orderedCut_pair_charpoly [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true))
    (w : ℂ) (hw : w * star w = (2 : ℂ)⁻¹) :
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    let B := orderedCut I (cutPairOrbitals p q fun _ _ => w)
    (B * B.conjTranspose).charpoly =
      X ^ (Fintype.card (Occupation I) - 2 ^ A.rank) *
        (X - C (((2 : ℂ) ^ A.rank)⁻¹)) ^ (2 ^ A.rank) := by
  intro A B
  let e := pairBitOccupation p
  let f := pairBitOccupation q
  let c : ℂ := w ^ (m + n)
  obtain ⟨left, right, hphase⟩ := orderedCut_pairs_character p q w hp hq
  have hactive (x : Fin m → ZMod 2) (y : Fin n → ZMod 2) :
      B (e x) (f y) =
        (-1 : ℂ) ^ (left x).val * ((-1 : ℂ) ^ (right y).val *
          (c * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y))) :=
    hphase x y
  have hnorm : c * star c =
      ((2 : ℂ) ^ (Fintype.card (Fin m) + Fintype.card (Fin n)))⁻¹ := by
    rw [show c = w ^ (m + n) from rfl, star_pow, ← mul_pow, hw, inv_pow]
    simp
  exact charpoly_of_signed_character_padding e f A c hnorm left right B hactive
    (fun a b ha => orderedCut_pairs_zero p q _ a b (Or.inl (not_pairOccupation_of_not_bit p ha)))
    (fun a b hb => orderedCut_pairs_zero p q _ a b (Or.inr (not_pairOccupation_of_not_bit q hb)))

/-- Keep the retained columns and put every discarded column at its earlier endpoint. -/
def coordinateReplacementWeights {m n : ℕ} (w : ℂ) : Fin (m + n) → Bool → ℂ :=
  Fin.addCases (fun _ _ => w) (fun _ e => if e then 0 else 1)

private theorem replacement_amplitude {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (w : ℂ)
    (x : Fin m → Bool) (y : Fin n → Bool) :
    orderedCut I (cutPairOrbitals p q (coordinateReplacementWeights w))
      (pairOccupation p x) (pairOccupation q y) =
      if y = (fun _ => false) then
        binarySign (inversionSum (Fin.addCases (fun i => (p (i, x i) : ι))
          (fun j => (q (j, false) : ι)))) * w ^ m
      else 0 := by
  classical
  unfold cutPairOrbitals
  rw [orderedCut_pairs_selected, Fin.prod_univ_add]
  simp only [coordinateReplacementWeights, Fin.addCases_left, Fin.addCases_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases hy : y = (fun _ => false)
  · subst y
    simp
  · obtain ⟨j, hj⟩ : ∃ j, y j = true := by
      by_contra! h
      apply hy
      funext j
      exact Bool.eq_false_of_not_eq_true (h j)
    have hprod : (∏ j : Fin n, if y j then (0 : ℂ) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    simp [hy, hprod]

private theorem replacement_compression [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (w : ℂ) :
    retainedRows I (cutPairOrbitals p q fun _ _ => w) =
      retainedRows I (cutPairOrbitals p q (coordinateReplacementWeights w)) := by
  ext u j
  induction j using Fin.addCases with
  | left j =>
    simp [retainedRows, cutPairOrbitals, pairedEntries, coordinateReplacementWeights]
  | right j =>
    have hne (e : Bool) : (u : ι) ≠ q (j, e) := fun h => (q (j, e)).property (h ▸ u.property)
    simp [retainedRows, cutPairOrbitals, pairedEntries, cutPairSites_right, hne]

private theorem binarySign_sq (z : ZMod 2) : binarySign z * binarySign z = 1 := by
  rw [← AddChar.map_add_eq_mul]
  have hz : z + z = 0 := calc
    z + z = -z + z := congrArg (fun a => a + z) (ZMod.neg_eq_self_mod_two z).symm
    _ = 0 := neg_add_cancel z
  rw [hz, AddChar.map_zero_eq_one]

private theorem replacement_charpoly [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ)) (w : ℂ)
    (hw : w * star w = (2 : ℂ)⁻¹) :
    let B := orderedCut I (cutPairOrbitals p q (coordinateReplacementWeights w))
    (B * B.conjTranspose).charpoly = X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  intro B
  let y₀ : Fin n → Bool := fun _ => false
  let f : Unit ↪ Occupation Iᶜ := ⟨fun _ => pairOccupation q y₀, fun _ _ _ => Subsingleton.elim _ _⟩
  let e := pairOccupation p
  let phase (x : Fin m → Bool) := inversionSum (Fin.addCases (fun i => (p (i, x i) : ι))
    (fun j => (q (j, false) : ι)))
  let N : Matrix (Fin m → Bool) Unit ℂ := fun x _ => binarySign (phase x) * w ^ m
  have heq : B = embedMatrix e * N * (embedMatrix f).conjTranspose := by
    apply eq_padding
    · intro x u
      change orderedCut I (cutPairOrbitals p q (coordinateReplacementWeights w))
        (pairOccupation p x) (pairOccupation q y₀) = _
      simpa [y₀] using replacement_amplitude p q w x y₀
    · intro a b ha
      exact orderedCut_pairs_zero p q _ a b (Or.inl ha)
    · intro a b hb
      by_cases ha : ∃ x, pairOccupation p x = a
      · obtain ⟨x, rfl⟩ := ha
        by_cases hex : ∃ y, pairOccupation q y = b
        · obtain ⟨y, rfl⟩ := hex
          have hy : y ≠ y₀ := fun h => hb ⟨(), congrArg (pairOccupation q) h.symm⟩
          simpa [y₀, hy] using replacement_amplitude p q w x y
        · exact orderedCut_pairs_zero p q _ _ b (Or.inr hex)
      · exact orderedCut_pairs_zero p q _ _ b (Or.inl ha)
  have hunit : N.conjTranspose * N = 1 := by
    ext u v
    cases u
    cases v
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    have hterm (x : Fin m → Bool) :
        star (N x ()) * N x () = ((2 : ℂ)⁻¹) ^ m := by
      unfold N
      rw [star_mul', binarySign_star, star_pow]
      calc
        _ = (binarySign (phase x) * binarySign (phase x)) * (w * star w) ^ m := by
          rw [mul_pow]
          ring
        _ = _ := by rw [binarySign_sq, hw, one_mul]
    simp only [Matrix.conjTranspose_apply, hterm, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
  have hle : Fintype.card Unit ≤ Fintype.card (Fin m → Bool) :=
    Fintype.card_le_of_injective (fun _ : Unit => fun _ : Fin m => false)
      (fun _ _ _ => Subsingleton.elim _ _)
  have he : Fintype.card (Fin m → Bool) ≤ Fintype.card (Occupation I) :=
    Fintype.card_le_of_injective e e.injective
  have hpow : Fintype.card (Occupation I) - Fintype.card (Fin m → Bool) +
      (Fintype.card (Fin m → Bool) - Fintype.card Unit) =
        Fintype.card (Occupation I) - 1 := by
    rw [Fintype.card_unit] at hle ⊢
    omega
  rw [heq, paddedGram_charpoly]
  change X ^ (Fintype.card (Occupation I) - Fintype.card (Fin m → Bool)) *
    (N * N.conjTranspose).charpoly = _
  rw [Matrix.charpoly_mul_comm_of_le N N.conjTranspose hle, hunit, ← mul_assoc, ← pow_add, hpow]
  simp [Matrix.charpoly_one]


/-- The coordinate replacement preserves the compression and leaves a pure marginal. -/
theorem coordinate_replacement [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (w : ℂ) (hw : w * star w = (2 : ℂ)⁻¹) :
    let V := cutPairOrbitals p q fun _ _ => w
    let W := cutPairOrbitals p q (coordinateReplacementWeights w)
    V.conjTranspose * V = 1 ∧ W.conjTranspose * W = 1 ∧
    retainedRows I V * (retainedRows I V).conjTranspose =
      retainedRows I W * (retainedRows I W).conjTranspose ∧
    ((orderedCut I W) * (orderedCut I W).conjTranspose).charpoly =
      X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  intro V W
  have hn : star w * w + star w * w = 1 := by
    rw [mul_comm (star w) w, hw]
    norm_num
  refine ⟨pairedEntries_orthonormal _ _ (fun _ => hn), pairedEntries_orthonormal _ _ ?_, ?_,
    replacement_charpoly p q w hw⟩
  · intro j
    induction j using Fin.addCases with
    | left j => simpa only [coordinateReplacementWeights, Fin.addCases_left] using hn
    | right j => simp [coordinateReplacementWeights]
  · exact congrArg (fun M => M * M.conjTranspose) (replacement_compression p q w)

end D5.S3.Quantum.Fermionic.SlaterPairCutRank
