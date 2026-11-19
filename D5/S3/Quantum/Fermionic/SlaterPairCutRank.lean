/- GID: D5/S3/Quantum/Fermionic/SlaterPairCutRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterPairCutRank
   mirror-E: none(waiver:binary-alternation-phase-and-rank)
   anchors: []
   utility: none
   digest: The ordinary occupation spectrum of Slater orbitals supported on disjoint site pairs. -/

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
private noncomputable def alternationMatrix {m n : ℕ}
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

end D5.S3.Quantum.Fermionic.SlaterPairCutRank
