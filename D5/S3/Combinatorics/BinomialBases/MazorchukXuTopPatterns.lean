/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuTopPatterns
   mirror-E: none(waiver:top-coordinate-pattern-count)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: none
   digest: Top coordinate patterns are counted by a subset and a complementary permutation. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuPolynomial
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm

/-! Counting the generic top-support coordinate patterns. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

private def TopChoice (i : ℕ) :=
  (P : {S : Finset (Fin (2 * i)) // S.card = i}) × (Fin i ≃ {r // r ∉ P.val})

private noncomputable instance topChoiceFintype (i : ℕ) : Fintype (TopChoice i) := by
  classical
  unfold TopChoice
  infer_instance

private noncomputable def topChoiceData {i : ℕ} (x : TopChoice i) : CoordinateDataCarrier (2 * i) i := by
  classical
  let p : Fin i → Fin (2 * i + 1) := fun j => (x.1.val.orderEmbOfFin x.1.property j).succ
  let c : Fin i → Fin (2 * i + 1) := fun j => (x.2 j).val.succ
  exact (p, c, Finset.univ.filter (fun jk => jk.1 < jk.2 ∧
    (c jk.1).val < (p jk.2).val ∧ (c jk.2).val < (p jk.1).val))

private theorem topChoiceData_mem {i : ℕ} (x : TopChoice i) :
    topChoiceData x ∈ coordinateDataFamily (2 * i) i ∧
      coordinateDataSupport (topChoiceData x) = Finset.univ.erase 0 := by
  classical
  let p : Fin i → Fin (2 * i + 1) := (topChoiceData x).1
  let c : Fin i → Fin (2 * i + 1) := (topChoiceData x).2.1
  have hp (j) : p j = (x.1.val.orderEmbOfFin x.1.property j).succ := rfl
  have hc (j) : c j = (x.2 j).val.succ := rfl
  have hpm : StrictMono (fun j => (p j).val) := by
    intro j k hjk
    have := (x.1.val.orderEmbOfFin x.1.property).strictMono hjk
    simp only [hp, Fin.val_succ]
    omega
  have hdis : ∀ j k, (c j).val ≠ (p k).val := by
    intro j k heq
    have hh : (x.2 j).val = x.1.val.orderEmbOfFin x.1.property k := by
      apply Fin.ext
      simpa only [hc, hp, Fin.val_succ, Nat.add_right_cancel_iff] using heq
    exact (x.2 j).property (hh ▸ x.1.val.orderEmbOfFin_mem x.1.property k)
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hpm.monotone, ?_, ?_⟩
    · intro j k hjk
      exact (Finset.mem_filter.mp hjk).2.1
    · apply (coordinate_generic_rules_iff (fun j => (p j).val) (fun j => (c j).val)
        (fun j k => (j, k) ∈ (topChoiceData x).2.2) hpm
        (fun j => Nat.le_of_lt_succ (p j).isLt)
        (fun j => Nat.le_of_lt_succ (c j).isLt)
        (fun j => by rw [hp]; simp) hdis
        (fun j k hjk => (Finset.mem_filter.mp hjk).2.1)).mpr
      intro j k
      simp only [topChoiceData, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  · ext a
    constructor
    · intro ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩
    · intro ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      have hap : 0 < a.val := Fin.pos_iff_ne_zero.mpr ha0
      let r : Fin (2 * i) := ⟨a.val - 1, by have := a.isLt; omega⟩
      have hra : r.succ = a := Fin.ext (by dsimp [r]; omega)
      apply Finset.mem_erase.mpr ⟨ha0, ?_⟩
      by_cases hr : r ∈ x.1.val
      · obtain ⟨j, hj⟩ := (x.1.val.orderIsoOfFin x.1.property).surjective ⟨r, hr⟩
        have heq : p j = a := by
          rw [hp, ← hra]
          exact congrArg Fin.succ (congrArg Subtype.val hj)
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩)
      · obtain ⟨j, hj⟩ := x.2.surjective ⟨r, hr⟩
        have heq : c j = a := by
          rw [hc, ← hra]
          exact congrArg Fin.succ (congrArg Subtype.val hj)
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq⟩)

private theorem top_support_separated {i : ℕ} (d : CoordinateDataCarrier (2 * i) i)
    (hs : coordinateDataSupport d = Finset.univ.erase 0) :
    (∀ j, d.1 j ≠ 0) ∧ (∀ j, d.2.1 j ≠ 0) ∧
      Function.Injective (Sum.elim d.1 d.2.1) := by
  classical
  let U := Finset.univ.image d.1 ∪ Finset.univ.image d.2.1
  have hcard : (coordinateDataSupport d).card = 2 * i := by rw [hs]; simp
  have hU : U.card ≤ 2 * i := by
    have hp := Finset.card_image_le (s := Finset.univ) (f := d.1)
    have hc := Finset.card_image_le (s := Finset.univ) (f := d.2.1)
    have hu := Finset.card_union_le (Finset.univ.image d.1) (Finset.univ.image d.2.1)
    simp only [Finset.card_univ, Fintype.card_fin] at hp hc
    dsimp [U]
    omega
  have hz : (0 : Fin (2 * i + 1)) ∉ U := by
    intro hz
    have h := Finset.card_erase_add_one hz
    change (coordinateDataSupport d).card + 1 = U.card at h
    omega
  have hpn : ∀ j, d.1 j ≠ 0 := by
    intro j hj
    apply hz
    rw [← hj]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hcn : ∀ j, d.2.1 j ≠ 0 := by
    intro j hj
    apply hz
    rw [← hj]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  refine ⟨hpn, hcn, ?_⟩
  have himage : Finset.univ.image (Sum.elim d.1 d.2.1) = U := by
    ext a
    simp [U]
  have hcU : U.card = 2 * i := by
    have herase : U.erase 0 = U := Finset.erase_eq_of_notMem hz
    change (U.erase 0).card = 2 * i at hcard
    rwa [herase] at hcard
  have hh : (Finset.univ.image (Sum.elim d.1 d.2.1)).card =
      (Finset.univ : Finset (Fin i ⊕ Fin i)).card := by rw [himage, hcU]; simp; omega
  have hinj := Finset.injOn_of_card_image_eq hh
  exact fun a b hab => hinj (Finset.mem_univ _) (Finset.mem_univ _) hab

private theorem topChoiceData_surjective {i : ℕ} (d : CoordinateDataCarrier (2 * i) i)
    (hd : d ∈ coordinateDataFamily (2 * i) i)
    (hds : coordinateDataSupport d = Finset.univ.erase 0) :
    ∃ x : TopChoice i, topChoiceData x = d := by
  classical
  obtain ⟨hpn, hcn, hinj⟩ := top_support_separated d hds
  obtain ⟨_, hpm, hB, hR⟩ := Finset.mem_filter.mp hd
  let p0 : Fin i → Fin (2 * i) := fun j => ⟨(d.1 j).val - 1, by
    have := (d.1 j).isLt
    have := Fin.pos_iff_ne_zero.mpr (hpn j)
    omega⟩
  let c0 : Fin i → Fin (2 * i) := fun j => ⟨(d.2.1 j).val - 1, by
    have := (d.2.1 j).isLt
    have := Fin.pos_iff_ne_zero.mpr (hcn j)
    omega⟩
  have hpsucc (j) : (p0 j).succ = d.1 j := by
    apply Fin.ext
    have := Fin.pos_iff_ne_zero.mpr (hpn j)
    dsimp [p0]
    omega
  have hcsucc (j) : (c0 j).succ = d.2.1 j := by
    apply Fin.ext
    have := Fin.pos_iff_ne_zero.mpr (hcn j)
    dsimp [c0]
    omega
  have hpInj : Function.Injective d.1 := by
    intro j k hjk
    exact Sum.inl.inj (hinj (a₁ := Sum.inl j) (a₂ := Sum.inl k) hjk)
  have hcInj : Function.Injective d.2.1 := by
    intro j k hjk
    exact Sum.inr.inj (hinj (a₁ := Sum.inr j) (a₂ := Sum.inr k) hjk)
  have hpNatInj : Function.Injective (fun j => (d.1 j).val) := by
    intro j k hjk
    exact hpInj (Fin.ext hjk)
  have hpstrict := hpm.strictMono_of_injective hpNatInj
  have hp0 : StrictMono p0 := by
    intro j k hjk
    have hlt : (d.1 j).val < (d.1 k).val := hpstrict hjk
    have hjp : (d.1 j).val ≠ 0 := fun hh => hpn j (Fin.ext hh)
    have hkp : (d.1 k).val ≠ 0 := fun hh => hpn k (Fin.ext hh)
    change (d.1 j).val - 1 < (d.1 k).val - 1
    omega
  let P := Finset.univ.image p0
  have hP : P.card = i := by
    rw [Finset.card_image_of_injective _ hp0.injective, Finset.card_univ, Fintype.card_fin]
  have hdis : ∀ j k, d.2.1 j ≠ d.1 k := by
    intro j k hjk
    have h := hinj (a₁ := Sum.inr j) (a₂ := Sum.inl k) hjk
    cases h
  have hcnot : ∀ j, c0 j ∉ P := by
    intro j hj
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
    exact hdis j k ((hcsucc j).symm.trans ((congrArg Fin.succ hk).symm.trans (hpsucc k)))
  let cf : Fin i → {r : Fin (2 * i) // r ∉ P} := fun j => ⟨c0 j, hcnot j⟩
  have hcf : Function.Bijective cf := by
    constructor
    · intro j k hjk
      apply hcInj
      exact (hcsucc j).symm.trans ((congrArg Fin.succ (congrArg Subtype.val hjk)).trans (hcsucc k))
    · intro r
      have hr : r.val.succ ∈ coordinateDataSupport d := by rw [hds]; simp
      obtain hr := (Finset.mem_erase.mp hr).2
      rcases Finset.mem_union.mp hr with hleft | hright
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hleft
        have heq : p0 j = r.val := Fin.succ_injective _ ((hpsucc j).trans hj)
        exact False.elim (r.property (heq ▸ Finset.mem_image_of_mem p0 (Finset.mem_univ j)))
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hright
        refine ⟨j, Subtype.ext ?_⟩
        exact Fin.succ_injective _ ((hcsucc j).trans hj)
  let e := Equiv.ofBijective cf hcf
  have hpEnum : P.orderEmbOfFin hP = p0 := by
    apply (P.orderEmbOfFin hP).strictMono.eq_of_range_eq hp0
    ext r
    constructor
    · rintro ⟨j, rfl⟩
      have hm := P.orderEmbOfFin_mem hP j
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
      exact ⟨k, hk⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := (P.orderIsoOfFin hP).surjective
        ⟨p0 j, Finset.mem_image_of_mem p0 (Finset.mem_univ j)⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  let x : TopChoice i := ⟨⟨P, hP⟩, e⟩
  refine ⟨x, ?_⟩
  have hpx : (topChoiceData x).1 = d.1 := by
    funext j
    change (P.orderEmbOfFin hP j).succ = d.1 j
    rw [show P.orderEmbOfFin hP j = p0 j from congrFun hpEnum j]
    exact hpsucc j
  have hcx : (topChoiceData x).2.1 = d.2.1 := by
    funext j
    exact hcsucc j
  apply Prod.ext hpx
  apply Prod.ext hcx
  have hbits := coordinate_generic_bits (fun j => (d.1 j).val) (fun j => (d.2.1 j).val)
    (fun j k => (j, k) ∈ d.2.2) hpstrict
    (fun j => Nat.le_of_lt_succ (d.1 j).isLt)
    (fun j => Nat.le_of_lt_succ (d.2.1 j).isLt)
    (fun j => Fin.pos_iff_ne_zero.mpr (hpn j))
    (fun j k heq => hdis j k (Fin.ext heq)) hB hR
  ext jk
  rcases jk with ⟨j, k⟩
  change ((j, k) ∈ (Finset.univ.filter (fun jk : Fin i × Fin i => jk.1 < jk.2 ∧
    ((topChoiceData x).2.1 jk.1).val < ((topChoiceData x).1 jk.2).val ∧
    ((topChoiceData x).2.1 jk.2).val < ((topChoiceData x).1 jk.1).val))) ↔ _
  rw [hpx, hcx]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hbits j k).symm

private theorem topChoiceData_injective {i : ℕ} : Function.Injective (@topChoiceData i) := by
  classical
  rintro ⟨⟨P, hP⟩, e⟩ ⟨⟨Q, hQ⟩, f⟩ h
  have hp (j : Fin i) : P.orderEmbOfFin hP j = Q.orderEmbOfFin hQ j := by
    apply Fin.succ_injective
    exact congrFun (congrArg Prod.fst h) j
  have hPQ : P = Q := by
    ext r
    constructor
    · intro hr
      obtain ⟨j, hj⟩ := (P.orderIsoOfFin hP).surjective ⟨r, hr⟩
      have hj' : P.orderEmbOfFin hP j = r := congrArg Subtype.val hj
      rw [← hj', hp]
      exact Q.orderEmbOfFin_mem hQ j
    · intro hr
      obtain ⟨j, hj⟩ := (Q.orderIsoOfFin hQ).surjective ⟨r, hr⟩
      have hj' : Q.orderEmbOfFin hQ j = r := congrArg Subtype.val hj
      rw [← hj', ← hp]
      exact P.orderEmbOfFin_mem hP j
  subst Q
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    apply Fin.succ_injective
    exact congrFun (congrArg (fun d => d.2.1) h) j
  cases hef
  rfl

private theorem topChoice_card (i : ℕ) :
    Fintype.card (TopChoice i) = (2 * i).choose i * i.factorial := by
  classical
  unfold TopChoice
  rw [Fintype.card_sigma]
  have heq (P : {S : Finset (Fin (2 * i)) // S.card = i}) :
      Fintype.card (Fin i ≃ {r // r ∉ P.val}) = i.factorial := by
    have hc : Fintype.card {r : Fin (2 * i) // r ∉ P.val} = i := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, P.property, Fintype.card_fin]
      omega
    let e : Fin i ≃ {r : Fin (2 * i) // r ∉ P.val} :=
      (Fintype.equivFinOfCardEq hc).symm
    simpa only [Fintype.card_fin] using Fintype.card_equiv e
  simp only [heq, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_finset_len, Fintype.card_fin]

/-- The literal top-support pattern coefficient has the conjectured factorial value. -/
theorem patternCoefficient_top_factorial (i : ℕ) :
    i.factorial * patternCoefficient i (2 * i) = (2 * i).factorial := by
  classical
  have hc : patternCoefficient i (2 * i) = Fintype.card (TopChoice i) := by
    unfold patternCoefficient
    symm
    change (Finset.univ : Finset (TopChoice i)).card = _
    apply Finset.card_bij (fun x _ => topChoiceData x)
    · intro x hx
      exact Finset.mem_filter.mpr (topChoiceData_mem x)
    · intro x hx y hy hxy
      exact topChoiceData_injective hxy
    · intro d hd
      obtain ⟨hd, hs⟩ := Finset.mem_filter.mp hd
      obtain ⟨x, hx⟩ := topChoiceData_surjective d hd hs
      exact ⟨x, Finset.mem_univ _, hx⟩
  rw [hc, topChoice_card]
  have h := Nat.add_choose_mul_factorial_mul_factorial i i
  simpa only [two_mul] using (show i.factorial * ((i + i).choose i * i.factorial) =
    (i + i).factorial from by nlinarith)

/-- The complete original Mazorchuk–Xu polynomial conjecture, for every deficit and
all original valid ranks, with exact degree and leading coefficient. -/
theorem mazorchukXu_conjecture : Conjecture := by
  intro i
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hff : ((2 * i).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * i)
  have hfactor : (i.factorial : ℚ) * (patternCoefficient i (2 * i) : ℚ) =
      ((2 * i).factorial : ℚ) := by exact_mod_cast patternCoefficient_top_factorial i
  have hcoeff : (countingPolynomial i).coeff (2 * i) = (i.factorial : ℚ)⁻¹ := by
    rw [countingPolynomial_top_coeff]
    field_simp
    nlinarith [hfactor]
  have hdeg : (countingPolynomial i).natDegree = 2 * i :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (countingPolynomial_natDegree_le i)
      (hcoeff ▸ inv_ne_zero hf)
  refine ⟨countingPolynomial i, hdeg, ?_, ?_⟩
  · simpa only [Polynomial.leadingCoeff, hdeg] using hcoeff
  · intro n hn
    exact countingPolynomial_eval hn

end D5.S3.Combinatorics.MazorchukXu
