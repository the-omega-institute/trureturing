/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Interior slot equivalences and alphabet/support encodings. -/
/-
admission_basis: escape-witness
escape_witness: interior_slot_equiv, interior_code_equiv
  (layered horizontal slot/count content).
InteriorSlots: proof_shape=bind-only; consumers=cut_slots_equiv,interior_code_equiv,interior_one_column_count,interior_slot_equiv
boundary_top_shared: proof_shape=bind-only; consumers=boundary_bottom_shared,cut_slots_equiv
boundary_bottom_shared: proof_shape=bind-only; consumers=cut_slots_equiv
cut_slots_equiv: proof_shape=bind-only; consumers=interior_slot_equiv
interior_slot_equiv: proof_shape=content; consumers=interior_count_alphabets,interior_one_column_count
OrdinaryAlphabet: proof_shape=bind-only; consumers=InteriorAlphabet,InteriorCode,coded_boundary,coded_boundary_valid,interior_count_alphabets,interior_six_lower_pairs,ordinary_equiv,pair_count_support
InteriorAlphabet: proof_shape=bind-only; consumers=InteriorCode,interior_count_alphabets,interior_six_lower_pairs,pair_count_support,support_alphabet_card
InteriorCode: proof_shape=bind-only; consumers=interior_code_equiv,interior_count_alphabets
coded_boundary: proof_shape=bind-only; consumers=coded_boundary_valid,interior_code_equiv
coded_boundary_valid: proof_shape=content; consumers=interior_code_equiv
interior_code_equiv: proof_shape=content; consumers=interior_count_alphabets
interior_count_alphabets: proof_shape=bind-only; consumers=interior_count_support
word_support: proof_shape=bind-only; consumers=pair_count_support,sum_by_support,support_alphabet_card,word_support_card,word_support_empty,word_support_full,word_support_singleton
word_support_empty: proof_shape=bind-only; consumers=word_support_card
word_support_singleton: proof_shape=bind-only; consumers=word_support_card,word_support_full
word_support_full: proof_shape=content; consumers=word_support_card
support_weight: proof_shape=bind-only; consumers=pair_count_support,pair_support_count,sum_by_support,support_case_count,support_case_eval,word_support_card
word_support_card: proof_shape=content; consumers=sum_by_support
sum_by_support: proof_shape=bind-only; consumers=pair_count_support
ordinary_value: proof_shape=bind-only; consumers=SupportAlphabet,ordinary_equiv,ordinary_value_valid
ordinary_value_valid: proof_shape=bind-only; consumers=ordinary_equiv
ordinary_equiv: proof_shape=bind-only; consumers=pair_count_support,support_alphabet_card
SupportAlphabet: proof_shape=bind-only; consumers=pair_count_support,pair_support_count,support_alphabet_card,support_sizes_correct
support_alphabet_card: proof_shape=bind-only; consumers=pair_count_support
pair_support_count: proof_shape=bind-only; consumers=interior_count,interior_count_support,pair_count_support,pair_support_cases
pair_count_support: proof_shape=content; consumers=interior_count_support,interior_six_lower_pairs
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
import Mathlib.Algebra.Ring.GeomSum

/-! Horizontal defects, with dimensions expressed as numbers of steps. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal

open KingGrid KingDifference
open scoped IsAddKleinFour

/-- The upper and lower boundary models share every nondefective horizontal slot. -/
def InteriorSlots (a b M : ℕ) (s : Fin M) :=
  {q : {u : BoundaryData a M // BoundaryValid s u} ×
      {l : BoundaryData b M // BoundaryValid s l} //
    ∀ j, j ≠ s → q.1.val.h j = q.2.val.h j}

theorem boundary_top_shared {m M : ℕ} (s : Fin M)
    (t : {t : DiffField (m + 1) M // RawAdmissible (.H 0 s) t}) (j : Fin M) (hj : j ≠ s) :
    (boundary_slot_equiv m M s t).val.h j = t.val.h 0 j := by
  simpa [boundary_slot_equiv, boundary_extract, hj] using (boundary_h s t.val t.property 0 j).symm

theorem boundary_bottom_shared {m M : ℕ} (s : Fin M)
    (t : {t : DiffField (m + 1) M // RawAdmissible (.H (Fin.last (m + 1)) s) t})
    (j : Fin M) (hj : j ≠ s) :
    (boundary_bottom_slot_equiv m M s t).val.h j = t.val.h (Fin.last (m + 1)) j := by
  have ht : RawAdmissible (.H 0 s) (row_reflect t.val) := by
    simpa using row_reflect_raw (Fin.last (m + 1)) s t.val t.property
  have h := boundary_top_shared s ⟨row_reflect t.val,ht⟩ j hj
  simpa [boundary_bottom_slot_equiv, row_reflect_equiv, row_reflect,
    Equiv.subtypeEquivRight, Equiv.subtypeEquiv, boundary_slot_equiv, boundary_extract] using h

def cut_slots_equiv (a b M : ℕ) (s : Fin M) :
    CutFields (a + 1) (b + 1) M s ≃ InteriorSlots a b M s where
  toFun q := ⟨((boundary_bottom_slot_equiv a M s) ⟨q.val.1,q.property.1⟩,
      (boundary_slot_equiv b M s) ⟨q.val.2,q.property.2.1⟩), by
    intro j hj
    rw [boundary_bottom_shared s _ j hj, boundary_top_shared s _ j hj]
    exact q.property.2.2 j⟩
  invFun q := ⟨(((boundary_bottom_slot_equiv a M s).symm q.val.1).val,
      ((boundary_slot_equiv b M s).symm q.val.2).val), by
    refine ⟨((boundary_bottom_slot_equiv a M s).symm q.val.1).property,
      ((boundary_slot_equiv b M s).symm q.val.2).property, ?_⟩
    intro j
    by_cases hj : j = s
    · subst j
      have hu := ((boundary_bottom_slot_equiv a M s).symm q.val.1).property.2
        (.H (Fin.last (a + 1)) s)
      have hl := ((boundary_slot_equiv b M s).symm q.val.2).property.2 (.H 0 s)
      exact (hu.mpr rfl).trans (hl.mpr rfl).symm
    · have hu := boundary_bottom_shared s ((boundary_bottom_slot_equiv a M s).symm q.val.1) j hj
      have hl := boundary_top_shared s ((boundary_slot_equiv b M s).symm q.val.2) j hj
      rw [Equiv.apply_symm_apply] at hu hl
      exact hu.symm.trans ((q.property j hj).trans hl)⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- Interior horizontal defects are exactly two compatible boundary-slot assignments. -/
def interior_slot_equiv (a b M : ℕ) (s : Fin M) :
    {t : DiffField ((a + 1) + (b + 1)) M //
      RawAdmissible (.H (cut_row (a + 1) (b + 1)) s) t} ≃ InteriorSlots a b M s :=
  (horizontal_cut_equiv (a + 1) (b + 1) M s).trans (cut_slots_equiv a b M s)

/-- The ordinary vertical alphabet excludes the broken horizontal value. -/
abbrev OrdinaryAlphabet (x : NZPair) := {v : K // v ≠ 0 ∧ v ≠ x.val.1 + x.val.2}

/-- A shared horizontal slot avoids both special values and both ordinary vertical words. -/
abbrev InteriorAlphabet {a b : ℕ} (x y : NZPair)
    (u : Fin a → OrdinaryAlphabet x) (v : Fin b → OrdinaryAlphabet y) (p q : K) :=
  {h : K // h ≠ 0 ∧ h ≠ p ∧ h ≠ q ∧ (∀ i, h ≠ (u i).val) ∧ ∀ i, h ≠ (v i).val}

/-- Independent special pairs and ordinary vertical words, followed by shared horizontal words. -/
abbrev InteriorCode (a b c d : ℕ) :=
  Σ x : NZPair, Σ y : NZPair,
    Σ u : Fin a → OrdinaryAlphabet x, Σ v : Fin b → OrdinaryAlphabet y,
      (Fin c → InteriorAlphabet x y u v x.val.1 y.val.1) ×
      (Fin d → InteriorAlphabet x y u v x.val.2 y.val.2)

def coded_boundary {m c d : ℕ} (x : NZPair)
    (u : Fin m → OrdinaryAlphabet x) (l : Fin c → K) (r : Fin d → K) :
    BoundaryData m (c + (d + 1)) where
  p := x.val.1
  q := x.val.2
  h := Fin.addCases l (Fin.cases (x.val.1 + x.val.2) r)
  v i := (u i).val

theorem coded_boundary_valid {m c d : ℕ} (x : NZPair)
    (u : Fin m → OrdinaryAlphabet x) (l : Fin c → K) (r : Fin d → K)
    (hl : ∀ j, l j ≠ 0 ∧ l j ≠ x.val.1 ∧ ∀ i, l j ≠ (u i).val)
    (hr : ∀ j, r j ≠ 0 ∧ r j ≠ x.val.2 ∧ ∀ i, r j ≠ (u i).val) :
    BoundaryValid (pivot c d) (coded_boundary x u l r) := by
  have hz : x.val.1 + x.val.2 ≠ 0 := by
    rw [ne_eq, add_eq_zero_iff_eq_neg, IsAddKleinFour.neg_eq_self]
    exact x.property.2.2
  refine ⟨x.property.1,x.property.2.1,x.property.2.2,?_,?_,?_,?_,?_,?_⟩
  · simp [coded_boundary, pivot]
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [coded_boundary] using (hl j).1
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [coded_boundary] using hz
      · simpa [coded_boundary] using (hr j).1
  · exact fun i => (u i).property.1
  · intro j
    refine Fin.addCases (fun j _ => ?_) (fun j hj => ?_) j
    · simpa [coded_boundary] using (hl j).2.1
    · have := j.isLt
      simp only [Fin.lt_def, Fin.val_natAdd, pivot, Fin.val_zero] at hj
      omega
  · intro j
    refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) j
    · have := j.isLt
      simp only [Fin.lt_def, Fin.val_castAdd, pivot, Fin.val_natAdd, Fin.val_zero] at hj
      omega
    · refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j _ => ?_) j hj
      simpa [coded_boundary] using (hr j).2.1
  · intro i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [coded_boundary] using (hl j).2.2 i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [coded_boundary] using Ne.symm (u i).property.2
      · simpa [coded_boundary] using (hr j).2.2 i

/-- A direct four-word version of the interior slot classification. -/
def interior_code_equiv (a b c d : ℕ) :
    InteriorCode a b c d ≃ InteriorSlots a b (c + (d + 1)) (pivot c d) where
  toFun w := ⟨(
    ⟨coded_boundary w.1 w.2.2.1 (fun j => (w.2.2.2.2.1 j).val)
        (fun j => (w.2.2.2.2.2 j).val),
      coded_boundary_valid _ _ _ _
        (fun j => ⟨(w.2.2.2.2.1 j).property.1,(w.2.2.2.2.1 j).property.2.1,
          (w.2.2.2.2.1 j).property.2.2.2.1⟩)
        (fun j => ⟨(w.2.2.2.2.2 j).property.1,(w.2.2.2.2.2 j).property.2.1,
          (w.2.2.2.2.2 j).property.2.2.2.1⟩)⟩,
    ⟨coded_boundary w.2.1 w.2.2.2.1 (fun j => (w.2.2.2.2.1 j).val)
        (fun j => (w.2.2.2.2.2 j).val),
      coded_boundary_valid _ _ _ _
        (fun j => ⟨(w.2.2.2.2.1 j).property.1,(w.2.2.2.2.1 j).property.2.2.1,
          (w.2.2.2.2.1 j).property.2.2.2.2⟩)
        (fun j => ⟨(w.2.2.2.2.2 j).property.1,(w.2.2.2.2.2 j).property.2.2.1,
          (w.2.2.2.2.2 j).property.2.2.2.2⟩)⟩), by
    intro j
    refine Fin.addCases (fun j _ => ?_) (fun j => ?_) j
    · simp [coded_boundary]
    · refine Fin.cases (fun hj => (hj rfl).elim) (fun _ _ => by simp [coded_boundary]) j⟩
  invFun w := ⟨⟨(w.val.1.val.p,w.val.1.val.q),w.val.1.property.1,
      w.val.1.property.2.1,w.val.1.property.2.2.1⟩,
    ⟨(w.val.2.val.p,w.val.2.val.q),w.val.2.property.1,
      w.val.2.property.2.1,w.val.2.property.2.2.1⟩,
    (fun i => ⟨w.val.1.val.v i,w.val.1.property.2.2.2.2.2.1 i, by
      rw [← w.val.1.property.2.2.2.1]
      exact Ne.symm (w.val.1.property.2.2.2.2.2.2.2.2 i (pivot c d))⟩),
    (fun i => ⟨w.val.2.val.v i,w.val.2.property.2.2.2.2.2.1 i, by
      rw [← w.val.2.property.2.2.2.1]
      exact Ne.symm (w.val.2.property.2.2.2.2.2.2.2.2 i (pivot c d))⟩),
    (fun j => ⟨w.val.1.val.h (j.castAdd (d + 1)),
      w.val.1.property.2.2.2.2.1 _,
      w.val.1.property.2.2.2.2.2.2.1 _ (by simp [pivot, Fin.lt_def]), by
      rw [w.property _ (by simp [pivot, Fin.ext_iff]; omega)]
      exact w.val.2.property.2.2.2.2.2.2.1 _ (by simp [pivot, Fin.lt_def]),
      fun i => w.val.1.property.2.2.2.2.2.2.2.2 i _, by
      intro i
      rw [w.property _ (by simp [pivot, Fin.ext_iff]; omega)]
      exact w.val.2.property.2.2.2.2.2.2.2.2 i _⟩),
    (fun j => ⟨w.val.1.val.h (j.succ.natAdd c),
      w.val.1.property.2.2.2.2.1 _,
      w.val.1.property.2.2.2.2.2.2.2.1 _ (by simp [pivot, Fin.lt_def]), by
      rw [w.property _ (by simp [pivot, Fin.ext_iff])]
      exact w.val.2.property.2.2.2.2.2.2.2.1 _ (by simp [pivot, Fin.lt_def]),
      fun i => w.val.1.property.2.2.2.2.2.2.2.2 i _, by
      intro i
      rw [w.property _ (by simp [pivot, Fin.ext_iff])]
      exact w.val.2.property.2.2.2.2.2.2.2.2 i _⟩)⟩
  left_inv w := by
    rcases w with ⟨x,y,u,v,l,r⟩
    simp [coded_boundary]
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply BoundaryData.ext
      · rfl
      · rfl
      · funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp [coded_boundary]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa [coded_boundary, pivot] using w.val.1.property.2.2.2.1.symm
          · simp [coded_boundary]
      · rfl
    · apply Subtype.ext
      apply BoundaryData.ext
      · rfl
      · rfl
      · funext j
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa [coded_boundary] using w.property (j.castAdd (d + 1))
            (by simp [pivot, Fin.ext_iff]; omega)
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa [coded_boundary, pivot] using w.val.2.property.2.2.2.1.symm
          · simpa [coded_boundary] using w.property (j.succ.natAdd c)
              (by simp [pivot, Fin.ext_iff])
      · rfl

set_option synthInstance.maxSize 2048 in
/-- An exact interior count as independent horizontal alphabet sizes over vertical words. -/
theorem interior_count_alphabets (a b c d : ℕ) :
    N_e (.H (cut_row (a + 1) (b + 1)) (pivot c d) :
      Edge ((a + 1) + (b + 1) + 1) (c + (d + 1) + 1)) =
      ∑ x : NZPair, ∑ y : NZPair,
        ∑ u : Fin a → OrdinaryAlphabet x, ∑ v : Fin b → OrdinaryAlphabet y,
          Nat.card (InteriorAlphabet x y u v x.val.1 y.val.1) ^ c *
          Nat.card (InteriorAlphabet x y u v x.val.2 y.val.2) ^ d := by
  classical
  unfold N_e
  rw [Nat.card_congr (interior_slot_equiv a b _ (pivot c d)),
    ← Nat.card_congr (interior_code_equiv a b c d)]
  let _ : Fintype (InteriorCode a b c d) := inferInstance
  simp only [InteriorCode, Nat.card_eq_fintype_card, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

def word_support {n : ℕ} (u : Fin n → Bool) : Finset Bool := Finset.univ.image u

theorem word_support_empty {n : ℕ} (u : Fin n → Bool) :
    word_support u = ∅ ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have i : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
    have hm : u i ∈ word_support u := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [h] at hm
    exact Finset.notMem_empty _ hm
  · intro h
    subst n
    simp [word_support]

theorem word_support_singleton {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) (b : Bool) :
    word_support u = {b} ↔ u = (fun _ => b) := by
  constructor
  · intro h
    funext i
    have hm : u i ∈ word_support u := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [h] at hm
    exact Finset.mem_singleton.mp hm
  · intro h
    subst u
    let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    exact Finset.image_const ⟨⟨0,hn⟩,Finset.mem_univ _⟩ b

theorem word_support_full {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) :
    word_support u = Finset.univ ↔
      u ≠ (fun _ => false) ∧ u ≠ (fun _ => true) := by
  constructor
  · intro h
    constructor <;> intro hu
    · have he := (word_support_singleton hn u false).mpr hu
      rw [h] at he
      exact (by decide : (Finset.univ : Finset Bool) ≠ {false}) he
    · have he := (word_support_singleton hn u true).mpr hu
      rw [h] at he
      exact (by decide : (Finset.univ : Finset Bool) ≠ {true}) he
  · rintro ⟨hf,ht⟩
    apply Finset.eq_univ_of_forall
    intro b
    by_contra hb
    have hne (i : Fin n) : u i ≠ b := by
      intro he
      apply hb
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
    cases b
    · apply ht
      funext i
      cases hi : u i
      · exact (hne i hi).elim
      · rfl
    · apply hf
      funext i
      cases hi : u i
      · rfl
      · exact (hne i hi).elim

def support_weight (n : ℕ) (S : Finset Bool) : ℕ :=
  if n = 0 then (if S = ∅ then 1 else 0)
  else if S = ∅ then 0 else if S = {false} ∨ S = {true} then 1 else 2 ^ n - 2

theorem word_support_card (n : ℕ) (S : Finset Bool) :
    Nat.card {u : Fin n → Bool // word_support u = S} = support_weight n S := by
  classical
  by_cases hn : n = 0
  · subst n
    have he (u : Fin 0 → Bool) : word_support u = ∅ := (word_support_empty u).mpr rfl
    by_cases hS : S = ∅
    · subst S
      simp [support_weight, he, Nat.card_eq_fintype_card]
    · let _ : IsEmpty {u : Fin 0 → Bool // word_support u = S} :=
        ⟨fun u => hS (u.property.symm.trans (he u.val))⟩
      simp [support_weight, hS]
  · have hn' := Nat.pos_of_ne_zero hn
    have casesS : S = ∅ ∨ S = {false} ∨ S = {true} ∨ S = Finset.univ := by
      revert S
      decide
    rcases casesS with rfl | rfl | rfl | rfl
    · simp [word_support_empty, hn, support_weight, Nat.card_eq_fintype_card]
    · simp [word_support_singleton hn', support_weight, hn, Nat.card_eq_fintype_card]
    · simp [word_support_singleton hn', support_weight, hn, Nat.card_eq_fintype_card]
    · simp only [word_support_full hn', Nat.card_eq_fintype_card]
      have hft : (fun _ : Fin n => false) ≠ (fun _ => true) := by
        intro h
        have := congrFun h ⟨0,hn'⟩
        contradiction
      have h := Fintype.card_subtype_compl
        (fun u : Fin n → Bool => u = (fun _ => false) ∨ u = (fun _ => true))
      rw [Fintype.card_subtype_eq_or_eq_of_ne hft] at h
      have hw : support_weight n Finset.univ = 2 ^ n - 2 := by
        unfold support_weight
        rw [ite_eq_right hn, ite_eq_right (by decide), ite_eq_right (by decide)]
      rw [hw]
      simpa only [not_or, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h

theorem sum_by_support (n : ℕ) (f : Finset Bool → ℕ) :
    (∑ u : Fin n → Bool, f (word_support u)) =
      ∑ S : Finset Bool, support_weight n S * f S := by
  classical
  have h := Equiv.sum_comp (Equiv.sigmaFiberEquiv (@word_support n))
    (fun u => f (word_support u))
  rw [Fintype.sum_sigma] at h
  calc
    _ = ∑ S : Finset Bool, ∑ u : {u : Fin n → Bool // word_support u = S},
        f (word_support u.val) := h.symm
    _ = ∑ S : Finset Bool, Nat.card {u : Fin n → Bool // word_support u = S} * f S := by
      apply Finset.sum_congr rfl
      intro S _
      have he : (fun u : {u : Fin n → Bool // word_support u = S} => f (word_support u.val)) =
          (fun _ => f S) := funext fun u => congrArg f u.property
      rw [he]
      simp [Nat.card_eq_fintype_card]
    _ = _ := by simp_rw [word_support_card]

def ordinary_value (x : NZPair) (b : Bool) : K := if b then x.val.2 else x.val.1

theorem ordinary_value_valid (x : NZPair) (b : Bool) :
    ordinary_value x b ≠ 0 ∧ ordinary_value x b ≠ x.val.1 + x.val.2 := by
  have h : ∀ x : NZPair, ∀ b : Bool,
      ordinary_value x b ≠ 0 ∧ ordinary_value x b ≠ x.val.1 + x.val.2 := by decide
  exact h x b

noncomputable def ordinary_equiv (x : NZPair) : Bool ≃ OrdinaryAlphabet x :=
  Equiv.ofBijective (fun b => ⟨ordinary_value x b,ordinary_value_valid x b⟩) (by
    constructor
    · intro b b' he
      have he := congrArg Subtype.val he
      cases b <;> cases b' <;> simp_all [ordinary_value, x.property.2.2, Ne.symm x.property.2.2]
    · have h : ∀ x : NZPair, ∀ z : OrdinaryAlphabet x,
          ∃ b : Bool, ordinary_value x b = z.val := by decide
      intro z
      obtain ⟨b,hb⟩ := h x z
      exact ⟨b,Subtype.ext hb⟩)

abbrev SupportAlphabet (x y : NZPair) (S T : Finset Bool) (p q : K) :=
  {h : K // h ≠ 0 ∧ h ≠ p ∧ h ≠ q ∧
    (∀ z ∈ S, h ≠ ordinary_value x z) ∧ ∀ z ∈ T, h ≠ ordinary_value y z}

theorem support_alphabet_card {a b : ℕ} (x y : NZPair)
    (u : Fin a → Bool) (v : Fin b → Bool) (p q : K) :
    Nat.card (InteriorAlphabet x y (fun i => ordinary_equiv x (u i))
      (fun i => ordinary_equiv y (v i)) p q) =
      Nat.card (SupportAlphabet x y (word_support u) (word_support v) p q) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro h
  simp [word_support, ordinary_equiv, Equiv.ofBijective]

noncomputable def pair_support_count (a b c d : ℕ) (x y : NZPair) : ℕ :=
  ∑ S : Finset Bool, ∑ T : Finset Bool,
    support_weight a S * support_weight b T *
      Nat.card (SupportAlphabet x y S T x.val.1 y.val.1) ^ c *
      Nat.card (SupportAlphabet x y S T x.val.2 y.val.2) ^ d

theorem pair_count_support (a b c d : ℕ) (x y : NZPair) :
    (∑ u : Fin a → OrdinaryAlphabet x, ∑ v : Fin b → OrdinaryAlphabet y,
      Nat.card (InteriorAlphabet x y u v x.val.1 y.val.1) ^ c *
      Nat.card (InteriorAlphabet x y u v x.val.2 y.val.2) ^ d) =
        pair_support_count a b c d x y := by
  classical
  let eu : (Fin a → Bool) ≃ (Fin a → OrdinaryAlphabet x) :=
    Equiv.arrowCongr (Equiv.refl _) (ordinary_equiv x)
  let ev : (Fin b → Bool) ≃ (Fin b → OrdinaryAlphabet y) :=
    Equiv.arrowCongr (Equiv.refl _) (ordinary_equiv y)
  calc
    _ = ∑ u : Fin a → Bool, ∑ v : Fin b → Bool,
        Nat.card (SupportAlphabet x y (word_support u) (word_support v) x.val.1 y.val.1) ^ c *
        Nat.card (SupportAlphabet x y (word_support u) (word_support v) x.val.2 y.val.2) ^ d := by
      symm
      apply Fintype.sum_equiv eu
      intro u
      apply Fintype.sum_equiv ev
      intro v
      simpa [eu,ev,Equiv.arrowCongr, Function.comp_def] using (congrArg₂ (fun L R : ℕ => L^c*R^d)
        (support_alphabet_card x y u v x.val.1 y.val.1)
        (support_alphabet_card x y u v x.val.2 y.val.2)).symm
    _ = _ := by
      have hs (u : Fin a → Bool) := sum_by_support b
        (fun T => Nat.card (SupportAlphabet x y (word_support u) T x.val.1 y.val.1)^c *
          Nat.card (SupportAlphabet x y (word_support u) T x.val.2 y.val.2)^d)
      simp_rw [hs]
      rw [sum_by_support a (fun S => ∑ T : Finset Bool, support_weight b T *
        (Nat.card (SupportAlphabet x y S T x.val.1 y.val.1)^c *
          Nat.card (SupportAlphabet x y S T x.val.2 y.val.2)^d))]
      unfold pair_support_count
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
