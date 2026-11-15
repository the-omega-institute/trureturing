/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Interior slot equivalences and alphabet/support encodings. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229571.result, HardinA229573.result, HardinA229574.result, HardinA229575.result, HardinA229576.result, HardinA229577.result, HardinA229578.result)
InteriorSlots: proof_shape=bind-only; consumers=KingHorizontal.cut_slots_equiv,KingHorizontal.interiorDecode,KingHorizontal.interiorEncode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_code_equiv,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_one_column_count,KingHorizontal.interior_slot_equiv
boundary_top_shared: proof_shape=bind-only; consumers=KingHorizontal.boundary_bottom_shared,KingHorizontal.cut_slots_equiv
boundary_bottom_shared: proof_shape=bind-only; consumers=KingHorizontal.cut_slots_equiv
cut_slots_equiv: proof_shape=bind-only; consumers=KingHorizontal.interior_slot_equiv
interior_slot_equiv: proof_shape=bind-only; consumers=KingHorizontal.interior_count_alphabets,KingHorizontal.interior_one_column_count
OrdinaryAlphabet: proof_shape=bind-only; consumers=KingHorizontal.InteriorAlphabet,KingHorizontal.InteriorCode,KingHorizontal.coded_boundaries_shared,KingHorizontal.coded_boundary,KingHorizontal.coded_boundary_left,KingHorizontal.coded_boundary_right,KingHorizontal.coded_boundary_valid,KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode,KingHorizontal.interiorDecode_encode,KingHorizontal.interiorEncode,KingHorizontal.interiorFirstPair,KingHorizontal.interiorFirstWord,KingHorizontal.interiorLeftWord,KingHorizontal.interiorRightWord,KingHorizontal.interiorSecondPair,KingHorizontal.interiorSecondWord,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.ordinary_equiv,KingHorizontal.pair_count_support,KingHorizontal.support_alphabet_card
InteriorAlphabet: proof_shape=bind-only; consumers=KingHorizontal.InteriorCode,KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode,KingHorizontal.interiorDecode_encode,KingHorizontal.interiorEncode,KingHorizontal.interiorFirstPair,KingHorizontal.interiorFirstWord,KingHorizontal.interiorLeftWord,KingHorizontal.interiorRightWord,KingHorizontal.interiorSecondPair,KingHorizontal.interiorSecondWord,KingHorizontal.interior_count_alphabets,KingHorizontal.interior_count_support,KingHorizontal.pair_count_support,KingHorizontal.support_alphabet_card
InteriorCode: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode,KingHorizontal.interiorDecode_encode,KingHorizontal.interiorEncode,KingHorizontal.interiorFirstPair,KingHorizontal.interiorFirstWord,KingHorizontal.interiorLeftWord,KingHorizontal.interiorRightWord,KingHorizontal.interiorSecondPair,KingHorizontal.interiorSecondWord,KingHorizontal.interior_code_equiv,KingHorizontal.interior_count_alphabets
coded_boundary: proof_shape=bind-only; consumers=KingHorizontal.coded_boundaries_shared,KingHorizontal.coded_boundary_left,KingHorizontal.coded_boundary_right,KingHorizontal.coded_boundary_valid,KingHorizontal.interiorEncode
coded_boundary_valid: proof_shape=bind-only; consumers=KingHorizontal.interiorEncode
coded_boundary_left: proof_shape=bind-only; consumers=KingHorizontal.coded_boundaries_shared,KingHorizontal.interiorDecode_encode
coded_boundary_right: proof_shape=bind-only; consumers=KingHorizontal.coded_boundaries_shared,KingHorizontal.interiorDecode_encode
coded_boundaries_shared: proof_shape=bind-only; consumers=KingHorizontal.interiorEncode
interiorEncode: proof_shape=bind-only; consumers=KingHorizontal.interiorDecode_encode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_code_equiv
interiorDecode: proof_shape=bind-only; consumers=KingHorizontal.interiorDecode_encode,KingHorizontal.interiorEncode_decode,KingHorizontal.interior_code_equiv
interiorFirstPair: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode_encode
interiorSecondPair: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode_encode
interiorFirstWord: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode_encode
interiorSecondWord: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext,KingHorizontal.interiorDecode_encode
interiorLeftWord: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext
interiorRightWord: proof_shape=bind-only; consumers=KingHorizontal.interiorCode_ext
interiorCode_ext: proof_shape=bind-only; consumers=KingHorizontal.interiorDecode_encode
interiorDecode_encode: proof_shape=bind-only; consumers=KingHorizontal.interior_code_equiv
interiorEncode_decode: proof_shape=bind-only; consumers=KingHorizontal.interior_code_equiv
interior_code_equiv: proof_shape=bind-only; consumers=KingHorizontal.interior_count_alphabets
interior_count_alphabets: proof_shape=bind-only; consumers=KingHorizontal.interior_count_support
word_support: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support,KingHorizontal.sum_by_support,KingHorizontal.support_alphabet_card,KingHorizontal.word_support_card,KingHorizontal.word_support_empty,KingHorizontal.word_support_full,KingHorizontal.word_support_singleton
word_support_empty: proof_shape=bind-only; consumers=KingHorizontal.word_support_card
word_support_singleton: proof_shape=bind-only; consumers=KingHorizontal.word_support_card,KingHorizontal.word_support_full
word_support_full: proof_shape=bind-only; consumers=KingHorizontal.word_support_card
support_weight: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support,KingHorizontal.pair_support_cases,KingHorizontal.pair_support_count,KingHorizontal.sum_by_support,KingHorizontal.support_case_count,KingHorizontal.support_case_eval,KingHorizontal.word_support_card
word_support_card: proof_shape=bind-only; consumers=KingHorizontal.sum_by_support
sum_by_support: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support
ordinary_value: proof_shape=bind-only; consumers=KingHorizontal.SupportAlphabet,KingHorizontal.ordinary_equiv,KingHorizontal.ordinary_value_valid,KingHorizontal.pair_count_support,KingHorizontal.support_alphabet_card,KingHorizontal.support_sizes_correct
ordinary_value_valid: proof_shape=bind-only; consumers=KingHorizontal.ordinary_equiv
ordinary_equiv: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support,KingHorizontal.support_alphabet_card
SupportAlphabet: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support,KingHorizontal.pair_support_cases,KingHorizontal.pair_support_count,KingHorizontal.support_alphabet_card,KingHorizontal.support_sizes_correct
support_alphabet_card: proof_shape=bind-only; consumers=KingHorizontal.pair_count_support
pair_support_count: proof_shape=bind-only; consumers=KingHorizontal.interior_count,KingHorizontal.interior_count_support,KingHorizontal.pair_count_support,KingHorizontal.pair_support_cases
pair_count_support: proof_shape=bind-only; consumers=KingHorizontal.interior_count_support
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

private theorem boundary_top_shared {m M : ℕ} (s : Fin M)
    (t : {t : DiffField (m + 1) M // RawAdmissible (.H 0 s) t}) (j : Fin M) (hj : j ≠ s) :
    (boundary_slot_equiv m M s t).val.h j = t.val.h 0 j := by
  simpa [boundary_slot_equiv, boundary_extract, hj] using (boundary_h s t.val t.property 0 j).symm

private theorem boundary_bottom_shared {m M : ℕ} (s : Fin M)
    (t : {t : DiffField (m + 1) M // RawAdmissible (.H (Fin.last (m + 1)) s) t})
    (j : Fin M) (hj : j ≠ s) :
    (boundary_bottom_slot_equiv m M s t).val.h j = t.val.h (Fin.last (m + 1)) j := by
  have ht : RawAdmissible (.H 0 s) (row_reflect t.val) := by
    simpa using row_reflect_raw (Fin.last (m + 1)) s t.val t.property
  have h := boundary_top_shared s ⟨row_reflect t.val,ht⟩ j hj
  simpa [boundary_bottom_slot_equiv, row_reflect_equiv, row_reflect,
    Equiv.subtypeEquivRight, Equiv.subtypeEquiv, boundary_slot_equiv, boundary_extract] using h

private def cut_slots_equiv (a b M : ℕ) (s : Fin M) :
    CutFields (a+1) (b+1) M s ≃ InteriorSlots a b M s := by
  let A := {t : DiffField (a+1) M // RawAdmissible (.H (Fin.last (a+1)) s) t}
  let B := {t : DiffField (b+1) M // RawAdmissible (.H 0 s) t}
  let joinCompat (q : A × B) : Prop := ∀ j, q.1.val.h (Fin.last (a+1)) j = q.2.val.h 0 j
  let E : CutFields (a+1) (b+1) M s ≃ {q : A × B // joinCompat q} :=
    (Equiv.subtypeEquivRight (fun _ => and_assoc.symm)).trans ((Equiv.subtypeSubtypeEquivSubtypeInter
      (fun q : DiffField (a+1) M × DiffField (b+1) M =>
        RawAdmissible (.H (Fin.last (a+1)) s) q.1 ∧ RawAdmissible (.H 0 s) q.2)
      (fun q => ∀ j, q.1.h (Fin.last (a+1)) j = q.2.h 0 j)).symm.trans
      (Equiv.subtypeProdEquivProd.subtypeEquiv (q := joinCompat) (by intro q; rfl)))
  exact E.trans ((Equiv.prodCongr (boundary_bottom_slot_equiv a M s)
    (boundary_slot_equiv b M s)).subtypeEquiv (by
      intro q
      change joinCompat q ↔ ∀ j, j ≠ s →
        (boundary_bottom_slot_equiv a M s q.1).val.h j =
          (boundary_slot_equiv b M s q.2).val.h j
      constructor
      · intro h j hj
        rw [boundary_bottom_shared s _ j hj, boundary_top_shared s _ j hj]
        exact h j
      · intro h j
        by_cases hj : j = s
        · subst j
          exact (q.1.property.2 _ |>.mpr rfl).trans (q.2.property.2 _ |>.mpr rfl).symm
        · have hh := h j hj
          rw [boundary_bottom_shared s _ j hj, boundary_top_shared s _ j hj] at hh
          exact hh))

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
private def InteriorCode (a b c d : ℕ) :=
  Σ x : NZPair, Σ y : NZPair,
    Σ u : Fin a → OrdinaryAlphabet x, Σ v : Fin b → OrdinaryAlphabet y,
      (Fin c → InteriorAlphabet x y u v x.val.1 y.val.1) ×
      (Fin d → InteriorAlphabet x y u v x.val.2 y.val.2)

private def coded_boundary {m c d : ℕ} (x : NZPair)
    (u : Fin m → OrdinaryAlphabet x) (l : Fin c → K) (r : Fin d → K) :
    BoundaryData m (c + (d + 1)) where
  p := x.val.1
  q := x.val.2
  h := Fin.addCases l (Fin.cases (x.val.1 + x.val.2) r)
  v i := (u i).val

private theorem coded_boundary_valid {m c d : ℕ} (x : NZPair)
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

private theorem coded_boundary_left {m c d : ℕ} (x : NZPair)
    (u : Fin m → OrdinaryAlphabet x) (l : Fin c → K) (r : Fin d → K) (j : Fin c) :
    (coded_boundary x u l r).h (j.castAdd (d + 1)) = l j := by
  simp only [coded_boundary, Fin.addCases_left]

private theorem coded_boundary_right {m c d : ℕ} (x : NZPair)
    (u : Fin m → OrdinaryAlphabet x) (l : Fin c → K) (r : Fin d → K) (j : Fin d) :
    (coded_boundary x u l r).h (j.succ.natAdd c) = r j := by
  simp only [coded_boundary, Fin.addCases_right, Fin.cases_succ]

private theorem coded_boundaries_shared {a b c d : ℕ} (x y : NZPair)
    (u : Fin a → OrdinaryAlphabet x) (v : Fin b → OrdinaryAlphabet y)
    (l : Fin c → K) (r : Fin d → K) :
    ∀ j, j ≠ pivot c d → (coded_boundary x u l r).h j =
      (coded_boundary y v l r).h j := by
  intro j
  refine Fin.addCases (fun j _ => ?_) (fun j => ?_) j
  · rw [coded_boundary_left, coded_boundary_left]
  · refine Fin.cases (fun hj => (hj rfl).elim) (fun j _ => ?_) j
    rw [coded_boundary_right, coded_boundary_right]

private def interiorEncode {a b c d : ℕ} (w : InteriorCode a b c d) :
    InteriorSlots a b (c + (d + 1)) (pivot c d) := by
  rcases w with ⟨x,y,u,v,l,r⟩
  refine ⟨(
    ⟨coded_boundary x u (fun j => (l j).val) (fun j => (r j).val),
      coded_boundary_valid _ _ _ _
        (fun j => ⟨(l j).property.1,(l j).property.2.1,
          (l j).property.2.2.2.1⟩)
        (fun j => ⟨(r j).property.1,(r j).property.2.1,
          (r j).property.2.2.2.1⟩)⟩,
    ⟨coded_boundary y v (fun j => (l j).val) (fun j => (r j).val),
      coded_boundary_valid _ _ _ _
        (fun j => ⟨(l j).property.1,(l j).property.2.2.1,
          (l j).property.2.2.2.2⟩)
        (fun j => ⟨(r j).property.1,(r j).property.2.2.1,
          (r j).property.2.2.2.2⟩)⟩), coded_boundaries_shared x y u v
      (fun j => (l j).val) (fun j => (r j).val)⟩

private def interiorDecode {a b c d : ℕ}
    (w : InteriorSlots a b (c + (d + 1)) (pivot c d)) : InteriorCode a b c d := by
  rcases w with ⟨⟨⟨b₁,hb₁⟩,⟨b₂,hb₂⟩⟩,hshared⟩
  rcases hb₁ with ⟨hp₁,hq₁,hpq₁,hs₁,hh₁,hv₁,hl₁,hr₁,hcross₁⟩
  rcases hb₂ with ⟨hp₂,hq₂,hpq₂,hs₂,hh₂,hv₂,hl₂,hr₂,hcross₂⟩
  have hu₁ (i : Fin a) : b₁.v i ≠ b₁.p + b₁.q := by
    intro he
    exact hcross₁ i _ (hs₁.trans he.symm)
  have hu₂ (i : Fin b) : b₂.v i ≠ b₂.p + b₂.q := by
    intro he
    exact hcross₂ i _ (hs₂.trans he.symm)
  have hleft (j : Fin c) : j.castAdd (d + 1) < pivot c d := by
    simp [pivot, Fin.lt_def]
  have hright (j : Fin d) : pivot c d < j.succ.natAdd c := by
    simp [pivot, Fin.lt_def]
  have hleft_ne (j : Fin c) : j.castAdd (d + 1) ≠ pivot c d := ne_of_lt (hleft j)
  have hright_ne (j : Fin d) : j.succ.natAdd c ≠ pivot c d := ne_of_gt (hright j)
  refine ⟨⟨(b₁.p,b₁.q),hp₁,hq₁,hpq₁⟩, ⟨(b₂.p,b₂.q),hp₂,hq₂,hpq₂⟩,
    (fun i => ⟨b₁.v i,hv₁ i,hu₁ i⟩), (fun i => ⟨b₂.v i,hv₂ i,hu₂ i⟩),
    (fun j => ⟨b₁.h (j.castAdd (d + 1)), hh₁ _, hl₁ _ (hleft j), ?_, ?_, ?_⟩),
    (fun j => ⟨b₁.h (j.succ.natAdd c), hh₁ _, hr₁ _ (hright j), ?_, ?_, ?_⟩)⟩
  · intro he
    exact hl₂ _ (hleft j) ((hshared _ (hleft_ne j)).symm.trans he)
  · intro i
    exact hcross₁ i _
  · intro i
    exact fun he => hcross₂ i _ ((hshared _ (hleft_ne j)).symm.trans he)
  · intro he
    exact hr₂ _ (hright j) ((hshared _ (hright_ne j)).symm.trans he)
  · intro i
    exact hcross₁ i _
  · intro i
    exact fun he => hcross₂ i _ ((hshared _ (hright_ne j)).symm.trans he)

private def interiorFirstPair {a b c d : ℕ} (w : InteriorCode a b c d) : NZPair := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact x

private def interiorSecondPair {a b c d : ℕ} (w : InteriorCode a b c d) : NZPair := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact y

private def interiorFirstWord {a b c d : ℕ} (w : InteriorCode a b c d) : Fin a → K := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact fun i => (u i).val

private def interiorSecondWord {a b c d : ℕ} (w : InteriorCode a b c d) : Fin b → K := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact fun i => (v i).val

private def interiorLeftWord {a b c d : ℕ} (w : InteriorCode a b c d) : Fin c → K := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact fun i => (l i).val

private def interiorRightWord {a b c d : ℕ} (w : InteriorCode a b c d) : Fin d → K := by
  rcases w with ⟨x,y,u,v,l,r⟩
  exact fun i => (r i).val

private theorem interiorCode_ext {a b c d : ℕ} {w z : InteriorCode a b c d}
    (hx : interiorFirstPair w = interiorFirstPair z)
    (hy : interiorSecondPair w = interiorSecondPair z)
    (hu : ∀ i, interiorFirstWord w i = interiorFirstWord z i)
    (hv : ∀ i, interiorSecondWord w i = interiorSecondWord z i)
    (hl : ∀ i, interiorLeftWord w i = interiorLeftWord z i)
    (hr : ∀ i, interiorRightWord w i = interiorRightWord z i) : w = z := by
  rcases w with ⟨x,y,u,v,l,r⟩
  rcases z with ⟨x',y',u',v',l',r'⟩
  change x = x' at hx
  change y = y' at hy
  cases hx
  cases hy
  have eu : u = u' := funext fun i => Subtype.ext (hu i)
  have ev : v = v' := funext fun i => Subtype.ext (hv i)
  cases eu
  cases ev
  have el : l = l' := funext fun i => Subtype.ext (hl i)
  have er : r = r' := funext fun i => Subtype.ext (hr i)
  cases el
  cases er
  rfl

private theorem interiorDecode_encode {a b c d : ℕ} (w : InteriorCode a b c d) :
    interiorDecode (interiorEncode w) = w := by
  rcases w with ⟨x,y,u,v,l,r⟩
  apply interiorCode_ext
  · rfl
  · rfl
  · intro i; rfl
  · intro i; rfl
  · intro j
    exact coded_boundary_left x u (fun k => (l k).val) (fun k => (r k).val) j
  · intro j
    exact coded_boundary_right x u (fun k => (l k).val) (fun k => (r k).val) j

private theorem interiorEncode_decode {a b c d : ℕ}
    (w : InteriorSlots a b (c + (d + 1)) (pivot c d)) :
    interiorEncode (interiorDecode w) = w := by
  rcases w with ⟨⟨⟨b₁,hb₁⟩,⟨b₂,hb₂⟩⟩,hshared⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply BoundaryData.ext
    · rfl
    · rfl
    · funext j
      change Fin.addCases (fun k => b₁.h (k.castAdd (d + 1)))
        (Fin.cases (b₁.p + b₁.q) (fun k => b₁.h (k.succ.natAdd c))) j = b₁.h j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
        refine Fin.cases ?_ (fun j => ?_) j
        · exact hb₁.2.2.2.1.symm
        · rw [Fin.cases_succ]
    · rfl
  · apply Subtype.ext
    apply BoundaryData.ext
    · rfl
    · rfl
    · funext j
      change Fin.addCases (fun k => b₁.h (k.castAdd (d + 1)))
        (Fin.cases (b₂.p + b₂.q) (fun k => b₁.h (k.succ.natAdd c))) j = b₂.h j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.addCases_left]
        exact hshared _ (ne_of_lt (by simp [pivot, Fin.lt_def]))
      · rw [Fin.addCases_right]
        refine Fin.cases ?_ (fun j => ?_) j
        · exact hb₂.2.2.2.1.symm
        · rw [Fin.cases_succ]
          exact hshared _ (ne_of_gt (by simp [pivot, Fin.lt_def]))
    · rfl

/-- A direct four-word version of the interior slot classification. -/
private def interior_code_equiv (a b c d : ℕ) :
    InteriorCode a b c d ≃ InteriorSlots a b (c + (d + 1)) (pivot c d) where
  toFun := interiorEncode
  invFun := interiorDecode
  left_inv := interiorDecode_encode
  right_inv := interiorEncode_decode

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
  let _ : Fintype (InteriorCode a b c d) := by unfold InteriorCode; infer_instance
  simp only [InteriorCode, Nat.card_eq_fintype_card, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

def word_support {n : ℕ} (u : Fin n → Bool) : Finset Bool := Finset.univ.image u

theorem word_support_empty {n : ℕ} (u : Fin n → Bool) :
    word_support u = ∅ ↔ n = 0 := by
  unfold word_support
  rw [Finset.image_eq_empty]
  constructor
  · intro h
    simpa using congrArg Finset.card h
  · rintro rfl
    exact Finset.univ_eq_empty

theorem word_support_singleton {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) (b : Bool) :
    word_support u = {b} ↔ u = (fun _ => b) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  rw [← Finset.coe_inj]
  simpa [word_support, funext_iff] using (Set.range_eq_singleton_iff (f := u) (y := b))

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
  have h := Fintype.sum_fiberwise' (@word_support n) f
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, word_support_card] using h.symm

def ordinary_value (x : NZPair) (b : Bool) : K := if b then x.val.2 else x.val.1

theorem ordinary_value_valid (x : NZPair) (b : Bool) :
    ordinary_value x b ≠ 0 ∧ ordinary_value x b ≠ x.val.1 + x.val.2 := by
  have h : ∀ x : NZPair, ∀ b : Bool,
      ordinary_value x b ≠ 0 ∧ ordinary_value x b ≠ x.val.1 + x.val.2 := by decide
  exact h x b

private noncomputable def ordinary_equiv (x : NZPair) : Bool ≃ OrdinaryAlphabet x :=
  Equiv.ofBijective (fun b => ⟨ordinary_value x b,ordinary_value_valid x b⟩) (by
    constructor
    · intro b b' he
      have hi : Function.Injective (fun b : Bool => if b then x.val.2 else x.val.1) := by
        simpa using (Bool.injective_iff
          (f := fun b : Bool => if b then x.val.2 else x.val.1)).mpr x.property.2.2
      exact hi (congrArg Subtype.val he)
    · have h : ∀ x : NZPair, ∀ z : OrdinaryAlphabet x,
          ∃ b : Bool, ordinary_value x b = z.val := by decide
      intro z
      obtain ⟨b,hb⟩ := h x z
      exact ⟨b,Subtype.ext hb⟩)

abbrev SupportAlphabet (x y : NZPair) (S T : Finset Bool) (p q : K) :=
  {h : K // h ≠ 0 ∧ h ≠ p ∧ h ≠ q ∧
    (∀ z ∈ S, h ≠ ordinary_value x z) ∧ ∀ z ∈ T, h ≠ ordinary_value y z}

private theorem support_alphabet_card {a b : ℕ} (x y : NZPair)
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
