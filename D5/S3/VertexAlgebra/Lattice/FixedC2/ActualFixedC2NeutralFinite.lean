/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-dimensional neutral image in the intrinsic Leech fixed C₂ quotient. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPower
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralGenerators
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeSugawaraConformal LatticeInvolution MvPolynomial
open ActualLeechHyperbolic (leechData)
open private even_cons_cons from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
open private neutral_class_length_le neutral_word_nil from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralGenerators

noncomputable section

local instance neutralFiniteFixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

private theorem word_class_perm (D : LatticeData) {u v : List (Index D)}
    (h : u.Perm v) (hu : Even u.length) (hv : Even v.length) :
    neutralWordClass D u hu = neutralWordClass D v hv := by
  have hpoly : neutralPolynomial D u = neutralPolynomial D v :=
    (h.map (fun t => (X t : Oscillator D))).prod_eq
  have hwords : fixedNeutralWord D u hu = fixedNeutralWord D v hv :=
    Subtype.ext (congrArg (Finsupp.single (0 : Charge D)) hpoly)
  exact congrArg (fun a : FixedCarrier D => (fixedC2 D).mkQ a) hwords

private theorem class_length_le_lt (D : LatticeData) {n k : ℕ} (hn : Even n)
    (h : n < k) : neutralClassLength D n hn ≤ neutralClassLengthLT D k :=
  neutral_class_length_le D n hn _ (fun w hw =>
    Submodule.subset_span ⟨w, hw.symm ▸ hn, hw ▸ h, rfl⟩)

private theorem class_length_lt_mono (D : LatticeData) {n k : ℕ} (h : n ≤ k) :
    neutralClassLengthLT D n ≤ neutralClassLengthLT D k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, hl, rfl⟩
  exact Submodule.subset_span ⟨w, hw, hl.trans_le h, rfl⟩

/-- An exact quadratic equality, with its scalar, replaces any two selected
letters in an even word up to classes of the remaining length. -/
theorem neutral_word_pair_replace (D : LatticeData) (x y x' y' : Index D)
    (w w' rest : List (Index D)) (hw : Even w.length) (hw' : Even w'.length)
    (hr : Even rest.length) (p : w.Perm (x :: y :: rest))
    (p' : w'.Perm (x' :: y' :: rest)) (c : ℂ)
    (he : pairClass D x.1 y.1 x.2 y.2 = c • pairClass D x'.1 y'.1 x'.2 y'.2) :
    neutralWordClass D w hw - c • neutralWordClass D w' hw' ∈
      neutralClassLength D rest.length hr := by
  rw [word_class_perm D p hw (even_cons_cons D x y rest hr),
    word_class_perm D p' hw' (even_cons_cons D x' y' rest hr)]
  have h := fixed_quadratic_word_length D x y rest hr
  rw [he, map_smul, LinearMap.smul_apply] at h
  have h' := (neutralClassLength D rest.length hr).smul_mem c
    (fixed_quadratic_word_length D x' y' rest hr)
  rw [smul_sub] at h'
  simpa only [sub_sub_sub_cancel_left] using
    (neutralClassLength D rest.length hr).sub_mem h' h

/-- Moving the first selected index onto the second preserves the top-length
class with the indicated nonzero signed binomial factor. -/
theorem neutral_word_pair_normalize (D : LatticeData) (i j : Fin D.rank) (a b : ℕ)
    (w w' rest : List (Index D)) (hw : Even w.length) (hw' : Even w'.length)
    (hr : Even rest.length) (p : w.Perm ((i, a) :: (j, b) :: rest))
    (p' : w'.Perm ((i, 0) :: (j, a + b) :: rest)) :
    let c : ℂ := (-1 : ℂ)^a * ((a + b).choose a : ℂ)
    c ≠ 0 ∧ neutralWordClass D w hw - c • neutralWordClass D w' hw' ∈
      neutralClassLength D rest.length hr := by
  refine ⟨mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_, ?_⟩
  · exact_mod_cast (Nat.choose_pos (by omega : a ≤ a + b)).ne'
  · exact neutral_word_pair_replace D _ _ _ _ w w' rest hw hw' hr p p' _
      (pair_class_normalize D i j a b)

private theorem pivot_high (i : Fin leechData.rank) (todo kept : List (Index leechData))
    (b : ℕ) (hw : Even ((i, b) :: (todo ++ kept)).length)
    (hs : 7 ≤ b + (todo.map Prod.snd).sum) :
    neutralWordClass leechData ((i, b) :: (todo ++ kept)) hw ∈
      neutralClassLengthLT leechData ((i, b) :: (todo ++ kept)).length := by
  induction todo generalizing kept b with
  | nil =>
    cases kept with
    | nil => norm_num at hw
    | cons x rest =>
      have hr : Even rest.length := by
        rw [Nat.even_iff] at hw ⊢
        simp only [List.nil_append, List.length_cons] at hw
        omega
      apply class_length_le_lt leechData hr (by simp)
      exact leech_neutral_word_high_pair (i, b) x _ rest hr (List.Perm.refl _) hw
        (by simp at hs; change 7 ≤ b + x.2; omega)
  | cons x todo ih =>
    let rest := todo ++ kept
    let kept' := (x.1, 0) :: kept
    let w := (i, b) :: (x :: todo ++ kept)
    let w' := (i, x.2 + b) :: (todo ++ kept')
    have p : w.Perm (x :: (i, b) :: rest) := List.Perm.swap _ _ _
    have p' : w'.Perm ((x.1, 0) :: (i, x.2 + b) :: rest) :=
      (List.Perm.cons _ List.perm_middle).trans (List.Perm.swap _ _ _)
    have hl : w'.length = w.length := p'.length_eq.trans (by simpa using p.length_eq.symm)
    have hw' : Even w'.length := hl.symm ▸ hw
    have hr : Even rest.length := by
      rw [Nat.even_iff] at hw ⊢
      simp only [List.length_cons, List.cons_append] at hw
      change (todo ++ kept).length % 2 = 0
      omega
    have hshort : rest.length < w.length := by simp [w, rest]
    obtain ⟨_, hreplace⟩ := neutral_word_pair_normalize leechData x.1 i x.2 b
      w w' rest hw hw' hr p p'
    have h' : neutralWordClass leechData w' hw' ∈ neutralClassLengthLT leechData w.length := by
      rw [← hl]
      exact ih kept' (x.2 + b) hw' (by simp only [List.map_cons, List.sum_cons] at hs; omega)
    let S := neutralClassLengthLT leechData w.length
    have ha := class_length_le_lt leechData hr hshort hreplace
    simpa only [sub_add_cancel] using
      S.add_mem ha (S.smul_mem ((-1 : ℂ)^x.2 * ((x.2 + b).choose x.2 : ℂ)) h')

/-- The total zero-based oscillator index is at most six in the leading
length of the neutral image of the actual Leech fixed C₂ quotient. -/
theorem leech_neutral_word_high_total_index (w : List (Index leechData))
    (hw : Even w.length) (hs : 7 ≤ (w.map Prod.snd).sum) :
    neutralWordClass leechData w hw ∈ neutralClassLengthLT leechData w.length := by
  cases w with
  | nil => simp at hs
  | cons x w =>
    simpa only [List.append_nil] using
      pivot_high x.1 w [] x.2 (by simpa only [List.append_nil] using hw)
        (by simpa only [List.map_cons, List.sum_cons] using hs)

attribute [local instance] fixedQuotientRing fixedQuotientAlgebra

private theorem pair_mul_word_length (D : LatticeData) (x y : Index D)
    (w : List (Index D)) (hw : Even w.length) :
    pairClass D x.1 y.1 x.2 y.2 * neutralWordClass D w hw -
      neutralWordClass D (x :: y :: w) (even_cons_cons D x y w hw) ∈
        neutralClassLength D w.length hw :=
  fixed_quadratic_word_length D x y w hw

private theorem pair_mul_short (D : LatticeData) (x y : Index D) {k : ℕ}
    {q : FixedC2Quotient D} (hq : q ∈ neutralClassLengthLT D k) :
    pairClass D x.1 y.1 x.2 y.2 * q ∈ neutralClassLengthLT D (k + 2) := by
  change q ∈ (neutralClassLengthLT D (k + 2)).comap
    (fixedQuotientProduct D (pairClass D x.1 y.1 x.2 y.2))
  refine (Submodule.span_le.mpr ?_) hq
  rintro _ ⟨w, hw, hlen, rfl⟩
  let S := neutralClassLengthLT D (k + 2)
  change pairClass D x.1 y.1 x.2 y.2 * neutralWordClass D w hw ∈ S
  have hlead : neutralWordClass D (x :: y :: w) (even_cons_cons D x y w hw) ∈ S :=
    Submodule.subset_span ⟨x :: y :: w, even_cons_cons D x y w hw, by simp; omega, rfl⟩
  have hcorr := class_length_le_lt D hw (show w.length < k + 2 by omega)
    (pair_mul_word_length D x y w hw)
  simpa only [sub_add_cancel] using S.add_mem hcorr hlead

/-- The product of two neutral words has their concatenation as leading term
in oscillator length in the actual fixed quotient. -/
theorem neutral_word_mul_append (D : LatticeData) (u v : List (Index D))
    (hu : Even u.length) (hv : Even v.length) :
    neutralWordClass D u hu * neutralWordClass D v hv -
      neutralWordClass D (u ++ v) (by simpa only [List.length_append] using hu.add hv) ∈
        neutralClassLengthLT D (u.length + v.length) := by
  suffices h : ∀ n (u : List (Index D)) (hu : Even u.length), u.length = n →
      neutralWordClass D u hu * neutralWordClass D v hv -
        neutralWordClass D (u ++ v) (by simpa only [List.length_append] using hu.add hv) ∈
          neutralClassLengthLT D (u.length + v.length) from h _ u hu rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hu hlen_u
    rcases u with _ | ⟨x, u⟩
    · simp only [List.nil_append, neutral_word_nil, one_mul, sub_self]
      exact Submodule.zero_mem _
    cases u with
    | nil => norm_num at hu
    | cons y u =>
      have hr : Even u.length := by
        rw [Nat.even_iff] at hu ⊢
        simp only [List.length_cons] at hu
        omega
      have hrv : Even (u ++ v).length := by simpa only [List.length_append] using hr.add hv
      let Q := pairClass D x.1 y.1 x.2 y.2
      let U := neutralWordClass D u hr
      let V := neutralWordClass D v hv
      let UV := neutralWordClass D (u ++ v) hrv
      let W := neutralWordClass D (x :: y :: u) hu
      let WV := neutralWordClass D ((x :: y :: u) ++ v)
        (by simpa only [List.length_append] using hu.add hv)
      let S := neutralClassLengthLT D ((x :: y :: u).length + v.length)
      have hlen : (x :: y :: u).length + v.length = (u.length + v.length) + 2 := by
        simp only [List.length_cons]
        omega
      have hshort : u.length < n := by simp only [List.length_cons] at hlen_u; omega
      have h1 : Q * (U * V - UV) ∈ S := by
        change _ ∈ neutralClassLengthLT D _
        rw [hlen]
        exact pair_mul_short D x y (ih u.length hshort u hr rfl)
      have h2 : Q * UV - WV ∈ S :=
        class_length_le_lt D hrv (by simp) (pair_mul_word_length D x y (u ++ v) hrv)
      have h3 : (Q * U - W) * V ∈ S := by
        rw [mul_comm]
        change Q * U - W ∈ S.comap (fixedQuotientProduct D V)
        apply neutral_class_length_le D u.length hr _ _ (pair_mul_word_length D x y u hr)
        intro t ht
        have htEven : Even t.length := ht.symm ▸ hr
        have htShort : t.length < n := ht ▸ hshort
        change V * neutralWordClass D t htEven ∈ S
        rw [mul_comm]
        have htv : Even (t ++ v).length := by simpa only [List.length_append] using htEven.add hv
        have hbelow : t.length + v.length < (x :: y :: u).length + v.length := by
          simp [ht]
        have ha := class_length_lt_mono D hbelow.le (ih t.length htShort t htEven rfl)
        have hb : neutralWordClass D (t ++ v) htv ∈ S :=
          Submodule.subset_span ⟨t ++ v, htv, by simpa only [List.length_append] using hbelow, rfl⟩
        simpa only [sub_add_cancel] using S.add_mem ha hb
      change W * V - WV ∈ S
      rw [show W * V - WV = Q * (U * V - UV) + (Q * UV - WV) - (Q * U - W) * V by ring]
      exact S.sub_mem (S.add_mem h1 h2) h3

private theorem word_mul_short (D : LatticeData) (v : List (Index D)) (hv : Even v.length)
    {k : ℕ} {q : FixedC2Quotient D} (hq : q ∈ neutralClassLengthLT D k) :
    q * neutralWordClass D v hv ∈ neutralClassLengthLT D (k + v.length) := by
  rw [mul_comm]
  let S := neutralClassLengthLT D (k + v.length)
  change q ∈ S.comap (fixedQuotientProduct D (neutralWordClass D v hv))
  refine (Submodule.span_le.mpr ?_) hq
  rintro _ ⟨u, hu, hlu, rfl⟩
  change neutralWordClass D v hv * neutralWordClass D u hu ∈ S
  rw [mul_comm]
  have huv : Even (u ++ v).length := by simpa only [List.length_append] using hu.add hv
  have hc := class_length_lt_mono D (Nat.add_le_add_right hlu.le _)
    (neutral_word_mul_append D u v hu hv)
  have hluv : (u ++ v).length < k + v.length := by
    simpa only [List.length_append] using Nat.add_lt_add_right hlu v.length
  have hl : neutralWordClass D (u ++ v) huv ∈ S :=
    Submodule.subset_span ⟨u ++ v, huv, hluv, rfl⟩
  simpa only [sub_add_cancel] using S.add_mem hc hl

/-- A prefix whose class drops in length still drops after any even suffix
is attached to the oscillator word. -/
theorem neutral_word_append_short (D : LatticeData) (u v : List (Index D))
    (hu : Even u.length) (hv : Even v.length)
    (h : neutralWordClass D u hu ∈ neutralClassLengthLT D u.length) :
    neutralWordClass D (u ++ v) (by simpa only [List.length_append] using hu.add hv) ∈
      neutralClassLengthLT D (u ++ v).length := by
  simp only [List.length_append]
  let S := neutralClassLengthLT D (u.length + v.length)
  have hprod := word_mul_short D v hv h
  have hcorr := neutral_word_mul_append D u v hu hv
  simpa only [sub_sub_cancel] using S.sub_mem hprod hcorr


/-- The charged power relation for the oscillator in a coordinate of the
actual Leech lattice. -/
def leechNeutralPowerLength (i : Fin leechData.rank) : ℕ :=
  (leechData.G i i + 2).toNat

private theorem leech_unit_charge_data (i : Fin leechData.rank) :
    unitCharge leechData i ≠ 0 ∧
      bilinear leechData (unitCharge leechData i) (unitCharge leechData i) = leechData.G i i ∧
      chargePolynomial leechData (unitCharge leechData i) = X (i, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hi := congrFun h i
    simp [unitCharge] at hi
  · simp [bilinear, unitCharge]
  · simp [chargePolynomial, unitCharge, apply_ite]

private theorem neutral_polynomial_replicate (D : LatticeData) (x : Index D) (n : ℕ) :
    neutralPolynomial D (List.replicate n x) = X x ^ n := by
  simp [neutralPolynomial, List.map_replicate, List.prod_replicate]

/-- A block of `Gᵢᵢ + 2` index-zero letters of colour `i` drops in length. -/
theorem leech_neutral_replicate_short (i : Fin leechData.rank) :
    let u := List.replicate (leechNeutralPowerLength i) ((i, 0) : Index leechData)
    ∃ hu : Even u.length, neutralWordClass leechData u hu ∈
      neutralClassLengthLT leechData u.length := by
  obtain ⟨hne, hnorm, hpoly⟩ := leech_unit_charge_data i
  have h := leech_fixed_neutral_charge_power_length_reduction (unitCharge leechData i) hne
  dsimp only at h
  rw [hnorm] at h
  obtain ⟨hk, hshort⟩ := h
  let k := leechNeutralPowerLength i
  let u := List.replicate k ((i, 0) : Index leechData)
  have hlen : u.length = k := List.length_replicate
  have hu : Even u.length := hlen.symm ▸ hk
  refine ⟨hu, ?_⟩
  have hp : neutralPolynomial leechData u =
      chargePolynomial leechData (unitCharge leechData i) ^ k :=
    (neutral_polynomial_replicate leechData (i, 0) k).trans
      (congrArg (fun p : Oscillator leechData => p ^ k) hpoly.symm)
  have heq : fixedNeutralWord leechData u hu =
      fixedNeutralChargePower leechData (unitCharge leechData i) k hk :=
    Subtype.ext (congrArg (Finsupp.single (0 : Charge leechData)) hp)
  have hclass : neutralWordClass leechData u hu =
      (fixedC2 leechData).mkQ
        (fixedNeutralChargePower leechData (unitCharge leechData i) k hk) :=
    congrArg (fun a : FixedCarrier leechData => (fixedC2 leechData).mkQ a) heq
  change neutralWordClass leechData u hu ∈ neutralClassLengthLT leechData u.length
  rw [hclass, hlen]
  exact hshort

/-- Repeated zero-index coordinate letters force an even neutral word to
land in strictly smaller oscillator length. -/
theorem leech_neutral_word_high_zero_count (w : List (Index leechData))
    (hw : Even w.length) (i : Fin leechData.rank)
    (hi : leechNeutralPowerLength i ≤ w.count (i, 0)) :
    neutralWordClass leechData w hw ∈ neutralClassLengthLT leechData w.length := by
  let u := List.replicate (leechNeutralPowerLength i) ((i, 0) : Index leechData)
  have hsub : u.Sublist w := List.replicate_sublist_iff.mpr hi
  obtain ⟨v, hp⟩ := hsub.exists_perm_append
  obtain ⟨hu, hshort⟩ := leech_neutral_replicate_short i
  have hv : Even v.length := by
    have hadd := hp.length_eq
    have hu' : Even (leechNeutralPowerLength i) := by
      simpa only [List.length_replicate] using hu
    simp only [u, List.length_append, List.length_replicate] at hadd
    rw [Nat.even_iff] at hu' hw ⊢
    omega
  have huv : Even (u ++ v).length := hp.length_eq ▸ hw
  rw [word_class_perm leechData hp hw huv, hp.length_eq]
  exact neutral_word_append_short leechData u v hu hv hshort

open scoped BigOperators

/-- Each colour can contribute at most its charged reduction length minus
one zero-index letter, while all positive indices account for at most six letters. -/
def leechNeutralLengthBound : ℕ :=
  6 + ∑ i : Fin leechData.rank, (leechNeutralPowerLength i - 1)

private theorem length_le_sum_index_add_zero_count (D : LatticeData) (w : List (Index D)) :
    w.length ≤ (w.map Prod.snd).sum + ∑ i : Fin D.rank, w.count (i, 0) := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.count_cons, Finset.sum_add_distrib]
    rcases x with ⟨j, a⟩
    by_cases ha : a = 0
    · subst a
      have hone : (∑ i : Fin D.rank, (if (j, 0) == (i, 0) then 1 else 0 : ℕ)) = 1 := by
        simp
      rw [hone]
      change w.length + 1 ≤ 0 + (List.map Prod.snd w).sum +
        ((∑ i : Fin D.rank, w.count (i, 0)) + 1)
      omega
    · change w.length + 1 ≤ a + (List.map Prod.snd w).sum +
        ((∑ i : Fin D.rank, w.count (i, 0)) +
          ∑ i : Fin D.rank, (if (j, a) == (i, 0) then 1 else 0 : ℕ))
      omega

private theorem leech_neutral_length_le (w : List (Index leechData))
    (hs : (w.map Prod.snd).sum ≤ 6)
    (hc : ∀ i : Fin leechData.rank, w.count (i, 0) < leechNeutralPowerLength i) :
    w.length ≤ leechNeutralLengthBound := by
  have hcounts : (∑ i : Fin leechData.rank, w.count (i, 0)) ≤
      ∑ i : Fin leechData.rank, (leechNeutralPowerLength i - 1) :=
    Finset.sum_le_sum (fun i _ => by have := hc i; omega)
  exact (length_le_sum_index_add_zero_count leechData w).trans (Nat.add_le_add hs hcounts)

/-- The finite spanning family of the image of the actual Leech fixed
vacuum sector in intrinsic fixed C₂. -/
def leechNeutralSpanningClasses : Set (FixedC2Quotient leechData) :=
  {q | ∃ (w : List (Index leechData)) (hw : Even w.length),
    w.length ≤ leechNeutralLengthBound ∧ (w.map Prod.snd).sum ≤ 6 ∧
    (∀ i : Fin leechData.rank, w.count (i, 0) < leechNeutralPowerLength i) ∧
    q = neutralWordClass leechData w hw}

private theorem leech_word_mem_bounded_span (w : List (Index leechData)) (hw : Even w.length) :
    neutralWordClass leechData w hw ∈ Submodule.span ℂ leechNeutralSpanningClasses := by
  suffices h : ∀ n (w : List (Index leechData)) (hw : Even w.length), w.length = n →
      neutralWordClass leechData w hw ∈ Submodule.span ℂ leechNeutralSpanningClasses
    from h _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw hlen
    have hshort : neutralClassLengthLT leechData w.length ≤
        Submodule.span ℂ leechNeutralSpanningClasses := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u, hu, hlu, rfl⟩
      exact ih u.length (hlen ▸ hlu) u hu rfl
    by_cases hs : (w.map Prod.snd).sum ≤ 6
    · by_cases hc : ∀ i : Fin leechData.rank, w.count (i, 0) < leechNeutralPowerLength i
      · exact Submodule.subset_span ⟨w, hw, leech_neutral_length_le w hs hc, hs, hc, rfl⟩
      · push Not at hc
        obtain ⟨i, hi⟩ := hc
        exact hshort (leech_neutral_word_high_zero_count w hw i hi)
    · exact hshort (leech_neutral_word_high_total_index w hw (by omega))

/-- The bounded oscillator classes span the whole neutral image. -/
theorem leech_neutral_image_eq_bounded_span :
    neutralImage leechData = Submodule.span ℂ leechNeutralSpanningClasses := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨w, hw, rfl⟩
    exact leech_word_mem_bounded_span w hw
  · rintro _ ⟨w, hw, _, _, _, rfl⟩
    exact Submodule.subset_span ⟨w, hw, rfl⟩

private theorem leech_index_le_total (w : List (Index leechData)) (x : Index leechData)
    (hx : x ∈ w) : x.2 ≤ (w.map Prod.snd).sum := by
  induction w with
  | nil => simp at hx
  | cons y w ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · simp only [List.map_cons, List.sum_cons]
      exact (ih hx).trans (Nat.le_add_left _ _)

/-- Finiteness of the explicit bounded family of classes. -/
theorem leech_neutral_spanning_classes_finite : leechNeutralSpanningClasses.Finite := by
  classical
  let A := Fin leechData.rank × Fin 7
  let decode : A → Index leechData := fun x => (x.1, x.2.val)
  let words : Set (List (Index leechData)) :=
    List.map decode '' {w : List A | w.length ≤ leechNeutralLengthBound}
  have wordsFinite : words.Finite :=
    (List.finite_length_le A leechNeutralLengthBound).image _
  let toClass (w : List (Index leechData)) : FixedC2Quotient leechData :=
    if h : Even w.length then neutralWordClass leechData w h else 0
  apply (wordsFinite.image toClass).subset
  rintro _ ⟨w, hw, hlen, hs, _, rfl⟩
  have indexBound (x : {x // x ∈ w}) : x.val.2 < 7 :=
    Nat.lt_succ_of_le ((leech_index_le_total w x.val x.property).trans hs)
  let encode (x : {x // x ∈ w}) : A := (x.val.1, ⟨x.val.2, indexBound x⟩)
  refine ⟨w, ⟨w.attach.map encode, ?_, ?_⟩, ?_⟩
  · simpa only [Set.mem_ofPred_eq, List.length_map, List.length_attach] using hlen
  · have hdecode : decode ∘ encode = fun x => x.val := by
      funext x
      exact Prod.eta _
    rw [List.map_map, hdecode, List.attach_map_subtype_val]
  · simp only [toClass, dite_eq_left hw]

/-- The literal fixed vacuum-charge image in the actual Leech intrinsic
fixed C₂ quotient is finite dimensional. -/
theorem leech_fixed_neutral_image_finite :
    FiniteDimensional ℂ ((fixedNeutralSpace leechData).map (fixedC2 leechData).mkQ) := by
  rw [← neutral_image_eq_fixed_neutral_image, leech_neutral_image_eq_bounded_span]
  exact Module.Finite.span_of_finite ℂ leech_neutral_spanning_classes_finite


end
end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_word_pair_replace
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_word_pair_normalize
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_word_high_total_index
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_word_mul_append
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_word_append_short
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_replicate_short
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_word_high_zero_count
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_image_eq_bounded_span
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_spanning_classes_finite
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_neutral_image_finite
