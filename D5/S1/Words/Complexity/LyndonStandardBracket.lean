/- GID: D5/S1/Words/Complexity/LyndonStandardBracket
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonStandardBracket
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Support]
   utility: none
   digest: Lyndon words have a longest Lyndon suffix and integral homogeneous word polynomials. -/

import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lyndon standard brackets in the integral word algebra

This module develops the finite-word algebra used in the Lyndon part of the
Nilforoushan-Parvaresh exact-deck problem.  A Lyndon word is defined by strict
comparison with every nontrivial rotation; no bracket property is built into
the definition.  The standard cut is the least positive cut leaving a Lyndon
suffix, equivalently the longest proper Lyndon suffix.

The results are general symbolic word results.  They use no bounded enumeration,
checker, numerical reduction, or certified instance.
-/

namespace D5.S1.Words.Complexity.LyndonStandardBracket

variable {A : Type*} [LinearOrder A]

/-- A nonempty word strictly smaller than each of its nontrivial rotations. -/
def IsLyndon (w : List A) : Prop :=
  w ≠ [] ∧ ∀ u v : List A, u ≠ [] → v ≠ [] → w = u ++ v → w < v ++ u

theorem isLyndon_singleton (a : A) : IsLyndon [a] := by
  refine ⟨by simp, ?_⟩
  intro u v hu hv huv
  have hlen := congrArg List.length huv
  simp only [List.length_singleton, List.length_append] at hlen
  have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
  have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
  omega

private theorem list_lt_self_append (u : List A) {v : List A} (hv : v ≠ []) :
    u < u ++ v := by
  change List.Lex (· < ·) u (u ++ v)
  induction u with
  | nil =>
      cases v with
      | nil => exact (hv rfl).elim
      | cons a v => exact List.Lex.nil
  | cons a u ih => exact List.Lex.cons ih

private theorem append_left_lt_iff (p x y : List A) :
    p ++ x < p ++ y ↔ x < y := by
  change List.Lex (· < ·) (p ++ x) (p ++ y) ↔ List.Lex (· < ·) x y
  induction p with
  | nil => simp
  | cons a p ih =>
      simpa only [List.cons_append, List.lex_cons_iff] using ih

private theorem lex_append_of_lex_of_length_eq {u x : List A}
    (hux : u < x) (hlen : u.length = x.length) (v y : List A) :
    u ++ v < x ++ y := by
  change List.Lex (· < ·) u x at hux
  change List.Lex (· < ·) (u ++ v) (x ++ y)
  induction hux with
  | nil => simp at hlen
  | rel h => exact List.Lex.rel h
  | cons h ih =>
      exact List.Lex.cons (ih (Nat.succ.inj hlen))

private theorem prefix_of_lt_of_lt_append {v w u : List A}
    (hvw : v < w) (hw : w < v ++ u) : ∃ t, w = v ++ t := by
  induction v generalizing w with
  | nil => exact ⟨w, by simp⟩
  | cons a v ih =>
      cases w with
      | nil => simp at hvw
      | cons b w =>
          have hab : a = b := le_antisymm
            (List.head_le_of_lt hvw) (List.head_le_of_lt hw)
          subst b
          have hvw' : v < w := List.lex_cons_iff.mp hvw
          have hw' : w < v ++ u := by
            change List.Lex (· < ·) (a :: w) ((a :: v) ++ u) at hw
            exact List.lex_cons_iff.mp hw
          rcases ih hvw' hw' with ⟨t, rfl⟩
          exact ⟨t, by simp⟩

/-- The rotation definition of a Lyndon word is equivalent to strict comparison
with every nonempty proper suffix. -/
theorem isLyndon_iff_lt_suffix (w : List A) :
    IsLyndon w ↔
      w ≠ [] ∧ ∀ v : List A, v ≠ [] → v <:+ w → v ≠ w → w < v := by
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    intro v hv ⟨u, huv⟩ hvw
    have hu : u ≠ [] := by
      intro hu
      apply hvw
      simpa [hu] using huv
    have hrot : w < v ++ u := hw.2 u v hu hv huv.symm
    by_contra hn
    have hvltw : v < w := lt_of_le_of_ne (le_of_not_gt hn) hvw
    rcases prefix_of_lt_of_lt_append hvltw hrot with ⟨t, hwt⟩
    have ht : t ≠ [] := by
      intro ht
      apply hvw
      simpa [hwt, ht]
    have htu : t < u := by
      apply (append_left_lt_iff v t u).mp
      simpa only [hwt] using hrot
    have hlen : t.length = u.length := by
      have h₁ := congrArg List.length huv
      have h₂ := congrArg List.length hwt
      simp only [List.length_append] at h₁ h₂
      omega
    have hback : t ++ v < w := by
      rw [← huv]
      exact lex_append_of_lex_of_length_eq htu hlen v v
    have hforward : w < t ++ v := hw.2 v t hv ht hwt
    exact lt_asymm hforward hback
  · rintro ⟨hwne, hsuffix⟩
    refine ⟨hwne, ?_⟩
    intro u v hu hv huv
    have hvSuffix : v <:+ w := ⟨u, huv.symm⟩
    have hvw : v ≠ w := by
      intro heq
      have hlen := congrArg List.length huv
      simp only [heq, List.length_append] at hlen
      have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
      omega
    exact (hsuffix v hv hvSuffix hvw).trans (list_lt_self_append v hu)

private theorem append_right_lt_of_lt_of_length_ge {u v : List A}
    (huv : u < v) (hlen : v.length ≤ u.length) (z : List A) :
    u ++ z < v ++ z := by
  change List.Lex (· < ·) u v at huv
  change List.Lex (· < ·) (u ++ z) (v ++ z)
  induction huv with
  | nil => simp at hlen
  | rel h => exact List.Lex.rel h
  | cons h ih => exact List.Lex.cons (ih (Nat.le_of_succ_le_succ hlen))

private theorem append_lt_of_lt_of_not_prefix {u v : List A}
    (huv : u < v) (hn : ¬u <+: v) (z : List A) : u ++ z < v := by
  change List.Lex (· < ·) u v at huv
  induction huv with
  | nil => exact (hn List.nil_prefix).elim
  | rel h => exact List.Lex.rel h
  | @cons a u v h ih =>
      apply List.Lex.cons
      apply ih
      intro hp
      rcases hp with ⟨q, hq⟩
      exact hn ⟨q, by simpa using congrArg (List.cons a) hq⟩

private theorem append_lt_right_of_lt_of_lyndon {u v : List A}
    (hu : u ≠ []) (huv : u < v) (hv : IsLyndon v) : u ++ v < v := by
  by_cases hp : u <+: v
  · rcases hp with ⟨z, rfl⟩
    have hz : z ≠ [] := by
      intro hz
      simp [hz] at huv
    apply (append_left_lt_iff u (u ++ z) z).mpr
    exact ((isLyndon_iff_lt_suffix (u ++ z)).mp hv).2 z hz
      ⟨u, rfl⟩ (by
        intro h
        have hlen := congrArg List.length h
        simp only [List.length_append] at hlen
        have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
        omega)
  · exact append_lt_of_lt_of_not_prefix huv hp v

/-- Concatenating two Lyndon words in increasing lexicographic order is Lyndon. -/
theorem isLyndon_append {u v : List A} (hu : IsLyndon u) (hv : IsLyndon v)
    (huv : u < v) : IsLyndon (u ++ v) := by
  apply (isLyndon_iff_lt_suffix (u ++ v)).mpr
  refine ⟨by simp [hu.1, hv.1], ?_⟩
  intro t ht htw htwne
  have huvltv : u ++ v < v := append_lt_right_of_lt_of_lyndon hu.1 huv hv
  have hvSuffix : v <:+ u ++ v := List.suffix_append u v
  rcases List.suffix_or_suffix_of_suffix htw hvSuffix with htv | hvt
  · rcases eq_or_ne t v with rfl | htvne
    · exact huvltv
    · exact huvltv.trans_le
        (((isLyndon_iff_lt_suffix v).mp hv).2 t ht htv htvne).le
  · rcases hvt with ⟨s, hst⟩
    subst t
    by_cases hs : s = []
    · subst s
      simpa only [List.nil_append] using huvltv
    · rcases htw with ⟨x, hxt⟩
      have hx : x ≠ [] := by
        intro hx
        apply htwne
        simpa [hx] using hxt
      have hxu : x ++ s = u := by
        apply List.append_left_injective v
        simpa only [List.append_assoc] using hxt
      have hsSuffix : s <:+ u := ⟨x, hxu⟩
      have hsu : s ≠ u := by
        intro h
        have hlen := congrArg List.length hxu
        simp only [h, List.length_append] at hlen
        have hxpos : 0 < x.length := List.length_pos_of_ne_nil hx
        omega
      have hus : u < s := ((isLyndon_iff_lt_suffix u).mp hu).2 s hs hsSuffix hsu
      exact append_right_lt_of_lt_of_length_ge hus hsSuffix.length_le v

theorem exists_lyndon_suffix_cut (w : List A) (hw : 2 ≤ w.length) :
    ∃ i : ℕ, 0 < i ∧ i < w.length ∧ IsLyndon (w.drop i) := by
  have hwne : w ≠ [] := by
    intro h
    simp [h] at hw
  refine ⟨w.length - 1, by omega, by omega, ?_⟩
  rw [List.drop_length_sub_one hwne]
  exact isLyndon_singleton _

/-- The least positive cut whose suffix is Lyndon.  Thus its suffix has maximal length. -/
noncomputable def standardCut (w : List A) (hw : 2 ≤ w.length) : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)

/-- The prefix in the standard longest-Lyndon-suffix factorization. -/
noncomputable def standardLeft (w : List A) (hw : 2 ≤ w.length) : List A :=
  w.take (standardCut w hw)

/-- The longest proper Lyndon suffix in the standard factorization. -/
noncomputable def standardRight (w : List A) (hw : 2 ≤ w.length) : List A :=
  w.drop (standardCut w hw)

private theorem standardRight_longest_suffix (w : List A) (hw : 2 ≤ w.length)
    {v : List A} (hv : IsLyndon v) (hvw : v <:+ w) (hvwne : v ≠ w) :
    v.length ≤ (standardRight w hw).length := by
  rcases hvw with ⟨u, huv⟩
  have hu : u ≠ [] := by
    intro hu
    apply hvwne
    simpa [hu] using huv
  have hj0 : 0 < u.length := List.length_pos_of_ne_nil hu
  have hjl : u.length < w.length := by
    have hlen := congrArg List.length huv
    simp only [List.length_append] at hlen
    have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv.1
    omega
  have hcut : standardCut w hw ≤ u.length :=
    @Nat.find_min' _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)
      u.length ⟨hj0, hjl, by simpa [← huv] using hv⟩
  simp only [standardRight, List.length_drop]
  have hlen := congrArg List.length huv
  simp only [List.length_append] at hlen
  omega

private theorem lyndon_or_standardRight_le (w : List A) (hw : 2 ≤ w.length) :
    IsLyndon w ∨ standardRight w hw ≤ w := by
  let s := standardRight w hw
  have hs : IsLyndon s := by
    simpa [s, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)).2.2
  have hsLeSuffix {v : List A} (hv : v ≠ []) (hvs : v <:+ s) : s ≤ v := by
    rcases eq_or_ne v s with rfl | hvsne
    · exact le_rfl
    · exact ((isLyndon_iff_lt_suffix s).mp hs).2 v hv hvs hvsne |>.le
  have hsw : s <:+ w := ⟨standardLeft w hw, by
    simpa [s, standardLeft, standardRight] using
      List.take_append_drop (standardCut w hw) w⟩
  by_cases hws : w < s
  · left
    apply (isLyndon_iff_lt_suffix w).mpr
    refine ⟨by
      intro h
      simp [h] at hw, ?_⟩
    intro t ht htw htwne
    by_cases hlen : t.length ≤ s.length
    · have hts : t <:+ s :=
        List.suffix_of_suffix_length_le htw hsw hlen
      exact hws.trans_le (hsLeSuffix ht hts)
    · have hslt : s.length < t.length := lt_of_not_ge hlen
      have htltw : t.length < w.length := by
        exact lt_of_le_of_ne htw.length_le (by
          intro heq
          exact htwne (htw.eq_of_length heq))
      have htNot : ¬IsLyndon t := by
        intro htL
        have := standardRight_longest_suffix w hw htL htw htwne
        change t.length ≤ s.length at this
        omega
      have htTwo : 2 ≤ t.length := by
        have hspos : 0 < s.length := List.length_pos_of_ne_nil hs.1
        omega
      have hrec := lyndon_or_standardRight_le t htTwo
      have hrt : standardRight t htTwo ≤ t := hrec.resolve_left htNot
      let r := standardRight t htTwo
      have hrL : IsLyndon r := by
        simpa [r, standardRight, standardCut] using
          (@Nat.find_spec _ (Classical.decPred _)
            (exists_lyndon_suffix_cut t htTwo)).2.2
      have hrtSuffix : r <:+ t := ⟨standardLeft t htTwo, by
        simpa [r, standardLeft, standardRight] using
          List.take_append_drop (standardCut t htTwo) t⟩
      have hrwSuffix : r <:+ w := hrtSuffix.trans htw
      have hrwne : r ≠ w := by
        intro hrw
        have hlenrw := congrArg List.length hrw
        have hrle := hrtSuffix.length_le
        omega
      have hrlen : r.length ≤ s.length :=
        standardRight_longest_suffix w hw hrL hrwSuffix hrwne
      have hrs : r <:+ s :=
        List.suffix_of_suffix_length_le hrwSuffix hsw hrlen
      exact hws.trans_le ((hsLeSuffix hrL.1 hrs).trans hrt)
  · exact Or.inr (le_of_not_gt hws)
termination_by w.length
decreasing_by exact htltw

/-- In the longest-Lyndon-suffix factorization of a Lyndon word, the left
factor is itself Lyndon. -/
theorem isLyndon_standardLeft (w : List A) (hw : 2 ≤ w.length)
    (h : IsLyndon w) : IsLyndon (standardLeft w hw) := by
  let u := standardLeft w hw
  let v := standardRight w hw
  have hu : u ≠ [] := by
    rw [← List.length_pos_iff_ne_nil]
    simp only [u, standardLeft, List.length_take]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut w hw)
    change 0 < standardCut w hw ∧ standardCut w hw < w.length ∧ _ at hc
    omega
  have hv : v ≠ [] := by
    rw [← List.length_pos_iff_ne_nil]
    simp only [v, standardRight, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut w hw)
    change 0 < standardCut w hw ∧ standardCut w hw < w.length ∧ _ at hc
    omega
  have hvL : IsLyndon v := by
    simpa [v, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _) (exists_lyndon_suffix_cut w hw)).2.2
  have hfactor : u ++ v = w := by
    simpa [u, v, standardLeft, standardRight] using
      List.take_append_drop (standardCut w hw) w
  have hvwne : v ≠ w := by
    intro hvw
    have hlen := congrArg List.length hfactor
    simp only [hvw, List.length_append] at hlen
    have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
    omega
  have hwv : w < v :=
    ((isLyndon_iff_lt_suffix w).mp h).2 v hv
      ⟨u, hfactor⟩ hvwne
  have huv : u < v := by
    have huw : u < w := by
      rw [← hfactor]
      exact list_lt_self_append u hv
    exact huw.trans hwv
  by_contra huL
  change ¬IsLyndon u at huL
  have huTwo : 2 ≤ u.length := by
    have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
    have hone : u.length ≠ 1 := by
      intro hlen
      rcases List.length_eq_one_iff.mp hlen with ⟨a, ha⟩
      exact huL (ha ▸ isLyndon_singleton a)
    omega
  have hsu : standardRight u huTwo ≤ u :=
    (lyndon_or_standardRight_le u huTwo).resolve_left huL
  let s := standardRight u huTwo
  have hsL : IsLyndon s := by
    simpa [s, standardRight, standardCut] using
      (@Nat.find_spec _ (Classical.decPred _)
        (exists_lyndon_suffix_cut u huTwo)).2.2
  have hsv : s < v := hsu.trans_lt huv
  have hsvL : IsLyndon (s ++ v) := isLyndon_append hsL hvL hsv
  have hsuffix : s ++ v <:+ w := by
    refine ⟨standardLeft u huTwo, ?_⟩
    calc
      standardLeft u huTwo ++ (s ++ v) =
          (standardLeft u huTwo ++ s) ++ v := (List.append_assoc _ _ _).symm
      _ = u ++ v := by
        simpa [s, standardLeft, standardRight] using
          List.take_append_drop (standardCut u huTwo) u
      _ = w := hfactor
  have hsuffixne : s ++ v ≠ w := by
    intro heq
    have hlen := congrArg List.length heq
    have hleftpos : 0 < (standardLeft u huTwo).length := by
      simp only [standardLeft, List.length_take]
      have hc := @Nat.find_spec _ (Classical.decPred _)
        (exists_lyndon_suffix_cut u huTwo)
      change 0 < standardCut u huTwo ∧
        standardCut u huTwo < u.length ∧ _ at hc
      omega
    have hfactoru := congrArg List.length (show
      standardLeft u huTwo ++ standardRight u huTwo = u by
        simpa [standardLeft, standardRight] using
          List.take_append_drop (standardCut u huTwo) u)
    have hfactorw := congrArg List.length hfactor
    simp only [List.length_append] at hlen hfactoru hfactorw
    change (standardLeft u huTwo).length + s.length = u.length at hfactoru
    omega
  have hlong := standardRight_longest_suffix w hw hsvL hsuffix hsuffixne
  change (s ++ v).length ≤ v.length at hlong
  have hspos : 0 < s.length := List.length_pos_of_ne_nil hsL.1
  simp only [List.length_append] at hlong
  omega

/-- Integral noncommutative polynomials whose monomials are finite words. -/
abbrev WordPolynomial (A : Type*) := MonoidAlgebra ℤ (FreeMonoid A)

/-- The basis monomial represented by a word. -/
noncomputable def wordMonomial (w : List A) : WordPolynomial A :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

/-- Every monomial occurring in `p` has word length `n`. -/
def Homogeneous (p : WordPolynomial A) (n : ℕ) : Prop :=
  ∀ m ∈ p.coeff.support, FreeMonoid.length m = n

private theorem homogeneous_sub {p q : WordPolynomial A} {n : ℕ}
    (hp : Homogeneous p n) (hq : Homogeneous q n) : Homogeneous (p - q) n := by
  intro m hm
  by_contra hnot
  have hp0 : p.coeff m = 0 := by
    by_contra hpne
    exact hnot (hp m (Finsupp.mem_support_iff.mpr hpne))
  have hq0 : q.coeff m = 0 := by
    by_contra hqne
    exact hnot (hq m (Finsupp.mem_support_iff.mpr hqne))
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, hp0, hq0, sub_zero] at hm
  exact hm rfl

private theorem homogeneous_mul {p q : WordPolynomial A} {m n : ℕ}
    (hp : Homogeneous p m) (hq : Homogeneous q n) : Homogeneous (p * q) (m + n) := by
  classical
  intro x hx
  have hx' := MonoidAlgebra.support_coeff_mul_subset p q hx
  rcases Finset.mem_mul.mp hx' with ⟨u, hu, v, hv, huv⟩
  rw [← huv, FreeMonoid.length_mul, hp u hu, hq v hv]

private theorem coeff_mul_append {p q : WordPolynomial A} {u v : List A}
    (hp : Homogeneous p u.length) (hq : Homogeneous q v.length) :
    (p * q).coeff (FreeMonoid.ofList (u ++ v)) =
      p.coeff (FreeMonoid.ofList u) * q.coeff (FreeMonoid.ofList v) := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  calc
    _ = q.coeff.sum (fun y ry ↦
          if FreeMonoid.ofList u * y = FreeMonoid.ofList (u ++ v)
          then p.coeff (FreeMonoid.ofList u) * ry else 0) := by
      apply Finsupp.sum_eq_single (FreeMonoid.ofList u)
      · intro x hx hxu
        rw [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro y hy
        split_ifs with heq
        · exfalso
          apply hxu
          apply List.append_inj_left heq
          exact hp x (Finsupp.mem_support_iff.mpr hx)
        · rfl
      · intro hu0
        simp
    _ = _ := by
      rw [Finsupp.sum_eq_single (FreeMonoid.ofList v)]
      · simp
      · intro y hy hyv
        split_ifs with heq
        · exfalso
          apply hyv
          apply List.append_inj_right heq
          simpa using hq y (Finsupp.mem_support_iff.mpr hy)
        · rfl
      · intro hv0
        simp

/-- A polynomial has leading word `w` when `w` has coefficient one and every
word in its support is lexicographically no smaller than `w`. -/
def HasLeadingWord (p : WordPolynomial A) (w : List A) : Prop :=
  Homogeneous p w.length ∧
    p.coeff (FreeMonoid.ofList w) = 1 ∧
    ∀ x ∈ p.coeff.support, w ≤ FreeMonoid.toList x

private theorem append_le_append_of_le_of_le {u v x y : List A}
    (hu : u ≤ x) (hv : v ≤ y) (hlen : u.length = x.length) :
    u ++ v ≤ x ++ y := by
  rcases hu.eq_or_lt with rfl | hux
  · rcases hv.eq_or_lt with rfl | hv
    · exact le_rfl
    · exact (show u ++ v < u ++ y by
        change List.Lex (· < ·) (u ++ v) (u ++ y)
        change List.Lex (· < ·) v y at hv
        exact List.Lex.append_left (· < ·) hv _).le
  · exact (lex_append_of_lex_of_length_eq hux hlen v y).le

/-- The commutator in the integral word algebra. -/
noncomputable def commutator (p q : WordPolynomial A) : WordPolynomial A := p * q - q * p

private theorem hasLeadingWord_mul {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) :
    HasLeadingWord (p * q) (u ++ v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa [List.length_append] using homogeneous_mul hp.1 hq.1
  · rw [coeff_mul_append hp.1 hq.1, hp.2.1, hq.2.1, one_mul]
  · intro z hz
    have hz' := MonoidAlgebra.support_coeff_mul_subset p q hz
    rcases Finset.mem_mul.mp hz' with ⟨x, hx, y, hy, hxy⟩
    rw [← hxy]
    exact append_le_append_of_le_of_le
      (hp.2.2 x hx) (hq.2.2 y hy) (hp.1 x hx).symm

private theorem reverse_product_coeff_zero {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) (hrot : u ++ v < v ++ u) :
    (q * p).coeff (FreeMonoid.ofList (u ++ v)) = 0 := by
  classical
  rw [← Finsupp.notMem_support_iff]
  intro hz
  have hz' := MonoidAlgebra.support_coeff_mul_subset q p hz
  rcases Finset.mem_mul.mp hz' with ⟨x, hx, y, hy, hxy⟩
  have hle : v ++ u ≤ FreeMonoid.toList (x * y) :=
    append_le_append_of_le_of_le
      (hq.2.2 x hx) (hp.2.2 y hy) (hq.1 x hx).symm
  have heq : FreeMonoid.toList (x * y) = u ++ v := by
    exact congrArg FreeMonoid.toList hxy
  exact (not_lt_of_ge (heq ▸ hle)) hrot

private theorem hasLeadingWord_commutator {p q : WordPolynomial A} {u v : List A}
    (hp : HasLeadingWord p u) (hq : HasLeadingWord q v) (hrot : u ++ v < v ++ u) :
    HasLeadingWord (commutator p q) (u ++ v) := by
  classical
  have hpq := hasLeadingWord_mul hp hq
  have hqp := hasLeadingWord_mul hq hp
  refine ⟨?_, ?_, ?_⟩
  · rw [commutator, List.length_append]
    apply homogeneous_sub (homogeneous_mul hp.1 hq.1)
    simpa [Nat.add_comm] using homogeneous_mul hq.1 hp.1
  · rw [commutator, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      hpq.2.1, reverse_product_coeff_zero hp hq hrot, sub_zero]
  · intro z hz
    rw [commutator, Finsupp.mem_support_iff, MonoidAlgebra.coeff_sub,
      Finsupp.sub_apply] at hz
    by_cases hpqz : z ∈ (p * q).coeff.support
    · exact hpq.2.2 z hpqz
    · have hpq0 := Finsupp.notMem_support_iff.mp hpqz
      have hqpz : z ∈ (q * p).coeff.support := by
        rw [Finsupp.mem_support_iff]
        intro hzero
        exact hz (by rw [hpq0, hzero, sub_zero])
      exact (hrot.le.trans (hqp.2.2 z hqpz))

/-- Recursive standard bracketing, using the longest proper Lyndon suffix at every
word of length at least two.  The value at the empty word is zero. -/
noncomputable def standardBracket : (w : List A) → WordPolynomial A
  | [] => 0
  | [a] => wordMonomial [a]
  | a :: b :: tail =>
      let w := a :: b :: tail
      let hw : 2 ≤ w.length := by simp [w]
      commutator
        (standardBracket (standardLeft w hw))
        (standardBracket (standardRight w hw))
termination_by w => w.length
decreasing_by
  all_goals
    simp only [standardLeft, standardRight, standardCut,
      List.length_take, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut (a :: b :: tail) (by simp))
    omega

theorem standardBracket_homogeneous (w : List A) :
    Homogeneous (standardBracket w) w.length := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil =>
          intro m hm
          simp [standardBracket] at hm
      | cons a tail =>
          cases tail with
          | nil =>
              rw [standardBracket]
              intro m hm
              simp only [wordMonomial, MonoidAlgebra.coeff_single,
                Finsupp.support_single_ne_zero _ one_ne_zero,
                Finset.mem_singleton] at hm
              subst m
              rfl
          | cons b tail =>
              let w := a :: b :: tail
              let hw : 2 ≤ w.length := by simp [w]
              rw [standardBracket]
              have hleft : (standardLeft w hw).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w hw)
                change 0 < standardCut w hw ∧
                  standardCut w hw < w.length ∧ _ at hc
                omega
              have hright : (standardRight w hw).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w hw)
                change 0 < standardCut w hw ∧
                  standardCut w hw < w.length ∧ _ at hc
                omega
              have hfactor := congrArg List.length (show
                standardLeft w hw ++ standardRight w hw = w by
                  simpa [standardLeft, standardRight] using
                    List.take_append_drop (standardCut w hw) w)
              rw [List.length_append] at hfactor
              rw [← hfactor]
              rw [commutator]
              apply homogeneous_sub
                (homogeneous_mul (ih _ hleft _ rfl) (ih _ hright _ rfl))
              simpa [Nat.add_comm] using
                homogeneous_mul (ih _ hright _ rfl) (ih _ hleft _ rfl)

/-- The word-theoretic closure needed by the recursive standard factorization.
It mentions only Lyndon suffix cuts and lexicographic rotations, not brackets or
coefficients. -/
noncomputable def StandardFactorClosed : (w : List A) → Prop
  | [] => False
  | [_] => True
  | a :: b :: tail =>
      let w := a :: b :: tail
      let hw : 2 ≤ w.length := by simp [w]
      StandardFactorClosed (standardLeft w hw) ∧
        StandardFactorClosed (standardRight w hw) ∧
        w < standardRight w hw ++ standardLeft w hw
termination_by w => w.length
decreasing_by
  all_goals
    simp only [standardLeft, standardRight, standardCut,
      List.length_take, List.length_drop]
    have hc := @Nat.find_spec _ (Classical.decPred _)
      (exists_lyndon_suffix_cut (a :: b :: tail) (by simp))
    omega

/-- Actual Lyndon words remain Lyndon throughout recursive standard factorization. -/
theorem isLyndon_standardFactorClosed (w : List A) (hw : IsLyndon w) :
    StandardFactorClosed w := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil => exact (hw.1 rfl).elim
      | cons a tail =>
          cases tail with
          | nil => simp [StandardFactorClosed]
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              have hleft : (standardLeft w htwo).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hright : (standardRight w htwo).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              change StandardFactorClosed w
              rw [StandardFactorClosed]
              exact ⟨
                ih _ hleft _ (isLyndon_standardLeft w htwo hw) rfl,
                ih _ hright _ (by
                  simpa [standardRight, standardCut] using
                    (@Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)).2.2) rfl,
                by
                  have hfactor : standardLeft w htwo ++ standardRight w htwo = w := by
                    simpa [standardLeft, standardRight] using
                      List.take_append_drop (standardCut w htwo) w
                  apply hw.2 (standardLeft w htwo) (standardRight w htwo)
                  · rw [← List.length_pos_iff_ne_nil]
                    simp only [standardLeft, List.length_take]
                    have hc := @Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)
                    change 0 < standardCut w htwo ∧
                      standardCut w htwo < w.length ∧ _ at hc
                    omega
                  · rw [← List.length_pos_iff_ne_nil]
                    simp only [standardRight, List.length_drop]
                    have hc := @Nat.find_spec _ (Classical.decPred _)
                      (exists_lyndon_suffix_cut w htwo)
                    change 0 < standardCut w htwo ∧
                      standardCut w htwo < w.length ∧ _ at hc
                    omega
                  · exact hfactor.symm⟩

theorem standardBracket_hasLeadingWord (w : List A) (hw : StandardFactorClosed w) :
    HasLeadingWord (standardBracket w) w := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil => simp [StandardFactorClosed] at hw
      | cons a tail =>
          cases tail with
          | nil =>
              rw [standardBracket]
              refine ⟨?_, by simp [wordMonomial], ?_⟩
              · intro m hm
                simp only [wordMonomial, MonoidAlgebra.coeff_single,
                  Finsupp.support_single_ne_zero _ one_ne_zero,
                  Finset.mem_singleton] at hm
                subst m
                rfl
              intro x hx
              simp only [wordMonomial, MonoidAlgebra.coeff_single,
                Finsupp.support_single_ne_zero _ one_ne_zero,
                Finset.mem_singleton] at hx
              subst x
              exact le_rfl
          | cons b tail =>
              let w := a :: b :: tail
              let htwo : 2 ≤ w.length := by simp [w]
              have hleft : (standardLeft w htwo).length < w.length := by
                simp only [standardLeft, List.length_take]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hright : (standardRight w htwo).length < w.length := by
                simp only [standardRight, List.length_drop]
                have hc := @Nat.find_spec _ (Classical.decPred _)
                  (exists_lyndon_suffix_cut w htwo)
                change 0 < standardCut w htwo ∧
                  standardCut w htwo < w.length ∧ _ at hc
                omega
              have hw' : StandardFactorClosed (a :: b :: tail) := hw
              simp only [StandardFactorClosed] at hw'
              rw [standardBracket]
              let u := standardLeft w htwo
              let v := standardRight w htwo
              change HasLeadingWord
                (commutator (standardBracket u) (standardBracket v)) w
              have hfactor : u ++ v = w := by
                simpa [u, v, standardLeft, standardRight] using
                  List.take_append_drop (standardCut w htwo) w
              have hrot : u ++ v < v ++ u := by
                rw [hfactor]
                exact hw'.2.2
              have hlead : HasLeadingWord
                  (commutator (standardBracket u) (standardBracket v)) (u ++ v) :=
                hasLeadingWord_commutator
                  (ih _ hleft _ hw'.1 rfl)
                  (ih _ hright _ hw'.2.1 rfl)
                  hrot
              exact hfactor ▸ hlead

/-- Standard brackets with recursively valid standard factorizations are linearly
independent over the integers, in every degree and hence jointly. -/
theorem standardBracket_linearIndependent :
    LinearIndependent ℤ
      (fun w : {w : List A // StandardFactorClosed w} ↦ standardBracket w.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter (fun j ↦ g j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  let m := t.min' ht
  have hm : m ∈ t := Finset.min'_mem t ht
  have hms : m ∈ s := (Finset.mem_filter.mp hm).1
  have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hcoeff := congrArg
    (fun p : WordPolynomial A ↦ p.coeff (FreeMonoid.ofList m.1)) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hcoeff
  have hother : ∀ j ∈ s, j ≠ m →
      g j • (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
    intro j hjs hjm
    by_cases hgj : g j = 0
    · simp [hgj]
    have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
    have hmj : m < j := lt_of_le_of_ne (Finset.min'_le t j hjt) (Ne.symm hjm)
    have hcoeff0 : (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hmem
      have hjmle : j.1 ≤ m.1 :=
        (standardBracket_hasLeadingWord j.1 j.2).2.2 _ hmem
      exact (not_lt_of_ge hjmle) hmj
    simp [hcoeff0]
  rw [Finset.sum_eq_single m hother (fun hmnot ↦ (hmnot hms).elim)] at hcoeff
  rw [(standardBracket_hasLeadingWord m.1 m.2).2.1] at hcoeff
  exact hmg (by simpa using hcoeff)

end D5.S1.Words.Complexity.LyndonStandardBracket
