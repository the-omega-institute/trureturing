/- GID: D5/S3/Combinatorics/APIntersectionBoundaryEndgameDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/APIntersectionBoundaryEndgameDefs
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Card, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Boundary single-difference AP-intersection families have at most choose N 2 plus one members. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.APIntersectionBoundaryEndgame

/-- `S` is a finite arithmetic progression with common difference `d`: `S = {a, a+d, …, a+(n-1)d}` with `n ≥ 1`. -/
def IsAPDiff (d : ℕ) (S : Finset ℕ) : Prop :=
  ∃ a n : ℕ, 0 < n ∧ S = (Finset.range n).image (fun i => a + i * d)

/-- `S` is a nonempty finite arithmetic progression (one- and two-element sets qualify). -/
def IsAP (S : Finset ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ IsAPDiff d S

/-- Boundary single-difference endgame of Erdős #272: in a family of subsets of `[1,N]` whose pairwise intersections are nonempty
APs, whose members of size ≥ 4 are APs, and whose members avoiding `1` are APs of one common difference `d₀` with ≥ 4 elements,
there are at most `C(N,2) + 1` members. -/
def claim : Prop :=
  ∀ (N d₀ : ℕ) (F : Finset (Finset ℕ)), 0 < d₀ →
    (∀ S ∈ F, S ⊆ Finset.Icc 1 N) →
    (∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty ∧ IsAP (S ∩ T)) →
    (∀ S ∈ F, 4 ≤ S.card → IsAP S) →
    (∀ S ∈ F, 1 ∉ S → 4 ≤ S.card ∧ IsAPDiff d₀ S) →
    F.card ≤ N.choose 2 + 1

def apRange (a d n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => a + i * d)

/-- A triple consisting of `1` and two consecutive terminal points of a boundary AP of
length at least four is not an AP. -/
lemma terminal_triple_not_ap {d k : ℕ} (hd : 0 < d) (hk : 3 ≤ k) :
    ¬ IsAP ({1, 1 + (k - 1) * d, 1 + k * d} : Finset ℕ) := by
  let x := 1 + (k - 1) * d
  let y := 1 + k * d
  have hmul : (k - 1) * d + d = k * d := by
    calc
      (k - 1) * d + d = (k - 1 + 1) * d := by rw [Nat.add_mul, one_mul]
      _ = k * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hpos : 0 < (k - 1) * d := Nat.mul_pos (by omega) hd
  have hxy : 1 < x ∧ x < y := by dsimp [x, y]; omega
  have hcard : ({1, x, y} : Finset ℕ).card = 3 := by
    simp [show 1 ≠ x by omega, show 1 ≠ y by omega, show x ≠ y by omega]
  have hsub : ({1, x, y} : Finset ℕ) ⊆ Finset.Icc 1 y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  intro hap
  obtain ⟨e, he, a, n, hn, hS⟩ := hap
  have haS : a ∈ ({1, x, y} : Finset ℕ) := by
    rw [hS]
    exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hsub haS)).1
  have h1a : a ≤ 1 := by
    have hmem : 1 ∈ (Finset.range n).image (fun i => a + i * e) := by
      rw [← hS]
      simp
    obtain ⟨i, hi, hval⟩ := Finset.mem_image.mp hmem
    omega
  have ha : a = 1 := by omega
  subst a
  change ({1, x, y} : Finset ℕ) = apRange 1 e n at hS
  have hcn : ({1, x, y} : Finset ℕ).card = n := by
    rw [hS]
    unfold apRange
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Nat.mul_right_cancel he (Nat.add_left_cancel hij)
  have hn3 : n = 3 := by omega
  rw [hn3] at hS
  have hxmem : x ∈ apRange 1 e 3 := hS ▸ (by simp : x ∈ ({1, x, y} : Finset ℕ))
  have hymem : y ∈ apRange 1 e 3 := hS ▸ (by simp : y ∈ ({1, x, y} : Finset ℕ))
  obtain ⟨i, hi, hxi⟩ : ∃ i < 3, x = 1 + i * e := by
    simpa [apRange, eq_comm] using hxmem
  obtain ⟨j, hj, hyj⟩ : ∃ j < 3, y = 1 + j * e := by
    simpa [apRange, eq_comm] using hymem
  have hi0 : 0 < i := by
    by_contra hzero
    have : i = 0 := by omega
    simp [this] at hxi
    omega
  have hij : i < j := by
    by_contra h
    have hle : j * e ≤ i * e := Nat.mul_le_mul_right e (by omega)
    omega
  have hi1 : i = 1 := by omega
  have hj2 : j = 2 := by omega
  subst i
  subst j
  simp only [one_mul] at hxi hyj
  have htwice : (k - 1) * d + (k - 1) * d = k * d := by omega
  have hbig : d < (k - 1) * d := by
    have htwo : 2 ≤ k - 1 := by omega
    have hge : 2 * d ≤ (k - 1) * d := Nat.mul_le_mul_right d htwo
    omega
  omega

/-- If an avoider's two external neighbours are consecutive terminal points of a long
boundary AP, the two family members are disjoint. -/
lemma terminal_avoider_disjoint {a d m e n : ℕ}
    (hd : 0 < d) (he : 0 < e) (hm : 0 < m) (hn : 4 ≤ n)
    (hleft : 2 ≤ a - d)
    (hpair : ({1 + (n - 2) * e, 1 + (n - 1) * e} : Finset ℕ) =
      {a - d, a + m * d}) :
    Disjoint (apRange 1 e n) (apRange a d m) := by
  have hmrel : a + (m - 1) * d + d = a + m * d := by
    calc
      a + (m - 1) * d + d = a + (m - 1 + 1) * d := by rw [Nat.add_mul, one_mul]; omega
      _ = a + m * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hnrel : (n - 2) * e + e = (n - 1) * e := by
    have hn' : n - 2 + 1 = n - 1 := by omega
    rw [← hn', Nat.add_mul, one_mul]
  have hpairOrd : 1 + (n - 2) * e < 1 + (n - 1) * e := by omega
  have havoidOrd : a - d < a + m * d := by omega
  have hfirst : 1 + (n - 2) * e = a - d := by
    have hmem : 1 + (n - 2) * e ∈ ({a - d, a + m * d} : Finset ℕ) := by
      rw [← hpair]
      simp
    have hmem' : 1 + (n - 1) * e ∈ ({a - d, a + m * d} : Finset ℕ) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    rcases hmem with h | h <;> rcases hmem' with h' | h' <;> omega
  have hlast : 1 + (n - 1) * e = a + m * d := by
    have hmem : 1 + (n - 1) * e ∈ ({a - d, a + m * d} : Finset ℕ) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> omega
  rw [Finset.disjoint_left]
  intro z hzQ hzA
  obtain ⟨i, hi, hzi⟩ : ∃ i < n, z = 1 + i * e := by
    simpa [apRange, eq_comm] using hzQ
  obtain ⟨j, hj, hzj⟩ : ∃ j < m, z = a + j * d := by
    simpa [apRange, eq_comm] using hzA
  have hjpos : a ≤ z := by omega
  have hupper : z ≤ a + (m - 1) * d := by
    have hj' : j ≤ m - 1 := by omega
    have hmul := Nat.mul_le_mul_right d hj'
    omega
  have hleftBound : a - d < z := by omega
  have hrightBound : z < a + m * d := by omega
  by_cases hii : i ≤ n - 2
  · have hmul : i * e ≤ (n - 2) * e := Nat.mul_le_mul_right e hii
    omega
  · have hii' : i = n - 1 := by omega
    subst i
    omega

/-- Two AP indices with starts at the left boundary of their residue classes can coincide
only when their starts and indices coincide. -/
lemma left_blocked_residue_recovery {a b d i j : ℕ}
    (_hd : 0 < d) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hla : a - d < 2) (hlb : b - d < 2)
    (heq : a + i * d = b + j * d) : a = b ∧ i = j := by
  have habound : a ≤ d + 1 := by omega
  have hbbound : b ≤ d + 1 := by omega
  have hstepi : (i + 1) * d = i * d + d := by rw [Nat.add_mul, one_mul]
  have hstepj : (j + 1) * d = j * d + d := by rw [Nat.add_mul, one_mul]
  have hji : ¬ i < j := by
    intro hij
    have hmul : (i + 1) * d ≤ j * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hij : ¬ j < i := by
    intro hji
    have hmul : (j + 1) * d ≤ i * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hindices : i = j := by omega
  constructor
  · rw [hindices] at heq
    omega
  · exact hindices

/-- At a fixed start and difference, two progressions both blocked on the right by `N`
have the same length. -/
lemma right_blocked_length_recovery {a d m n N : ℕ}
    (_hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hmLast : a + (m - 1) * d ≤ N) (hnLast : a + (n - 1) * d ≤ N)
    (hmBlocked : N < a + m * d) (hnBlocked : N < a + n * d) : m = n := by
  have hmn : ¬ m < n := by
    intro h
    have hmul : m * d ≤ (n - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hnm : ¬ n < m := by
    intro h
    have hmul : n * d ≤ (m - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  omega

/-- A left-only outside-neighbour image determines an avoider. -/
lemma avoider_left_point_recovery {a b d m n N : ℕ}
    (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hla : 2 ≤ a - d) (hlb : 2 ≤ b - d)
    (hmLast : a + (m - 1) * d ≤ N) (hnLast : b + (n - 1) * d ≤ N)
    (hmBlocked : N < a + m * d) (hnBlocked : N < b + n * d)
    (heq : a - d = b - d) :
    apRange a d m = apRange b d n := by
  have hab : a = b := by omega
  subst b
  have hmn := right_blocked_length_recovery hd hm hn hmLast hnLast hmBlocked hnBlocked
  subst n
  rfl

/-- A right-only outside-neighbour image determines an avoider. -/
lemma avoider_right_point_recovery {a b d m n : ℕ}
    (hd : 0 < d) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hla : a - d < 2) (hlb : b - d < 2)
    (heq : a + m * d = b + n * d) :
    apRange a d m = apRange b d n := by
  obtain ⟨hab, hmn⟩ := left_blocked_residue_recovery hd ha hb hla hlb heq
  subst b
  subst n
  rfl

/-- Equal left and right point images from opposite ends force the two avoiders to be
disjoint. -/
lemma avoider_opposite_point_disjoint {a b d m n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (heq : a - d = b + n * d) :
    Disjoint (apRange a d m) (apRange b d n) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  obtain ⟨i, hi, hzi⟩ : ∃ i < m, z = a + i * d := by
    simpa [apRange, eq_comm] using hzA
  obtain ⟨j, hj, hzj⟩ : ∃ j < n, z = b + j * d := by
    simpa [apRange, eq_comm] using hzB
  have hza : a ≤ z := by omega
  have hzb : z ≤ b + (n - 1) * d := by
    have hj' : j ≤ n - 1 := by omega
    have hmul := Nat.mul_le_mul_right d hj'
    omega
  have hrel : b + (n - 1) * d + d = b + n * d := by
    calc
      b + (n - 1) * d + d = b + (n - 1 + 1) * d := by rw [Nat.add_mul, one_mul]; omega
      _ = b + n * d := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  omega

/-- Two avoiders with no outside neighbour that intersect are the same complete residue
class segment in `[2,N]`. -/
lemma avoider_no_neighbour_recovery {a b d m n N : ℕ}
    (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hla : a - d < 2) (hlb : b - d < 2)
    (hmLast : a + (m - 1) * d ≤ N) (hnLast : b + (n - 1) * d ≤ N)
    (hmBlocked : N < a + m * d) (hnBlocked : N < b + n * d)
    (hinter : ((apRange a d m) ∩ (apRange b d n)).Nonempty) :
    apRange a d m = apRange b d n := by
  obtain ⟨z, hz⟩ := hinter
  obtain ⟨i, hi, hzi⟩ : ∃ i < m, z = a + i * d := by
    simpa [apRange, eq_comm] using (Finset.mem_inter.mp hz).1
  obtain ⟨j, hj, hzj⟩ : ∃ j < n, z = b + j * d := by
    simpa [apRange, eq_comm] using (Finset.mem_inter.mp hz).2
  obtain ⟨hab, _⟩ := left_blocked_residue_recovery hd ha hb hla hlb (hzi.symm.trans hzj)
  subst b
  have hmn := right_blocked_length_recovery hd hm hn hmLast hnLast hmBlocked hnBlocked
  subst n
  rfl

noncomputable def throughStep (S : Finset ℕ) : ℕ := by
  classical
  exact if h : IsAP S then Classical.choose h else 0

noncomputable def avoiderStart (d : ℕ) (S : Finset ℕ) : ℕ := by
  classical
  exact if h : IsAPDiff d S then Classical.choose h else 0

/-- One extra code, a point code, or a two-point code for a boundary AP family member. -/
noncomputable def code (N d : ℕ) (S : Finset ℕ) : Option (ℕ ⊕ Finset ℕ) := by
  classical
  exact
  if 1 ∈ S then
    if S.card = 1 then none
    else if S.card = 2 then some (Sum.inl (S.sup id))
    else if S.card = 3 then some (Sum.inr (S.erase 1))
    else some (Sum.inr
      {1 + (S.card - 2) * throughStep S, 1 + (S.card - 1) * throughStep S})
  else
    let a := avoiderStart d S
    if 2 ≤ a - d then
      if a + S.card * d ≤ N then some (Sum.inr {a - d, a + S.card * d})
      else some (Sum.inl (a - d))
    else if a + S.card * d ≤ N then some (Sum.inl (a + S.card * d))
    else none

def vertices (N : ℕ) : Finset ℕ := Finset.Icc 2 N

def targets (N : ℕ) : Finset (Option (ℕ ⊕ Finset ℕ)) :=
  insert none
    (((vertices N).image (fun x => some (Sum.inl x))) ∪
      (((vertices N).powersetCard 2).image (fun p => some (Sum.inr p))))

/-- A three-point boundary member and a longer boundary member cannot have the same
two-point code: their intersection would be the non-AP terminal triple. -/
lemma triple_terminal_separate {F : Finset (Finset ℕ)} {T Q : Finset ℕ}
    {d n : ℕ} (hd : 0 < d) (hn : 4 ≤ n)
    (hT : T ∈ F) (hQ : Q ∈ F) (hone : 1 ∈ T) (hcard : T.card = 3)
    (hQform : Q = apRange 1 d n)
    (hpair : T.erase 1 = {1 + (n - 2) * d, 1 + (n - 1) * d})
    (hinter : ∀ S ∈ F, ∀ U ∈ F, S ≠ U → (S ∩ U).Nonempty ∧ IsAP (S ∩ U)) :
    False := by
  have hTform : T = ({1, 1 + (n - 2) * d, 1 + (n - 1) * d} : Finset ℕ) := by
    calc
      T = insert 1 (T.erase 1) := (Finset.insert_erase hone).symm
      _ = _ := by rw [hpair]
  have hTsub : T ⊆ Q := by
    rw [hTform, hQform]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, by simp only [Finset.mem_range]; omega, by simp⟩
    · exact Finset.mem_image.mpr
        ⟨n - 2, by simp only [Finset.mem_range]; omega, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨n - 1, by simp only [Finset.mem_range]; omega, rfl⟩
  have hneq : T ≠ Q := by
    intro heq
    have hc := congrArg Finset.card heq
    have hrangeCard : (apRange 1 d n).card = n := by
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    rw [hQform, hrangeCard] at hc
    omega
  have hap : IsAP T := by
    simpa [Finset.inter_eq_left.mpr hTsub] using (hinter T hT Q hQ hneq).2
  have hnot := terminal_triple_not_ap hd (show 3 ≤ n - 1 by omega)
  have hidx : n - 1 - 1 = n - 2 := by omega
  rw [hidx] at hnot
  exact hnot (hTform ▸ hap)

/-- At most one member of the family can use the extra, untyped code. -/
lemma none_code_separate {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty ∧ IsAP (S ∩ T))
    (havoid : ∀ S ∈ F, 1 ∉ S → 4 ≤ S.card ∧ IsAPDiff d S)
    {S T : Finset ℕ} (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hcS : code N d S = none) (hcT : code N d T = none) : False := by
  classical
  have avoiderForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∉ U →
      IsAPDiff d U → 2 ≤ avoiderStart d U ∧ 0 < U.card ∧
        U = apRange (avoiderStart d U) d U.card ∧
        avoiderStart d U + (U.card - 1) * d ≤ N := by
    intro U hU hone hap
    let a := avoiderStart d U
    have hs : ∃ n : ℕ, 0 < n ∧ U = apRange a d n := by
      simpa only [a, avoiderStart, dif_pos hap, apRange] using Classical.choose_spec hap
    obtain ⟨n, hn, hUform⟩ := hs
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have ha2 : 2 ≤ a := by
      by_contra h
      have hval : a = 1 := by omega
      exact hone (hval ▸ haU)
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    have hlast : a + (n - 1) * d ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨n - 1, by simp only [Finset.mem_range]; omega, rfl⟩
    exact ⟨ha2, by omega, by simpa [hc] using hUform,
      by simpa [hc] using (Finset.mem_Icc.mp (hU hlast)).2⟩
  have hmeet := (hinter S hS T hT hne).1
  by_cases honeS : 1 ∈ S
  · have hcardS : S.card = 1 := by
      by_contra h
      simp only [code, if_pos honeS, if_neg h] at hcS
      split_ifs at hcS
    have hSform : S = {1} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardS
      have hxeq : x = 1 := by
        have hx1 : 1 = x := by simpa [hx] using honeS
        exact hx1.symm
      simpa [hxeq] using hx
    by_cases honeT : 1 ∈ T
    · have hcardT : T.card = 1 := by
        by_contra h
        simp only [code, if_pos honeT, if_neg h] at hcT
        split_ifs at hcT
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardT
      have hxeq : x = 1 := by
        have hx1 : 1 = x := by simpa [hx] using honeT
        exact hx1.symm
      have hTform : T = {1} := by simpa [hxeq] using hx
      exact hne (hSform.trans hTform.symm)
    · obtain ⟨z, hz⟩ := hmeet
      have hzS := (Finset.mem_inter.mp hz).1
      have hzT := (Finset.mem_inter.mp hz).2
      have hz1 : z = 1 := by simpa [hSform] using hzS
      exact honeT (hz1 ▸ hzT)
  · by_cases honeT : 1 ∈ T
    · have hcardT : T.card = 1 := by
        by_contra h
        simp only [code, if_pos honeT, if_neg h] at hcT
        split_ifs at hcT
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardT
      have hxeq : x = 1 := by
        have hx1 : 1 = x := by simpa [hx] using honeT
        exact hx1.symm
      obtain ⟨z, hz⟩ := hmeet
      have hzT := (Finset.mem_inter.mp hz).2
      have hzS := (Finset.mem_inter.mp hz).1
      have hz1 : z = 1 := by simpa [hx, hxeq] using hzT
      exact honeS (hz1 ▸ hzS)
    · obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haS, hpS, hnormS, hlastS⟩ :=
        avoiderForm (hsub S hS) honeS hapS
      obtain ⟨haT, hpT, hnormT, hlastT⟩ :=
        avoiderForm (hsub T hT) honeT hapT
      let a := avoiderStart d S
      let b := avoiderStart d T
      change S = apRange a d S.card at hnormS
      change T = apRange b d T.card at hnormT
      have hlS : ¬ 2 ≤ a - d := by
        intro h
        change 2 ≤ avoiderStart d S - d at h
        simp only [code, if_neg honeS, if_pos h] at hcS
        split_ifs at hcS
      have hlT : ¬ 2 ≤ b - d := by
        intro h
        change 2 ≤ avoiderStart d T - d at h
        simp only [code, if_neg honeT, if_pos h] at hcT
        split_ifs at hcT
      have hrS : ¬ a + S.card * d ≤ N := by
        intro h
        have hl : ¬ 2 ≤ avoiderStart d S - d := hlS
        change avoiderStart d S + S.card * d ≤ N at h
        simp only [code, if_neg honeS, if_neg hl, if_pos h] at hcS
        cases hcS
      have hrT : ¬ b + T.card * d ≤ N := by
        intro h
        have hl : ¬ 2 ≤ avoiderStart d T - d := hlT
        change avoiderStart d T + T.card * d ≤ N at h
        simp only [code, if_neg honeT, if_neg hl, if_pos h] at hcT
        cases hcT
      have hmeet' : ((apRange a d S.card) ∩ (apRange b d T.card)).Nonempty := by
        rw [← hnormS, ← hnormT]
        exact hmeet
      have hnorm := avoider_no_neighbour_recovery hd hpS hpT haS haT
        (by omega : a - d < 2) (by omega : b - d < 2)
        hlastS hlastT (by omega) (by omega)
        hmeet'
      exact hne (hnormS.trans (hnorm.trans hnormT.symm))

/-- Distinct members cannot share a point code. -/
lemma point_code_separate {N d : ℕ} {F : Finset (Finset ℕ)}
    (hd : 0 < d)
    (hsub : ∀ S ∈ F, S ⊆ Finset.Icc 1 N)
    (hinter : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → (S ∩ T).Nonempty ∧ IsAP (S ∩ T))
    (havoid : ∀ S ∈ F, 1 ∉ S → 4 ≤ S.card ∧ IsAPDiff d S)
    {S T : Finset ℕ} (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T) {x : ℕ}
    (hcS : code N d S = some (Sum.inl x))
    (hcT : code N d T = some (Sum.inl x)) : False := by
  classical
  have avoiderForm : ∀ {U : Finset ℕ}, U ⊆ Finset.Icc 1 N → 1 ∉ U →
      IsAPDiff d U → 2 ≤ avoiderStart d U ∧ 0 < U.card ∧
        U = apRange (avoiderStart d U) d U.card ∧
        avoiderStart d U + (U.card - 1) * d ≤ N := by
    intro U hU hone hap
    let a := avoiderStart d U
    have hs : ∃ n : ℕ, 0 < n ∧ U = apRange a d n := by
      simpa only [a, avoiderStart, dif_pos hap, apRange] using Classical.choose_spec hap
    obtain ⟨n, hn, hUform⟩ := hs
    have haU : a ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨0, by simpa using hn, by simp⟩
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hU haU)).1
    have ha2 : 2 ≤ a := by
      by_contra h
      have hval : a = 1 := by omega
      exact hone (hval ▸ haU)
    have hc : U.card = n := by
      rw [hUform]
      unfold apRange
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    have hlast : a + (n - 1) * d ∈ U := by
      rw [hUform]
      exact Finset.mem_image.mpr ⟨n - 1, by simp only [Finset.mem_range]; omega, rfl⟩
    exact ⟨ha2, by omega, by simpa [hc] using hUform,
      by simpa [hc] using (Finset.mem_Icc.mp (hU hlast)).2⟩
  have pointNormal : ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 N → 1 ∈ U →
      U.card = 2 → U = {1, U.sup id} ∧ 2 ≤ U.sup id := by
    intro U hU hone hcard
    have herase : (U.erase 1).card = 1 := by
      rw [Finset.card_erase_of_mem hone]
      omega
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp herase
    have hzE : z ∈ U.erase 1 := by rw [hz]; simp
    have hzU : z ∈ U := (Finset.mem_erase.mp hzE).2
    have hzNe : z ≠ 1 := (Finset.mem_erase.mp hzE).1
    have hz2 : 2 ≤ z := by
      have h := (Finset.mem_Icc.mp (hU hzU)).1
      omega
    have hUform : U = {1, z} := by
      calc
        U = insert 1 (U.erase 1) := (Finset.insert_erase hone).symm
        _ = {1, z} := by rw [hz]
    have hsup : U.sup id = z := by
      rw [hUform]
      simp [max_eq_right (by omega : 1 ≤ z)]
    exact ⟨by simpa [hsup] using hUform, by simpa [hsup] using hz2⟩
  have smallPoint : ∀ A : Finset ℕ, ({1, x} : Finset ℕ) ∈ F →
      A ∈ F → 1 ∉ A → x ∈ A := by
    intro A hsmall hA havoidA
    have hne : ({1, x} : Finset ℕ) ≠ A := by
      intro heq
      exact havoidA (heq ▸ (by simp : 1 ∈ ({1, x} : Finset ℕ)))
    obtain ⟨z, hz⟩ := (hinter _ hsmall _ hA hne).1
    have hz' := Finset.mem_inter.mp hz
    have hzx : z = 1 ∨ z = x := by simpa using hz'.1
    rcases hzx with rfl | rfl
    · exact False.elim (havoidA hz'.2)
    · exact hz'.2
  let aS := avoiderStart d S
  let aT := avoiderStart d T
  have point_cases (U : Finset ℕ) (hc : code N d U = some (Sum.inl x)) :
      (1 ∈ U ∧ U.card = 2 ∧ x = U.sup id) ∨
      (1 ∉ U ∧ 2 ≤ avoiderStart d U - d ∧ N < avoiderStart d U + U.card * d ∧
        x = avoiderStart d U - d) ∨
      (1 ∉ U ∧ avoiderStart d U - d < 2 ∧ avoiderStart d U + U.card * d ≤ N ∧
        x = avoiderStart d U + U.card * d) := by
    by_cases hone : 1 ∈ U
    · by_cases h1 : U.card = 1
      · simp [code, hone, h1] at hc
      by_cases h2 : U.card = 2
      · left
        have hx : x = U.sup id := by
          simpa only [code, if_pos hone, if_neg h1, if_pos h2,
            Option.some.injEq, Sum.inl.injEq] using hc.symm
        exact ⟨hone, h2, hx⟩
      by_cases h3 : U.card = 3
      · simp only [code, if_pos hone, if_neg h1, if_neg h2, if_pos h3] at hc
        cases hc
      · simp only [code, if_pos hone, if_neg h1, if_neg h2, if_neg h3] at hc
        cases hc
    · by_cases hl : 2 ≤ avoiderStart d U - d
      · by_cases hr : avoiderStart d U + U.card * d ≤ N
        · simp only [code, if_neg hone, if_pos hl, if_pos hr] at hc
          cases hc
        · right; left
          have hx : x = avoiderStart d U - d := by
            simpa only [code, if_neg hone, if_pos hl, if_neg hr,
              Option.some.injEq, Sum.inl.injEq] using hc.symm
          exact ⟨hone, hl, by omega, hx⟩
      · by_cases hr : avoiderStart d U + U.card * d ≤ N
        · right; right
          have hx : x = avoiderStart d U + U.card * d := by
            simpa only [code, if_neg hone, if_neg hl, if_pos hr,
              Option.some.injEq, Sum.inl.injEq] using hc.symm
          exact ⟨hone, by omega, hr, hx⟩
        · simp only [code, if_neg hone, if_neg hl, if_neg hr] at hc
          cases hc
  have meet := (hinter S hS T hT hne).1
  have outside (A : Finset ℕ) (hA : A ∈ F) (hone : 1 ∉ A)
      (hleft : x = avoiderStart d A - d ∧ 2 ≤ avoiderStart d A - d ∨
        x = avoiderStart d A + A.card * d ∧ avoiderStart d A + A.card * d ≤ N) :
      x ∉ A := by
    obtain ⟨_, hap⟩ := havoid A hA hone
    obtain ⟨ha, hp, hnorm, hlast⟩ := avoiderForm (hsub A hA) hone hap
    intro hxA
    have hxR : x ∈ apRange (avoiderStart d A) d A.card := by
      rw [← hnorm]
      exact hxA
    obtain ⟨i, hi, hxi⟩ : ∃ i < A.card, x = avoiderStart d A + i * d := by
      simpa [apRange, eq_comm] using hxR
    have hb : avoiderStart d A ≤ x ∧
        x ≤ avoiderStart d A + (A.card - 1) * d := by
      constructor
      · omega
      · have hmul := Nat.mul_le_mul_right d (show i ≤ A.card - 1 by omega)
        omega
    have hrel : avoiderStart d A + (A.card - 1) * d + d =
        avoiderStart d A + A.card * d := by
      calc
        _ = avoiderStart d A + (A.card - 1 + 1) * d := by rw [Nat.add_mul, one_mul]; omega
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ A.card)]
    rcases hleft with ⟨hx, _⟩ | ⟨hx, _⟩ <;> omega
  rcases point_cases S hcS with hsp | hsl | hsr
  · rcases point_cases T hcT with htp | htl | htr
    · obtain ⟨honeS, hcardS, hxS⟩ := hsp
      obtain ⟨honeT, hcardT, hxT⟩ := htp
      have hSform := (pointNormal S (hsub S hS) honeS hcardS).1
      have hTform := (pointNormal T (hsub T hT) honeT hcardT).1
      exact hne (calc
        S = {1, S.sup id} := hSform
        _ = {1, x} := by rw [← hxS]
        _ = {1, T.sup id} := by rw [hxT]
        _ = T := hTform.symm)
    · obtain ⟨honeS, hcardS, hxS⟩ := hsp
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htl
      have hSform := (pointNormal S (hsub S hS) honeS hcardS).1
      rw [← hxS] at hSform
      have hxT' : x ∈ T := smallPoint T
        (hSform ▸ hS) hT honeT
      exact outside T hT honeT (Or.inl ⟨hxT, hlT⟩) hxT'
    · obtain ⟨honeS, hcardS, hxS⟩ := hsp
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htr
      have hSform := (pointNormal S (hsub S hS) honeS hcardS).1
      rw [← hxS] at hSform
      have hxT' : x ∈ T := smallPoint T
        (hSform ▸ hS) hT honeT
      exact outside T hT honeT (Or.inr ⟨hxT, hrT⟩) hxT'
  · rcases point_cases T hcT with htp | htl | htr
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsl
      obtain ⟨honeT, hcardT, hxT⟩ := htp
      have hTform := (pointNormal T (hsub T hT) honeT hcardT).1
      rw [← hxT] at hTform
      have hxS' : x ∈ S := smallPoint S
        (hTform ▸ hT) hS honeS
      exact outside S hS honeS (Or.inl ⟨hxS, hlS⟩) hxS'
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsl
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htl
      obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haS, hpS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS hapS
      obtain ⟨haT, hpT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT hapT
      have heq : avoiderStart d S - d = avoiderStart d T - d := hxS.symm.trans hxT
      have hrec := avoider_left_point_recovery hd hpS hpT hlS hlT hlastS hlastT
        hrS hrT heq
      exact hne (hnormS.trans (hrec.trans hnormT.symm))
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsl
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htr
      obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haS, hpS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS hapS
      obtain ⟨haT, hpT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT hapT
      have hdis := avoider_opposite_point_disjoint (m := S.card) hd hpT
        (hxS.symm.trans hxT)
      change S = apRange aS d S.card at hnormS
      change T = apRange aT d T.card at hnormT
      have hdis' : Disjoint S T := by rw [hnormS, hnormT]; exact hdis
      obtain ⟨z, hz⟩ := meet
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
  · rcases point_cases T hcT with htp | htl | htr
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsr
      obtain ⟨honeT, hcardT, hxT⟩ := htp
      have hTform := (pointNormal T (hsub T hT) honeT hcardT).1
      rw [← hxT] at hTform
      have hxS' : x ∈ S := smallPoint S
        (hTform ▸ hT) hS honeS
      exact outside S hS honeS (Or.inr ⟨hxS, hrS⟩) hxS'
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsr
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htl
      obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haS, hpS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS hapS
      obtain ⟨haT, hpT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT hapT
      have hdis := avoider_opposite_point_disjoint (m := T.card) hd hpS
        (hxT.symm.trans hxS)
      change S = apRange aS d S.card at hnormS
      change T = apRange aT d T.card at hnormT
      have hdis' : Disjoint S T := by rw [hnormS, hnormT]; exact hdis.symm
      obtain ⟨z, hz⟩ := meet
      exact Finset.disjoint_left.mp hdis' (Finset.mem_inter.mp hz).1
        (Finset.mem_inter.mp hz).2
    · obtain ⟨honeS, hlS, hrS, hxS⟩ := hsr
      obtain ⟨honeT, hlT, hrT, hxT⟩ := htr
      obtain ⟨_, hapS⟩ := havoid S hS honeS
      obtain ⟨_, hapT⟩ := havoid T hT honeT
      obtain ⟨haS, hpS, hnormS, hlastS⟩ := avoiderForm (hsub S hS) honeS hapS
      obtain ⟨haT, hpT, hnormT, hlastT⟩ := avoiderForm (hsub T hT) honeT hapT
      have heq : avoiderStart d S + S.card * d = avoiderStart d T + T.card * d :=
        hxS.symm.trans hxT
      have hrec := avoider_right_point_recovery hd haS haT hlS hlT heq
      exact hne (hnormS.trans (hrec.trans hnormT.symm))

end D5.S3.Combinatorics.APIntersectionBoundaryEndgame
