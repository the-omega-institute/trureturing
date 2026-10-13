/- GID: D5/S3/Arith/FibonacciAtomic/LegalConditionedSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LegalConditionedSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive product laws separate effective teacher signatures after legal conditioning. -/

import D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
import D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.LegalConditionedSeparation

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last bits flatten)
open D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
open D5.S3.Arith.ZeckendorfFutureKernel (legal)
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping

/-- Whole zero windows remain positions; this operation does not trim a word. -/
def overwrite {n : ℕ} (support : Finset (Fin n)) (assignment x : Input n) : Input n :=
  fun i => if i ∈ support then assignment i else x i

/-- The partition function for the original initial-false seam predicate. -/
noncomputable def legalNormalizer {n : ℕ} (laws : Fin n → FiniteResponseLaw Window) : ℚ := by
  classical
  exact ∑ x : Input n, if Legal x then (independentSourceLaw laws).mass x else 0

/-- Exact disagreement probability obtained by conditioning the full product law.
There is no terminal End condition and no independence premise after conditioning. -/
noncomputable def conditionedDisagreement {n : ℕ}
    (laws : Fin n → FiniteResponseLaw Window) (t u : Roles n) : ℚ := by
  classical
  exact (∑ x : Input n,
    if Legal x ∧ teacher t x ≠ teacher u x then
      (independentSourceLaw laws).mass x else 0) / legalNormalizer laws

set_option maxHeartbeats 1200000 in
/-- Uniform quantitative separation on the actual five-window legal carrier.
The elementary laws supply positivity and normalization; the legal partition
function, safe separating assignment, and division bound are consequences. -/
theorem result {n : ℕ} (laws : Fin n → FiniteResponseLaw Window)
    (rho : ℚ) (rho_pos : 0 < rho)
    (lower : ∀ i a, rho ≤ (laws i).mass a)
    (t u : Roles n) (different : signature t ≠ signature u) :
    0 < legalNormalizer laws ∧ rho ^ 5 ≤ conditionedDisagreement laws t u := by
  classical
  have legal_list (w : List Window) (s : Bool) :
      legal s (flatten w) ↔
        (∀ b ∈ w.head?, ¬ (s = true ∧ first b = true)) ∧
        w.IsChain (fun a b => ¬ (last a = true ∧ first b = true)) := by
    induction w generalizing s with
    | nil => simp [flatten, legal]
    | cons a w ih =>
      have ha : legal s (bits a ++ flatten w) ↔
          ¬ (s = true ∧ first a = true) ∧ legal (last a) (flatten w) := by
        cases s <;> cases a <;> simp [bits, first, last, legal]
      change legal s (bits a ++ flatten w) ↔ _
      rw [ha, ih]
      cases w <;> simp [List.isChain_cons]
  have legal_iff (x : Input n) : Legal x ↔
      ∀ i j : Fin n, i.val + 1 = j.val →
        ¬ (last (x i) = true ∧ first (x j) = true) := by
    rw [Legal, legal_list]
    simp only [Bool.false_eq_true, false_and, not_false_eq_true, implies_true,
      true_and, List.isChain_ofFn]
    constructor
    · intro h i j hij
      have hj : i.val + 1 < n := hij ▸ j.isLt
      simpa only [Fin.eta, Fin.ext_iff, hij] using h i.val hj
    · intro h i hi
      exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have adjacent_zero (x : Input n) (hx : Legal x) (i j : Fin n)
      (hij : i < j) (hgap : ¬ i.val + 1 < j.val) : gate x i j = false := by
    have hadj : i.val + 1 = j.val := by
      change i.val < j.val at hij
      omega
    have hh := (legal_iff x).1 hx i j hadj
    cases hi : last (x i) <;> cases hj : first (x j) <;> simp_all [gate]
  have equal_gates (x : Input n) (hx : Legal x)
      (i j a b : Fin n) (hij : i < j) (hab : a < b)
      (he : edge i j = edge a b) : gate x i j = gate x a b := by
    by_cases hg : i.val + 1 < j.val
    · have hg' : a.val + 1 < b.val := by
        by_contra hn
        simp [edge, hg, hn] at he
      have hp : i = a ∧ j = b := by simpa [edge, hg, hg'] using he
      rw [hp.1, hp.2]
    · have hg' : ¬ a.val + 1 < b.val := by
        intro hh
        simp [edge, hg, hh] at he
      rw [adjacent_zero x hx i j hij hg, adjacent_zero x hx a b hab hg']

  have safe_pattern (i j z : Fin n) (gap : i.val + 1 < j.val) :
      ∃ S : Finset (Fin n), ∃ a : Input n,
        S.card ≤ 5 ∧
        (∀ x, Legal x → Legal (overwrite S a x)) ∧
        (∀ x, last (overwrite S a x i) = true ∧
          first (overwrite S a x i) = false ∧
          first (overwrite S a x j) = true ∧
          last (overwrite S a x j) = false ∧
          (z ≠ i → z ≠ j → overwrite S a x z = Window.zero)) := by
    let next : Fin n := ⟨i.val + 1, by omega⟩
    let prev : Fin n := ⟨j.val - 1, by omega⟩
    let S : Finset (Fin n) := {i, j, next, prev, z}
    let a : Input n := fun k => if k = i then Window.high
      else if k = j then Window.low else Window.zero
    have ji : j ≠ i := by intro h; have := congrArg Fin.val h; omega
    have forced_last (k : Fin n) : last (a k) = true ↔ k = i := by
      by_cases hi : k = i
      · simp [a, hi, last]
      · by_cases hj : k = j <;> simp [a, hi, hj, ji, last]
    have forced_first (k : Fin n) : first (a k) = true ↔ k = j := by
      by_cases hi : k = i
      · simp [a, hi, first, Ne.symm ji]
      · by_cases hj : k = j <;> simp [a, hi, hj, ji, first]
    refine ⟨S, a, Finset.card_le_five, ?_, ?_⟩
    · intro x hx
      apply (legal_iff _).2
      intro k l hkl hbad
      by_cases hk : k ∈ S
      · have ki : k = i := (forced_last k).mp (by
          simpa [overwrite, hk] using hbad.1)
        by_cases hl : l ∈ S
        · have lj : l = j := (forced_first l).mp (by
            simpa [overwrite, hl] using hbad.2)
          subst k
          subst l
          omega
        · have ln : l = next := by
            apply Fin.ext
            dsimp [next]
            subst k
            omega
          exact hl (by simp [S, ln])
      · by_cases hl : l ∈ S
        · have lj : l = j := (forced_first l).mp (by
            simpa [overwrite, hl] using hbad.2)
          have kp : k = prev := by
            apply Fin.ext
            dsimp [prev]
            subst l
            omega
          exact hk (by simp [S, kp])
        · exact (legal_iff x).1 hx k l hkl (by
            simpa [overwrite, hk, hl] using hbad)
    · intro x
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [overwrite, S, a, last]
      · simp [overwrite, S, a, first]
      · simp [overwrite, S, a, first, ji]
      · simp [overwrite, S, a, last, ji]
      · intro zi zj
        simp [overwrite, S, a, zi, zj]

  have edge_pattern (i j a b : Fin n) (hij : i < j) (hab : a < b)
      (gap : i.val + 1 < j.val) (unequal : edge i j ≠ edge a b) :
      ∃ S : Finset (Fin n), ∃ pat : Input n,
        S.card ≤ 5 ∧ (∀ x, Legal x → Legal (overwrite S pat x)) ∧
        (∀ x, Legal x →
          gate (overwrite S pat x) i j = true ∧
          gate (overwrite S pat x) a b = false ∧
          first (overwrite S pat x i) = false) := by
    by_cases rival : a.val + 1 < b.val
    · have pair_ne : (a, b) ≠ (i, j) := by
        intro h
        apply unequal
        have ai : a = i := congrArg Prod.fst h
        have bj : b = j := congrArg Prod.snd h
        simp [edge, gap, ai, bj]
      have blocker : ∃ z : Fin n, z ≠ i ∧ z ≠ j ∧ (z = a ∨ z = b) := by
        by_cases ai : a = i
        · refine ⟨b, ?_, ?_, Or.inr rfl⟩
          · intro bi
            have hab' : a.val < b.val := hab
            have := congrArg Fin.val ai
            have := congrArg Fin.val bi
            omega
          · intro bj
            exact pair_ne (Prod.ext ai bj)
        · by_cases aj : a = j
          · refine ⟨b, ?_, ?_, Or.inr rfl⟩
            · intro bi
              have hij' : i.val < j.val := hij
              have hab' : a.val < b.val := hab
              have := congrArg Fin.val aj
              have := congrArg Fin.val bi
              omega
            · intro bj
              have hab' : a.val < b.val := hab
              have := congrArg Fin.val aj
              have := congrArg Fin.val bj
              omega
          · exact ⟨a, ai, aj, Or.inl rfl⟩
      obtain ⟨z, zi, zj, hz⟩ := blocker
      obtain ⟨S, pat, card, safe, pins⟩ := safe_pattern i j z gap
      refine ⟨S, pat, card, safe, ?_⟩
      intro x hx
      obtain ⟨hi, fi, fj, _, zero⟩ := pins x
      refine ⟨by simp [gate, hi, fj], ?_, fi⟩
      have hz0 := zero zi zj
      rcases hz with za | zb
      · have ha0 : overwrite S pat x a = Window.zero := by simpa [za] using hz0
        simp [gate, ha0, last]
      · have hb0 : overwrite S pat x b = Window.zero := by simpa [zb] using hz0
        simp [gate, hb0, first]
    · obtain ⟨S, pat, card, safe, pins⟩ := safe_pattern i j i gap
      refine ⟨S, pat, card, safe, ?_⟩
      intro x hx
      obtain ⟨hi, fi, fj, _, _⟩ := pins x
      exact ⟨by simp [gate, hi, fj],
        adjacent_zero _ (safe x hx) a b hab rival, fi⟩

  have first_certificate (v w : Roles n) (gap : v.p.val + 1 < v.q.val)
      (unequal : edge v.p v.q ≠ edge w.p w.q) :
      ∃ S : Finset (Fin n), ∃ pat : Input n, S.card ≤ 5 ∧
        ∀ x, Legal x → Legal (overwrite S pat x) ∧
          teacher v (overwrite S pat x) ≠ teacher w (overwrite S pat x) := by
    obtain ⟨S, pat, card, safe, gates⟩ :=
      edge_pattern v.p v.q w.p w.q v.pq w.pq gap unequal
    refine ⟨S, pat, card, ?_⟩
    intro x hx
    obtain ⟨on, off, _⟩ := gates x hx
    refine ⟨safe x hx, ?_⟩
    cases hh : gate (overwrite S pat x) w.q w.r <;>
      simp [teacher, on, off, hh]
  have second_certificate (v w : Roles n) (gap : v.q.val + 1 < v.r.val)
      (first_same : edge v.p v.q = edge w.p w.q)
      (unequal : edge v.q v.r ≠ edge w.q w.r) :
      ∃ S : Finset (Fin n), ∃ pat : Input n, S.card ≤ 5 ∧
        ∀ x, Legal x → Legal (overwrite S pat x) ∧
          teacher v (overwrite S pat x) ≠ teacher w (overwrite S pat x) := by
    obtain ⟨S, pat, card, safe, gates⟩ :=
      edge_pattern v.q v.r w.q w.r v.qr w.qr gap unequal
    refine ⟨S, pat, card, ?_⟩
    intro x hx
    obtain ⟨on, off, fi⟩ := gates x hx
    have first_off : gate (overwrite S pat x) v.p v.q = false := by simp [gate, fi]
    have other_off : gate (overwrite S pat x) w.p w.q = false :=
      (equal_gates _ (safe x hx) v.p v.q w.p w.q v.pq w.pq first_same).symm.trans first_off
    exact ⟨safe x hx, by simp [teacher, first_off, other_off, on, off]⟩
  have certificate : ∃ S : Finset (Fin n), ∃ pat : Input n, S.card ≤ 5 ∧
      ∀ x, Legal x → Legal (overwrite S pat x) ∧
        teacher t (overwrite S pat x) ≠ teacher u (overwrite S pat x) := by
    by_cases hfirst : edge t.p t.q = edge u.p u.q
    · have hsecond : edge t.q t.r ≠ edge u.q u.r := by
        intro h
        exact different (Prod.ext hfirst h)
      by_cases ht : t.q.val + 1 < t.r.val
      · exact second_certificate t u ht hfirst hsecond
      · have hu : u.q.val + 1 < u.r.val := by
          by_contra hn
          simp [edge, ht, hn] at hsecond
        obtain ⟨S, pat, card, hh⟩ :=
          second_certificate u t hu hfirst.symm (Ne.symm hsecond)
        exact ⟨S, pat, card, fun x hx => ⟨(hh x hx).1, Ne.symm (hh x hx).2⟩⟩
    · by_cases ht : t.p.val + 1 < t.q.val
      · exact first_certificate t u ht hfirst
      · have hu : u.p.val + 1 < u.q.val := by
          by_contra hn
          simp [edge, ht, hn] at hfirst
        obtain ⟨S, pat, card, hh⟩ := first_certificate u t hu (Ne.symm hfirst)
        exact ⟨S, pat, card, fun x hx => ⟨(hh x hx).1, Ne.symm (hh x hx).2⟩⟩

  let P := independentSourceLaw laws
  have P_nonneg (x : Input n) : 0 ≤ P.mass x := P.nonnegative x
  have P_pos (x : Input n) : 0 < P.mass x := by
    change 0 < ∏ i, (laws i).mass (x i)
    exact Finset.prod_pos (fun i _ => rho_pos.trans_le (lower i (x i)))
  have Z_pos : 0 < legalNormalizer laws := by
    let zero : Input n := fun _ => Window.zero
    have zero_legal : Legal zero := (legal_iff zero).2 (by
      intro i j _
      simp [zero, last, first])
    have hsingle : P.mass zero ≤ legalNormalizer laws := by
      simpa [legalNormalizer, zero_legal] using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x : Input n => if Legal x then P.mass x else 0)
          (fun x _ => by split_ifs; exacts [P_nonneg x, le_rfl])
          (Finset.mem_univ zero))
    exact (P_pos zero).trans_le hsingle
  have rho_le_one : rho ≤ 1 := by
    have hs : (laws t.p).mass Window.zero ≤ ∑ a, (laws t.p).mass a :=
      Finset.single_le_sum (fun a _ => (laws t.p).nonnegative a) (Finset.mem_univ _)
    exact (lower t.p Window.zero).trans (hs.trans_eq (laws t.p).total)
  obtain ⟨S, pat, card, repair⟩ := certificate
  let Inside := {i : Fin n // i ∈ S}
  let Outside := {i : Fin n // i ∉ S}
  let A := Inside → Window
  let B := Outside → Window
  let split := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ S) (fun _ => Window)
  let left := independentSourceLaw (fun i : Inside => laws i.1)
  let right := independentSourceLaw (fun i : Outside => laws i.1)
  let merge : A → B → Input n := fun a b => split.symm (a, b)
  let fixed : A := fun i => pat i.1
  let W : B → ℚ := fun b => ∑ a : A, if Legal (merge a b) then left.mass a else 0
  let D : B → ℚ := fun b => ∑ a : A,
    if Legal (merge a b) ∧ teacher t (merge a b) ≠ teacher u (merge a b)
      then left.mass a else 0
  have at_merge (a : A) (b : B) : P.mass (merge a b) = left.mass a * right.mass b := by
    have h := independentSource_mass_split laws S (merge a b)
    simpa only [P, merge, split, Equiv.apply_symm_apply, productResponseMass] using h
  have fixed_overwrite (a : A) (b : B) :
      overwrite S pat (merge a b) = merge fixed b := by
    funext i
    by_cases hi : i ∈ S
    · simp [overwrite, merge, split, Equiv.piEquivPiSubtypeProd, fixed, hi]
    · simp [overwrite, merge, split, Equiv.piEquivPiSubtypeProd, hi]
  have W_le_one (b : B) : W b ≤ 1 := by
    calc
      W b ≤ ∑ a : A, left.mass a := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs; exacts [le_rfl, left.nonnegative a]
      _ = 1 := left.total
  have D_nonneg (b : B) : 0 ≤ D b := by
    apply Finset.sum_nonneg
    intro a _
    split_ifs; exacts [left.nonnegative a, le_rfl]
  have fiber_bound (b : B) : left.mass fixed * W b ≤ D b := by
    by_cases completable : ∃ a : A, Legal (merge a b)
    · obtain ⟨a, ha⟩ := completable
      have hh := repair (merge a b) ha
      rw [fixed_overwrite a b] at hh
      have atom : left.mass fixed ≤ D b := by
        simpa only [D, if_pos hh] using
          (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun a : A =>
              if Legal (merge a b) ∧ teacher t (merge a b) ≠ teacher u (merge a b)
                then left.mass a else 0)
            (fun a _ => by split_ifs; exacts [left.nonnegative a, le_rfl])
            (Finset.mem_univ fixed))
      exact (mul_le_of_le_one_right (left.nonnegative fixed) (W_le_one b)).trans atom
    · have W_zero : W b = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : ¬ Legal (merge a b) := fun h => completable ⟨a, h⟩
        simp [ha]
      rw [W_zero, mul_zero]
      exact D_nonneg b
  have regroup (event : Input n → Prop) [DecidablePred event] :
      (∑ x : Input n, if event x then P.mass x else 0) =
        ∑ b : B, right.mass b *
          ∑ a : A, if event (merge a b) then left.mass a else 0 := by
    calc
      (∑ x : Input n, if event x then P.mass x else 0) =
          ∑ z : A × B, if event (split.symm z) then P.mass (split.symm z) else 0 :=
        (split.symm.sum_comp (fun x => if event x then P.mass x else 0)).symm
      _ = ∑ b : B, ∑ a : A,
          if event (merge a b) then left.mass a * right.mass b else 0 := by
        rw [Fintype.sum_prod_type_right]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        change (if event (merge a b) then P.mass (merge a b) else 0) = _
        rw [at_merge]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp [mul_comm]
  have normalizer_split : legalNormalizer laws = ∑ b : B, right.mass b * W b := by
    exact regroup Legal
  let numerator : ℚ := ∑ x : Input n,
    if Legal x ∧ teacher t x ≠ teacher u x then P.mass x else 0
  have numerator_split : numerator = ∑ b : B, right.mass b * D b := by
    simpa [numerator, D] using
      regroup (fun x => Legal x ∧ teacher t x ≠ teacher u x)
  have weighted : left.mass fixed * legalNormalizer laws ≤ numerator := by
    rw [normalizer_split, numerator_split, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    calc
      left.mass fixed * (right.mass b * W b) =
          right.mass b * (left.mass fixed * W b) := by ring
      _ ≤ right.mass b * D b :=
        mul_le_mul_of_nonneg_left (fiber_bound b) (right.nonnegative b)
  have fixed_lower : rho ^ S.card ≤ left.mass fixed := by
    have hp : (∏ _i : Inside, rho) ≤ ∏ i : Inside, (laws i.1).mass (fixed i) :=
      Finset.prod_le_prod₀ (fun _ _ => rho_pos.le) (fun i _ => lower i.1 (fixed i))
    have hcard : Fintype.card Inside = S.card := Fintype.card_coe S
    simpa only [Finset.prod_const, Finset.card_univ, hcard, left,
      independentSourceLaw] using hp
  have power_lower : rho ^ 5 ≤ left.mass fixed :=
    (pow_le_pow_of_le_one rho_pos.le rho_le_one card).trans fixed_lower
  have division : left.mass fixed ≤ numerator / legalNormalizer laws :=
    (le_div_iff₀ Z_pos).2 weighted
  exact ⟨Z_pos, power_lower.trans division⟩

#print axioms result

end D5.S3.Arith.FibonacciAtomic.LegalConditionedSeparation
