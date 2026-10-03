/- GID: D5/S3/ConceptDynamics/PartialIdentification/GraphPrioritySeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/GraphPrioritySeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Local graph guards separate priority classifiers under global legal conditioning. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.GraphPrioritySeparation

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping

structure Roles (V : Type*) [LT V] where
  p : V
  q : V
  r : V
  pq : p < q
  qr : q < r

variable {V Symbol : Type*} [Fintype V] [LinearOrder V] [Fintype Symbol]

def Legal (G : V → V → Prop) (first last : Symbol → Bool) (x : V → Symbol) : Prop :=
  ∀ i j, G i j → ¬ (last (x i) = true ∧ first (x j) = true)

def gate (first last : Symbol → Bool) (x : V → Symbol) (i j : V) : Bool :=
  last (x i) && first (x j)

def teacher (first last : Symbol → Bool) (t : Roles V) (x : V → Symbol) : Fin 3 :=
  if gate first last x t.p t.q then 1 else if gate first last x t.q t.r then 2 else 0

noncomputable def edge (G : V → V → Prop) (i j : V) : Option (V × V) := by
  classical
  exact if G i j then none else some (i,j)

noncomputable def signature (G : V → V → Prop) (t : Roles V) :=
  (edge G t.p t.q, edge G t.q t.r)

noncomputable def outgoing (G : V → V → Prop) (i : V) : Finset V := by
  classical
  exact Finset.univ.filter (G i)

noncomputable def incoming (G : V → V → Prop) (j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => G i j)

def overwrite (support : Finset V) (assignment x : V → Symbol) : V → Symbol :=
  fun i => if i ∈ support then assignment i else x i

noncomputable def legalNormalizer (G : V → V → Prop) (first last : Symbol → Bool)
    (laws : V → FiniteResponseLaw Symbol) : ℚ := by
  classical
  exact ∑ x : V → Symbol, if Legal G first last x then (independentSourceLaw laws).mass x else 0

noncomputable def conditionedDisagreement (G : V → V → Prop) (first last : Symbol → Bool)
    (laws : V → FiniteResponseLaw Symbol) (t u : Roles V) : ℚ := by
  classical
  exact (∑ x : V → Symbol, if Legal G first last x ∧
    teacher first last t x ≠ teacher first last u x then
    (independentSourceLaw laws).mass x else 0) / legalNormalizer G first last laws

set_option maxHeartbeats 1800000 in
/-- Arbitrary directed constraints, including loops, admit degree-controlled
separating repairs. The original product law is conditioned on all constraints
at once; the resulting coordinates are allowed to be dependent. -/
theorem result (G : V → V → Prop) (first last : Symbol → Bool)
    (zero high low : Symbol)
    (zero_bits : first zero = false ∧ last zero = false)
    (high_bits : first high = false ∧ last high = true)
    (low_bits : first low = true ∧ last low = false)
    (dout din : ℕ)
    (out_bound : ∀ i, (outgoing G i).card ≤ dout)
    (in_bound : ∀ j, (incoming G j).card ≤ din)
    (laws : V → FiniteResponseLaw Symbol) (rho : ℚ) (rho_pos : 0 < rho)
    (lower : ∀ i a, rho ≤ (laws i).mass a) :
    0 < legalNormalizer G first last laws ∧
    ∀ t u : Roles V,
    ((∀ x : V → Symbol, Legal G first last x →
        teacher first last t x = teacher first last u x) ↔ signature G t = signature G u) ∧
    (signature G t ≠ signature G u →
      rho ^ (dout + din + 3) ≤ conditionedDisagreement G first last laws t u) := by
  classical
  let L := Legal G first last
  let C : Roles V → (V → Symbol) → Fin 3 := teacher first last
  let e := edge G
  let sig := signature G
  have forbidden_zero (x : V → Symbol) (hx : L x) (i j : V)
      (hij : G i j) : gate first last x i j = false := by
    have hh := hx i j hij
    cases hi : last (x i) <;> cases hj : first (x j) <;> simp_all [gate]
  have equal_gates (x : V → Symbol) (hx : L x) (i j a b : V)
      (he : e i j = e a b) : gate first last x i j = gate first last x a b := by
    by_cases hg : G i j
    · have hg' : G a b := by
        by_contra hn
        simp [e, edge, hg, hn] at he
      rw [forbidden_zero x hx i j hg, forbidden_zero x hx a b hg']
    · have hg' : ¬ G a b := by
        intro hh
        simp [e, edge, hg, hh] at he
      have hp : i = a ∧ j = b := by simpa [e, edge, hg, hg'] using he
      rw [hp.1, hp.2]
  have safe_pattern (i j z : V) (hij : i < j) (active : ¬ G i j) :
      ∃ S : Finset V, ∃ a : V → Symbol,
        S.card ≤ dout + din + 3 ∧
        (∀ x, L x → L (overwrite S a x)) ∧
        (∀ x, last (overwrite S a x i) = true ∧
          first (overwrite S a x i) = false ∧
          first (overwrite S a x j) = true ∧
          last (overwrite S a x j) = false ∧
          (z ≠ i → z ≠ j → overwrite S a x z = zero)) := by
    let S : Finset V := {i,j,z} ∪ outgoing G i ∪ incoming G j
    let a : V → Symbol := fun k => if k = i then high else if k = j then low else zero
    have ji : j ≠ i := ne_of_gt hij
    have forced_last (k : V) : last (a k) = true ↔ k = i := by
      by_cases hi : k = i
      · simp [a, hi, high_bits]
      · by_cases hj : k = j <;> simp [a, hi, hj, ji, zero_bits, low_bits]
    have forced_first (k : V) : first (a k) = true ↔ k = j := by
      by_cases hi : k = i
      · simp [a, hi, high_bits, Ne.symm ji]
      · by_cases hj : k = j <;> simp [a, hi, hj, ji, zero_bits, low_bits]
    refine ⟨S, a, ?_, ?_, ?_⟩
    · have hc1 := Finset.card_union_le ({i,j,z} : Finset V) (outgoing G i)
      have hc2 := Finset.card_union_le ({i,j,z} ∪ outgoing G i) (incoming G j)
      have hc3 : ({i,j,z} : Finset V).card ≤ 3 := Finset.card_le_three
      have ho := out_bound i
      have hn := in_bound j
      dsimp [S]
      omega
    · intro x hx k l hkl hbad
      by_cases hk : k ∈ S
      · have ki : k = i := (forced_last k).mp (by
          simpa [overwrite, hk] using hbad.1)
        by_cases hl : l ∈ S
        · have lj : l = j := (forced_first l).mp (by
            simpa [overwrite, hl] using hbad.2)
          exact active (ki ▸ lj ▸ hkl)
        · exact hl (by simp [S, outgoing, ← ki, hkl])
      · by_cases hl : l ∈ S
        · have lj : l = j := (forced_first l).mp (by
            simpa [overwrite, hl] using hbad.2)
          exact hk (by simp [S, incoming, ← lj, hkl])
        · exact hx k l hkl (by simpa [overwrite, hk, hl] using hbad)
    · intro x
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [overwrite, S, a, high_bits]
      · simp [overwrite, S, a, high_bits]
      · simp [overwrite, S, a, low_bits, ji]
      · simp [overwrite, S, a, low_bits, ji]
      · intro zi zj
        simp [overwrite, S, a, zi, zj]

  have edge_pattern (i j a b : V) (hij : i < j) (hab : a < b)
      (active : ¬ G i j) (unequal : e i j ≠ e a b) :
      ∃ S : Finset V, ∃ pat : V → Symbol, S.card ≤ dout + din + 3 ∧
        (∀ x, L x → L (overwrite S pat x)) ∧
        (∀ x, L x → gate first last (overwrite S pat x) i j = true ∧
          gate first last (overwrite S pat x) a b = false ∧
          first (overwrite S pat x i) = false) := by
    by_cases rival : G a b
    · obtain ⟨S, pat, card, safe, pins⟩ := safe_pattern i j i hij active
      refine ⟨S, pat, card, safe, ?_⟩
      intro x hx
      obtain ⟨hi, fi, fj, _, _⟩ := pins x
      exact ⟨by simp [gate, hi, fj], forbidden_zero _ (safe x hx) a b rival, fi⟩
    · have pair_ne : (a,b) ≠ (i,j) := by
        intro h
        apply unequal
        simp [e, edge, active, rival, Prod.mk.inj h]
      have blocker : ∃ z : V, z ≠ i ∧ z ≠ j ∧ (z = a ∨ z = b) := by
        by_cases ai : a = i
        · refine ⟨b, ?_, ?_, Or.inr rfl⟩
          · exact ne_of_gt (ai ▸ hab)
          · intro bj
            exact pair_ne (Prod.ext ai bj)
        · by_cases aj : a = j
          · refine ⟨b, ?_, ?_, Or.inr rfl⟩
            · exact ne_of_gt (hij.trans (aj ▸ hab))
            · exact ne_of_gt (aj ▸ hab)
          · exact ⟨a, ai, aj, Or.inl rfl⟩
      obtain ⟨z, zi, zj, hz⟩ := blocker
      obtain ⟨S, pat, card, safe, pins⟩ := safe_pattern i j z hij active
      refine ⟨S, pat, card, safe, ?_⟩
      intro x hx
      obtain ⟨hi, fi, fj, _, zero_at⟩ := pins x
      refine ⟨by simp [gate, hi, fj], ?_, fi⟩
      have hz0 := zero_at zi zj
      rcases hz with za | zb
      · have ha0 : overwrite S pat x a = zero := by simpa [za] using hz0
        simp [gate, ha0, zero_bits]
      · have hb0 : overwrite S pat x b = zero := by simpa [zb] using hz0
        simp [gate, hb0, zero_bits]
  have first_certificate (v w : Roles V) (active : ¬ G v.p v.q)
      (unequal : e v.p v.q ≠ e w.p w.q) :
      ∃ S : Finset V, ∃ pat : V → Symbol, S.card ≤ dout + din + 3 ∧
        ∀ x, L x → L (overwrite S pat x) ∧
          C v (overwrite S pat x) ≠ C w (overwrite S pat x) := by
    obtain ⟨S, pat, card, safe, gates⟩ :=
      edge_pattern v.p v.q w.p w.q v.pq w.pq active unequal
    refine ⟨S, pat, card, ?_⟩
    intro x hx
    obtain ⟨on, off, _⟩ := gates x hx
    refine ⟨safe x hx, ?_⟩
    cases hh : gate first last (overwrite S pat x) w.q w.r <;>
      simp [C, teacher, on, off, hh]
  have second_certificate (v w : Roles V) (active : ¬ G v.q v.r)
      (first_same : e v.p v.q = e w.p w.q)
      (unequal : e v.q v.r ≠ e w.q w.r) :
      ∃ S : Finset V, ∃ pat : V → Symbol, S.card ≤ dout + din + 3 ∧
        ∀ x, L x → L (overwrite S pat x) ∧
          C v (overwrite S pat x) ≠ C w (overwrite S pat x) := by
    obtain ⟨S, pat, card, safe, gates⟩ :=
      edge_pattern v.q v.r w.q w.r v.qr w.qr active unequal
    refine ⟨S, pat, card, ?_⟩
    intro x hx
    obtain ⟨on, off, fi⟩ := gates x hx
    have first_off : gate first last (overwrite S pat x) v.p v.q = false := by
      simp [gate, fi]
    have other_off : gate first last (overwrite S pat x) w.p w.q = false :=
      (equal_gates _ (safe x hx) v.p v.q w.p w.q first_same).symm.trans first_off
    exact ⟨safe x hx, by simp [C, teacher, first_off, other_off, on, off]⟩
  let P := independentSourceLaw laws
  have P_nonneg (x : V → Symbol) : 0 ≤ P.mass x := P.nonnegative x
  have P_pos (x : V → Symbol) : 0 < P.mass x := by
    change 0 < ∏ i, (laws i).mass (x i)
    exact Finset.prod_pos (fun i _ => rho_pos.trans_le (lower i (x i)))
  let zeroInput : V → Symbol := fun _ => zero
  have zero_legal : L zeroInput := by
    intro i j _
    simp [zeroInput, zero_bits]
  have Z_pos : 0 < legalNormalizer G first last laws := by
    have hsingle : P.mass zeroInput ≤ legalNormalizer G first last laws := by
      simpa [legalNormalizer, L, zero_legal] using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x : V → Symbol => if L x then P.mass x else 0)
          (fun x _ => by split_ifs; exacts [P_nonneg x, le_rfl])
          (Finset.mem_univ zeroInput))
    exact (P_pos zeroInput).trans_le hsingle
  refine ⟨Z_pos, ?_⟩
  intro t u
  have certificate (different : sig t ≠ sig u) :
      ∃ S : Finset V, ∃ pat : V → Symbol, S.card ≤ dout + din + 3 ∧
        ∀ x, L x → L (overwrite S pat x) ∧
          C t (overwrite S pat x) ≠ C u (overwrite S pat x) := by
    by_cases hfirst : e t.p t.q = e u.p u.q
    · have hsecond : e t.q t.r ≠ e u.q u.r := by
        intro h
        exact different (Prod.ext hfirst h)
      by_cases ht : G t.q t.r
      · have hu : ¬ G u.q u.r := by
          intro hn
          simp [e, edge, ht, hn] at hsecond
        obtain ⟨S, pat, card, hh⟩ :=
          second_certificate u t hu hfirst.symm (Ne.symm hsecond)
        exact ⟨S, pat, card, fun x hx => ⟨(hh x hx).1, Ne.symm (hh x hx).2⟩⟩
      · exact second_certificate t u ht hfirst hsecond
    · by_cases ht : G t.p t.q
      · have hu : ¬ G u.p u.q := by
          intro hn
          simp [e, edge, ht, hn] at hfirst
        obtain ⟨S, pat, card, hh⟩ := first_certificate u t hu (Ne.symm hfirst)
        exact ⟨S, pat, card, fun x hx => ⟨(hh x hx).1, Ne.symm (hh x hx).2⟩⟩
      · exact first_certificate t u ht hfirst
  have rho_le_one : rho ≤ 1 := by
    have hs : (laws t.p).mass zero ≤ ∑ a, (laws t.p).mass a :=
      Finset.single_le_sum (fun a _ => (laws t.p).nonnegative a) (Finset.mem_univ _)
    exact (lower t.p zero).trans (hs.trans_eq (laws t.p).total)
  refine ⟨?_, ?_⟩
  · constructor
    · intro same
      by_contra different
      obtain ⟨S, pat, _, repair⟩ := certificate different
      have h := repair zeroInput zero_legal
      exact h.2 (same _ h.1)
    · intro hs x hx
      have hp := congrArg Prod.fst hs
      have hq := congrArg Prod.snd hs
      have ep := equal_gates x hx t.p t.q u.p u.q hp
      have eq := equal_gates x hx t.q t.r u.q u.r hq
      simp only [teacher, ep, eq]
  intro different
  obtain ⟨S, pat, card, repair⟩ := certificate different
  let Inside := {i : V // i ∈ S}
  let Outside := {i : V // i ∉ S}
  let A := Inside → Symbol
  let B := Outside → Symbol
  let split := Equiv.piEquivPiSubtypeProd (fun i : V => i ∈ S) (fun _ => Symbol)
  let left := independentSourceLaw (fun i : Inside => laws i.1)
  let right := independentSourceLaw (fun i : Outside => laws i.1)
  let merge : A → B → (V → Symbol) := fun a b => split.symm (a, b)
  let fixed : A := fun i => pat i.1
  let W : B → ℚ := fun b => ∑ a : A, if L (merge a b) then left.mass a else 0
  let D : B → ℚ := fun b => ∑ a : A,
    if L (merge a b) ∧ C t (merge a b) ≠ C u (merge a b)
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
    by_cases completable : ∃ a : A, L (merge a b)
    · obtain ⟨a, ha⟩ := completable
      have hh := repair (merge a b) ha
      rw [fixed_overwrite a b] at hh
      have atom : left.mass fixed ≤ D b := by
        simpa only [D, if_pos hh] using
          (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun a : A =>
              if L (merge a b) ∧ C t (merge a b) ≠ C u (merge a b)
                then left.mass a else 0)
            (fun a _ => by split_ifs; exacts [left.nonnegative a, le_rfl])
            (Finset.mem_univ fixed))
      exact (mul_le_of_le_one_right (left.nonnegative fixed) (W_le_one b)).trans atom
    · have W_zero : W b = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha : ¬ L (merge a b) := fun h => completable ⟨a, h⟩
        simp [ha]
      rw [W_zero, mul_zero]
      exact D_nonneg b
  have regroup (event : (V → Symbol) → Prop) [DecidablePred event] :
      (∑ x : (V → Symbol), if event x then P.mass x else 0) =
        ∑ b : B, right.mass b *
          ∑ a : A, if event (merge a b) then left.mass a else 0 := by
    calc
      (∑ x : (V → Symbol), if event x then P.mass x else 0) =
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
  have normalizer_split : legalNormalizer G first last laws = ∑ b : B, right.mass b * W b := by
    exact regroup L
  let numerator : ℚ := ∑ x : (V → Symbol),
    if L x ∧ C t x ≠ C u x then P.mass x else 0
  have numerator_split : numerator = ∑ b : B, right.mass b * D b := by
    simpa [numerator, D] using
      regroup (fun x => L x ∧ C t x ≠ C u x)
  have weighted : left.mass fixed * legalNormalizer G first last laws ≤ numerator := by
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
      Finset.prod_le_prod (fun _ _ => rho_pos.le) (fun i _ => lower i.1 (fixed i))
    have hcard : Fintype.card Inside = S.card := Fintype.card_coe S
    simpa only [Finset.prod_const, Finset.card_univ, hcard, left,
      independentSourceLaw] using hp
  have power_lower : rho ^ (dout + din + 3) ≤ left.mass fixed :=
    (pow_le_pow_of_le_one rho_pos.le rho_le_one card).trans fixed_lower
  have division : left.mass fixed ≤ numerator / legalNormalizer G first last laws :=
    (le_div_iff₀ Z_pos).2 weighted
  exact power_lower.trans division

#print axioms result

end D5.S3.ConceptDynamics.PartialIdentification.GraphPrioritySeparation
