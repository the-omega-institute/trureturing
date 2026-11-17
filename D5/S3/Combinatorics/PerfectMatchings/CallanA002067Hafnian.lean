/- GID: D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both Callan A002067 conjectures hold for every natural index. -/

/-
proof_shape: result: content (unbounded involution extension and weighted-walk inductions).
escape_witness: none (the settling result supplies admission).
admission_basis: open-problem-resolution (#23975; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24743
The partner-map type is supplied by D5/S0/Certificates/Combinatorics/NormalizedPfaffian.P.
The Dyck identity also uses DepthBudgetIidGreedyOptimality.words and
SchroederPeakAlternatingQuadraticMoment.PrefixNonnegative with its Step constructors
and instances, through the delivered Dyck module.
-/

import D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
import D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
import D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation

/-! Weighted involutions connect the constant-row hafnian to the source recurrence. -/

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)

/-- The hafnian of u(i,j) = i on 1 <= i < j <= 2n.
Mathlib's perfect matching predicate is used on subgraphs of the complete graph.
For each matching, the product takes each edge once, at its smaller endpoint.
The label of a vertex i : Fin (2*n) is i.val + 1. -/
noncomputable def hafnian (n : ℕ) : ℕ := by
  classical
  exact ∑ M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph,
    if M.IsPerfectMatching then
      ∏ i : Fin (2 * n), ∏ j : Fin (2 * n),
        if i < j ∧ M.Adj i j then i.val + 1 else 1
    else 0

/-- Both consecutive Callan assertions, with sequence existence explicit. -/
def claim : Prop :=
  (∃ a : ℕ → ℕ, IsSourceSequence a) ∧
    ∀ a : ℕ → ℕ, IsSourceSequence a →
      ∀ n : ℕ, a n = hafnian n ∧ a n = weightedDyckSum n

private theorem matching_weight_row (n : ℕ)
    (M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph) (hM : M.IsPerfectMatching)
    (i : Fin (2 * n)) :
    (∏ j : Fin (2 * n), if i < j ∧ M.Adj i j then i.val + 1 else 1) =
      if i < matchingMate M hM i then i.val + 1 else 1 := by
  classical
  rw [prod_eq_single (matchingMate M hM i)]
  · simp only [matchingMate_adj M hM i, and_true]
  · intro j hj hne
    have hn : ¬ M.Adj i j := by
      intro h
      exact hne ((matchingMate_eq_iff M hM i j).mpr h).symm
    simp [hn]
  · simp

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial
attribute [local instance] Classical.propDecidable

private noncomputable def extendInvFun {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    Fin (r + 1) → Fin (r + 1) :=
  Fin.lastCases (q.elim (Fin.last r) (fun i => i.val.castSucc))
    (fun j => if ∃ i, q = some i ∧ j = i.val then Fin.last r else (f.val j).castSucc)

private theorem extendInvFun_none_last {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    extendInvFun f none (Fin.last r) = Fin.last r := by simp [extendInvFun]

private theorem extendInvFun_none_castSucc {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (j : Fin r) :
    extendInvFun f none j.castSucc = (f.val j).castSucc := by simp [extendInvFun]

private theorem extendInvFun_some_last {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    extendInvFun f (some i) (Fin.last r) = i.val.castSucc := by simp [extendInvFun]

private theorem extendInvFun_some_castSucc {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) (j : Fin r) :
    extendInvFun f (some i) j.castSucc =
      if j = i.val then Fin.last r else (f.val j).castSucc := by simp [extendInvFun]

private theorem extendInvFun_involutive {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    Function.Involutive (extendInvFun f q) := by
  intro x
  induction x using Fin.lastCases with
  | last =>
    cases q with
    | none => simp [extendInvFun_none_last]
    | some i => simp [extendInvFun_some_last, extendInvFun_some_castSucc]
  | cast j =>
    cases q with
    | none => simp [extendInvFun_none_castSucc, f.property j]
    | some i =>
      by_cases hj : j = i.val
      · subst j
        simp [extendInvFun_some_castSucc, extendInvFun_some_last]
      · have hf : f.val j ≠ i.val := by
          intro he
          have he' := congrArg f.val he
          rw [f.property j, i.property] at he'
          exact hj he'
        simp [extendInvFun_some_castSucc, hj, hf, f.property j]

private noncomputable abbrev extendInv {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} :=
  ⟨extendInvFun f q, extendInvFun_involutive f q⟩

private noncomputable def dropInvFun {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r) : Fin r :=
  if h : g.val j.castSucc = Fin.last r then j
  else ⟨(g.val j.castSucc).val, by
    have hv := (g.val j.castSucc).isLt
    have hn : (g.val j.castSucc).val ≠ r := by
      intro he; exact h (Fin.ext he)
    omega⟩

private theorem dropInvFun_last {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r)
    (h : g.val j.castSucc = Fin.last r) : dropInvFun g j = j := by
  simp [dropInvFun, h]

private theorem dropInvFun_castSucc {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r)
    (h : g.val j.castSucc ≠ Fin.last r) :
    (dropInvFun g j).castSucc = g.val j.castSucc := by
  apply Fin.ext
  simp [dropInvFun, h]

private theorem dropInvFun_involutive {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    Function.Involutive (dropInvFun g) := by
  intro j
  by_cases hj : g.val j.castSucc = Fin.last r
  · rw [dropInvFun_last g j hj, dropInvFun_last g j hj]
  · have he := dropInvFun_castSucc g j hj
    have hh : g.val (dropInvFun g j).castSucc = j.castSucc := by
      rw [he, g.property]
    have hn : g.val (dropInvFun g j).castSucc ≠ Fin.last r := by
      rw [hh]; exact Fin.castSucc_ne_last j
    have ht := dropInvFun_castSucc g (dropInvFun g j) hn
    rw [hh] at ht
    exact Fin.castSucc_inj.mp ht

private noncomputable abbrev dropInv {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) : {f : Fin r → Fin r // Function.Involutive f} :=
  ⟨dropInvFun g, dropInvFun_involutive g⟩

private noncomputable def partner {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) : Option ({i : _ // (dropInv g).val i = i}) :=
  if h : g.val (Fin.last r) = Fin.last r then none
  else some ⟨⟨(g.val (Fin.last r)).val, by
      have hv := (g.val (Fin.last r)).isLt
      have hn : (g.val (Fin.last r)).val ≠ r := by
        intro he; exact h (Fin.ext he)
      omega⟩, by
    apply dropInvFun_last
    have hg := g.property (Fin.last r)
    convert hg using 1
    apply congrArg g.val
    apply Fin.ext
    rfl⟩

private theorem drop_extend {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    dropInv (extendInv f q) = f := by
  apply Subtype.ext
  funext j
  cases q with
  | none =>
    apply Fin.castSucc_inj.mp
    calc
      (dropInvFun (extendInv f none) j).castSucc =
          (extendInv f none).val j.castSucc := dropInvFun_castSucc _ _ (by
            simp [extendInv, extendInvFun_none_castSucc, Fin.castSucc_ne_last])
      _ = (f.val j).castSucc := extendInvFun_none_castSucc f j
  | some i =>
    by_cases hj : j = i.val
    · subst j
      change dropInvFun (extendInv f (some i)) i.val = f.val i.val
      rw [dropInvFun_last _ _ (by simp [extendInv, extendInvFun_some_castSucc]), i.property]
    · apply Fin.castSucc_inj.mp
      calc
        (dropInvFun (extendInv f (some i)) j).castSucc =
            (extendInv f (some i)).val j.castSucc := dropInvFun_castSucc _ _ (by
              simp [extendInv, extendInvFun_some_castSucc, hj, Fin.castSucc_ne_last])
        _ = (f.val j).castSucc := by simp [extendInv, extendInvFun_some_castSucc, hj]

private theorem partner_image {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    (partner g).elim (Fin.last r) (fun i => i.val.castSucc) = g.val (Fin.last r) := by
  unfold partner
  split
  · rename_i h
    exact h.symm
  · simp only [Option.elim_some]
    apply Fin.ext
    rfl

private theorem extend_drop {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    extendInv (dropInv g) (partner g) = g := by
  apply Subtype.ext
  funext x
  have he := partner_image g
  induction x using Fin.lastCases with
  | last => simpa only [extendInv, extendInvFun, Fin.lastCases_last] using he
  | cast j =>
    cases hq : partner g with
    | none =>
      rw [hq] at he
      simp only [Option.elim_none] at he
      have hn : g.val j.castSucc ≠ Fin.last r := by
        intro hh
        have ht := congrArg g.val hh
        rw [g.property, ← he] at ht
        exact Fin.castSucc_ne_last j ht
      change extendInvFun (dropInv g) none j.castSucc = g.val j.castSucc
      rw [extendInvFun_none_castSucc]
      exact dropInvFun_castSucc g j hn
    | some i =>
      rw [hq] at he
      simp only [Option.elim_some] at he
      change extendInvFun (dropInv g) (some i) j.castSucc = g.val j.castSucc
      rw [extendInvFun_some_castSucc]
      by_cases hj : j = i.val
      · rw [if_pos hj, hj, he, g.property]
      · rw [if_neg hj]
        apply dropInvFun_castSucc
        intro hh
        have ht := congrArg g.val hh
        rw [g.property, ← he] at ht
        exact hj (Fin.castSucc_inj.mp ht)

private theorem extend_injective (r : ℕ) :
    Function.Injective (fun s : (Σ f : {f : Fin r → Fin r // Function.Involutive f}, Option ({i : _ // (f).val i = i})) => extendInv s.1 s.2) := by
  rintro ⟨f, q⟩ ⟨f', q'⟩ h
  have hf := congrArg dropInv h
  simp only [drop_extend] at hf
  cases hf
  have he := congrArg (fun g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} => g.val (Fin.last r)) h
  have hq : q = q' := by
    cases q with
    | none =>
      cases q' with
      | none => rfl
      | some i =>
        simp only [extendInv, extendInvFun_none_last, extendInvFun_some_last] at he
        exact False.elim ((Fin.castSucc_ne_last i.val) he.symm)
    | some i =>
      cases q' with
      | none =>
        simp only [extendInv, extendInvFun_none_last, extendInvFun_some_last] at he
        exact False.elim ((Fin.castSucc_ne_last i.val) he)
      | some i' =>
        simp only [extendInv, extendInvFun_some_last] at he
        have hi : i = i' := Subtype.ext (Fin.castSucc_inj.mp he)
        subst i'
        rfl
  subst q'
  rfl

private noncomputable def invSuccEquiv (r : ℕ) :
    (Σ f : {f : Fin r → Fin r // Function.Involutive f}, Option ({i : _ // (f).val i = i})) ≃ {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} :=
  Equiv.ofBijective (fun s => extendInv s.1 s.2)
    ⟨extend_injective r, fun g => ⟨⟨dropInv g, partner g⟩, extend_drop g⟩⟩

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial
attribute [local instance] Classical.propDecidable

private noncomputable def invWeight {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) : ℕ :=
  ∏ i : Fin r, if i ≤ f.val i then i.val + 1 else 1

private noncomputable def invMonomial {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) : Polynomial ℕ :=
  C (invWeight f) * X ^ (Fintype.card {x : _ // (f).val x = x})

private noncomputable def invSum (r : ℕ) : Polynomial ℕ := ∑ f : {f : Fin r → Fin r // Function.Involutive f}, invMonomial f

private theorem fixedCount_sum {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (f).val x = x}) = ∑ j : Fin r, if f.val j = j then 1 else 0 := by
  classical
  rw [Fintype.card_subtype, card_filter]

private theorem invWeight_none {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    invWeight (extendInv f none) = (r + 1) * invWeight f := by
  unfold invWeight
  rw [Fin.prod_univ_castSucc]
  simp only [extendInv, extendInvFun_none_last, le_refl, ↓reduceIte,
    Fin.val_last, extendInvFun_none_castSucc, Fin.castSucc_le_castSucc_iff,
    Fin.val_castSucc]
  exact mul_comm _ _

private theorem invWeight_some {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    invWeight (extendInv f (some i)) = invWeight f := by
  unfold invWeight
  rw [Fin.prod_univ_castSucc]
  have hn : ¬ Fin.last r ≤ i.val.castSucc := by
    intro h
    have := i.val.isLt
    change r ≤ i.val.val at h
    omega
  simp only [extendInv, extendInvFun_some_last, hn, ↓reduceIte, mul_one]
  apply prod_congr rfl
  intro j hj
  simp only [extendInvFun_some_castSucc]
  by_cases he : j = i.val
  · subst j
    have hi : i.val.castSucc ≤ Fin.last r := by exact Fin.le_last _
    simp [i.property, hi]
  · simp [he]

private theorem fixedCount_none {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (extendInv f none).val x = x}) = (Fintype.card {x : _ // (f).val x = x}) + 1 := by
  rw [fixedCount_sum, fixedCount_sum, Fin.sum_univ_castSucc]
  simp only [extendInv, extendInvFun_none_last, ↓reduceIte,
    extendInvFun_none_castSucc, Fin.castSucc_inj]

private theorem fixedCount_some {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    (Fintype.card {x : _ // (extendInv f (some i)).val x = x}) + 1 = (Fintype.card {x : _ // (f).val x = x}) := by
  rw [fixedCount_sum, fixedCount_sum, Fin.sum_univ_castSucc]
  simp only [extendInv, extendInvFun_some_last, Fin.castSucc_ne_last, ↓reduceIte, add_zero]
  have he : ∀ j : Fin r,
      (if extendInvFun f (some i) j.castSucc = j.castSucc then 1 else 0) +
        (if j = i.val then 1 else 0) = if f.val j = j then 1 else 0 := by
    intro j
    rw [extendInvFun_some_castSucc]
    by_cases hj : j = i.val
    · subst j
      simp [i.property, Ne.symm (Fin.castSucc_ne_last i.val)]
    · simp [hj]
  have hs := sum_congr (s₁ := univ) (s₂ := univ) rfl (fun j _ => he j)
  simpa only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte] using hs

private theorem invMonomial_option {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (∑ q : Option ({i : _ // (f).val i = i}), invMonomial (extendInv f q)) =
      (invMonomial f).derivative + C (r + 1) * X * invMonomial f := by
  classical
  rw [Fintype.sum_option]
  have hnone : invMonomial (extendInv f none) = C (r + 1) * X * invMonomial f := by
    simp only [invMonomial, invWeight_none, fixedCount_none, C_mul, pow_succ]
    ring
  have hsome : ∀ i : {i : _ // (f).val i = i}, invMonomial (extendInv f (some i)) =
      C (invWeight f) * X ^ ((Fintype.card {x : _ // (f).val x = x}) - 1) := by
    intro i
    have h := fixedCount_some f i
    have he : (Fintype.card {x : _ // (extendInv f (some i)).val x = x}) = (Fintype.card {x : _ // (f).val x = x}) - 1 := by omega
    simp [invMonomial, invWeight_some, he]
  rw [hnone]
  simp_rw [hsome]
  simp only [sum_const, nsmul_eq_mul, invMonomial, derivative_C_mul_X_pow]
  change C (r + 1) * X * (C (invWeight f) * X ^ (Fintype.card {x : _ // (f).val x = x})) +
    ((Fintype.card {x : _ // (f).val x = x}) : Polynomial ℕ) * (C (invWeight f) * X ^ ((Fintype.card {x : _ // (f).val x = x}) - 1)) = _
  simp only [← C_eq_natCast, C_mul]
  ring

private theorem invSum_succ (r : ℕ) :
    invSum (r + 1) = (invSum r).derivative + C (r + 1) * X * invSum r := by
  classical
  unfold invSum
  rw [← Equiv.sum_comp (invSuccEquiv r)]
  rw [Fintype.sum_sigma]
  change (∑ f : {f : Fin r → Fin r // Function.Involutive f}, ∑ q : Option ({i : _ // (f).val i = i}), invMonomial (extendInv f q)) = _
  simp_rw [invMonomial_option]
  rw [sum_add_distrib, ← derivative_sum, ← mul_sum]

private theorem invSum_zero : invSum 0 = 1 := by
  classical
  letI : Unique ({f : Fin 0 → Fin 0 // Function.Involutive f}) :=
    { default := ⟨id, fun x => rfl⟩
      uniq := fun f => Subtype.ext (funext (fun x => Fin.elim0 x)) }
  simp [invSum, invMonomial, invWeight]

private theorem invSum_walkPoly (r : ℕ) : invSum r = walkPoly r := by
  induction r with
  | zero => exact invSum_zero
  | succ r ih => rw [invSum_succ, ih, walkPoly]

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian

namespace D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck
open scoped BigOperators
open Finset Polynomial
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation (P)
attribute [local instance] Classical.propDecidable

private theorem fixedCount_zero_iff {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (f).val x = x}) = 0 ↔ ∀ i, f.val i ≠ i := by
  constructor
  · intro hz i hi
    have hp : 0 < (Fintype.card {x : _ // (f).val x = x}) := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    omega
  · intro hn
    letI : IsEmpty ({i : _ // (f).val i = i}) := ⟨fun i => hn i.val i.property⟩
    exact Fintype.card_eq_zero

private noncomputable def pairingInvEquiv (n : ℕ) :
    P n ≃ {f : {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f} // (Fintype.card {x : _ // (f).val x = x}) = 0} where
  toFun p := ⟨⟨(p).val, (p).property.1⟩, (fixedCount_zero_iff _).mpr p.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, (fixedCount_zero_iff _).mp f.property⟩
  left_inv p := rfl
  right_inv f := rfl

private theorem invMonomial_eval_zero {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (invMonomial f).eval 0 = if (Fintype.card {x : _ // (f).val x = x}) = 0 then invWeight f else 0 := by
  by_cases h : (Fintype.card {x : _ // (f).val x = x}) = 0 <;> simp [invMonomial, h]

private theorem polyConst_pairings (n : ℕ) :
    (walkPoly (2 * n)).eval 0 = ∑ p : P n, invWeight (⟨(p).val, (p).property.1⟩) := by
  classical
  rw [← invSum_walkPoly, invSum, eval_finsetSum]
  simp only [invMonomial_eval_zero]
  rw [← sum_filter]
  rw [sum_subtype (p := fun f : {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f} => (Fintype.card {x : _ // (f).val x = x}) = 0) _ (by simp)]
  exact (Equiv.sum_comp (pairingInvEquiv n) (fun f => invWeight f.val)).symm

private theorem matching_weight (n : ℕ)
    (M : {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching}) :
    (∏ i : Fin (2 * n), ∏ j : Fin (2 * n),
      if i < j ∧ M.val.Adj i j then i.val + 1 else 1) =
        invWeight (⟨(matchingToPairing n M).val, (matchingToPairing n M).property.1⟩) := by
  classical
  unfold invWeight matchingToPairing
  apply prod_congr rfl
  intro i hi
  rw [matching_weight_row n M.val M.property i]
  congr 1
  apply propext
  exact lt_iff_le_and_ne.trans (and_iff_left (matchingMate_ne M.val M.property i).symm)

private theorem hafnian_pairings (n : ℕ) :
    hafnian n = ∑ p : P n, invWeight (⟨(p).val, (p).property.1⟩) := by
  classical
  unfold hafnian
  rw [← sum_filter]
  rw [sum_subtype (p := fun M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph => M.IsPerfectMatching) _ (by simp)]
  calc
    _ = ∑ M : {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching},
        invWeight (⟨(matchingEquiv n M).val, (matchingEquiv n M).property.1⟩) := by
      apply sum_congr rfl
      intro M hM
      exact matching_weight n M
    _ = _ := Equiv.sum_comp (matchingEquiv n) (fun p => invWeight (⟨(p).val, (p).property.1⟩))

private theorem polyConst_hafnian (n : ℕ) : (walkPoly (2 * n)).eval 0 = hafnian n :=
  (polyConst_pairings n).trans (hafnian_pairings n).symm

private theorem source_eq_hafnian (a : ℕ → ℕ) (ha : IsSourceSequence a) (n : ℕ) :
    a n = hafnian n :=
  (congrFun (source_unique ha poly_is_source) n).trans (polyConst_hafnian n)

theorem result : claim := by
  refine ⟨⟨fun n => (walkPoly (2 * n)).eval 0, poly_is_source⟩, ?_⟩
  intro a ha n
  exact ⟨source_eq_hafnian a ha n, source_eq_dyck a ha n⟩

end D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
