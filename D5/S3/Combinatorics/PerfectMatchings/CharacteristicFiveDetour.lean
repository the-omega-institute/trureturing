/- GID: D5/S3/Combinatorics/PerfectMatchings/CharacteristicFiveDetour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/CharacteristicFiveDetour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Three cuts reconstruct a relative path through every nonzero column. -/

import D5.S1.Words.Sequenceability.RowOrbitLift
import D5.S3.Combinatorics.PerfectMatchings.WeightedReattachment

/-! Three cuts join the two row-lift cycles and the two endpoints into an exact relative path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicFiveDetour

open Equiv
open D5.S3.Combinatorics.PerfectMatchings
open FiniteEndpointPairing FiniteReturnTowers WeightedReattachment
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Swapping outgoing attachments joins two disjoint cycles, including singleton
cycles, without requiring the ambient permutation to have only those cycles. -/
theorem merge_cycles {X : Type*} [Finite X] [DecidableEq X] (f : Perm X)
    (A B : Set X) (hA : f.IsCycleOn A) (hB : f.IsCycleOn B)
    (hd : Disjoint A B) (a b : X) (ha : a ∈ A) (hb : b ∈ B) :
    (f * swap a b).IsCycleOn (A ∪ B) := by
  let S : Set X := {a, b}
  let : DecidablePred (· ∈ S) := fun _ => Classical.propDecidable _
  let aa : S := ⟨a, by simp [S]⟩
  let bb : S := ⟨b, by simp [S]⟩
  let J : Perm S := swap aa bb
  let g := f * J.ofSubtype
  have hJ : J.ofSubtype = swap a b := Perm.ofSubtype_swap_eq aa bb
  have hfirst (x : S) : FirstVisit f S x (orbitPeriod f x) := by
    have hp := orbit_period_spec f (x : X)
    refine ⟨hp.1.1, ?_, ?_⟩
    · rw [hp.1.2]; exact x.property
    · intro k hk hkn hmem
      have hself : (f ^ k) (x : X) ≠ x := by
        intro he
        have := hp.2 ⟨hk, he⟩
        omega
      rcases x.property with hxa | hxb
      · have hxa : (x : X) = a := hxa
        rcases hmem with hka | hkb
        · exact hself (hka.trans hxa.symm)
        · exact Set.disjoint_left.mp hd ((hA.1.perm_pow k).1 (hxa.symm ▸ ha)) (hkb.symm ▸ hb)
      · have hxb : (x : X) = b := hxb
        rcases hmem with hka | hkb
        · exact Set.disjoint_left.mp hd (hka.symm ▸ ha) ((hB.1.perm_pow k).1 (hxb.symm ▸ hb))
        · exact hself (hkb.trans hxb.symm)
  have hjump (x : S) : ∃ n : ℕ, FirstVisit g S x n ∧ (g ^ n) x = J x := by
    refine ⟨orbitPeriod f (J x), ?_⟩
    obtain ⟨hv, he⟩ := first_visit_reattach f S J x _ (hfirst (J x))
    exact ⟨hv, he.trans (orbit_period_spec f (J x)).1.2⟩
  have hmarks : g.SameCycle a b := by
    exact (same_cycle_of_first_visit g S J hjump aa bb).mpr
      ⟨1, by simp [J, aa, bb]⟩
  have hreach (z : X) (hz : z ∈ A ∪ B) : g.SameCycle a z := by
    have horig : ∃ x : S, f.SameCycle x z := by
      rcases hz with hz | hz
      · exact ⟨aa, hA.2 ha hz⟩
      · exact ⟨bb, hB.2 hb hz⟩
    have hnew : ∃ x : S, g.SameCycle x z := by
      by_contra hn
      have hn' : ∀ x : S, ¬ g.SameCycle x z := by simpa using hn
      have hf := (untouched_reattach_iff f S J z).mp hn'
      obtain ⟨x, hx⟩ := horig
      exact hf x hx
    obtain ⟨x, hx⟩ := hnew
    rcases x.property with hxa | hxb
    · exact (show (x : X) = a from hxa) ▸ hx
    · exact hmarks.trans ((show (x : X) = b from hxb) ▸ hx)
  rw [← hJ]
  refine ⟨?_, fun x hx y hy => (hreach x hx).symm.trans (hreach y hy)⟩
  simpa only [hJ, Perm.coe_mul] using (hA.1.union hB.1 f.injective.injOn).comp
    (Equiv.bijOn_swap (Or.inl ha) (Or.inr hb))


open RowOrbitLift

private abbrev Carrier (K : Type*) := (Fin 4 × K) ⊕ Fin 2

private def basePerm {K : Type*} [Field K] (r : Kˣ) (c : K) : Perm (Carrier K) :=
  (lift r c).sumCongr 1

private def surgery {K : Type*} [Field K] (r : Kˣ) (u : K) : Perm (Carrier K) :=
  swap (.inl (1, 3 * u)) (.inr 0) * swap (.inl (1, 3 * u)) (.inr 1) *
    swap (.inl (2, 4 * u)) (.inl (3, 2 * u)) * basePerm r (4 * u)

private def coordinate {K : Type*} [Field K] (u : K) : Carrier K → ZMod 5 × K
  | .inl v => vertex v
  | .inr i => if i = 0 then (0, 0) else (0, u)

private theorem surgery_cycle {K : Type*} [Field K] [Finite K] [CharP K 5]
    (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hc : ∀ v w : Fin 4 × K, (lift r (4 * u)).SameCycle v w ↔
      (initialRow v = 4 * u ↔ initialRow w = 4 * u)) :
    (surgery r u).IsCycleOn Set.univ := by
  let P := basePerm r (4 * u)
  let h₁ : Carrier K := .inl (1, 3 * u)
  let h₂ : Carrier K := .inl (2, 4 * u)
  let h₃ : Carrier K := .inl (3, 2 * u)
  let s : Carrier K := .inr 0
  let t : Carrier K := .inr 1
  let A : Set (Carrier K) := {z | P.SameCycle h₂ z}
  let B : Set (Carrier K) := {z | P.SameCycle h₃ z}
  let U : Set (Carrier K) := Set.range Sum.inl
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hi₂ : initialRow (2, 4 * u) = 4 * u := by simp [initialRow]
  have hi₃ : initialRow (3, 2 * u) ≠ 4 * u := by
    intro heq
    have h : -(2 * u) = 4 * u := by simpa [initialRow] using heq
    apply hu
    linear_combination -h - u * h5
  have hp (n : ℕ) (v : Fin 4 × K) :
      (P ^ n) (.inl v) = .inl ((lift r (4 * u) ^ n) v) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Perm.mul_apply, ih]; rfl
  have hcP (v w : Fin 4 × K) :
      P.SameCycle (.inl v) (.inl w) ↔ (initialRow v = 4 * u ↔ initialRow w = 4 * u) := by
    rw [← hc]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [hp] at hn
      exact ⟨(n : ℤ), by simpa only [zpow_natCast] using Sum.inl.inj hn⟩
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      exact ⟨(n : ℤ), by rw [zpow_natCast, hp, hn]⟩
  have hA : P.IsCycleOn A :=
    ⟨P.bijOn (fun z => Perm.sameCycle_apply_right), fun x hx y hy => hx.symm.trans hy⟩
  have hB : P.IsCycleOn B :=
    ⟨P.bijOn (fun z => Perm.sameCycle_apply_right), fun x hx y hy => hx.symm.trans hy⟩
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    have hh := hzA.trans hzB.symm
    have he := (hcP (2, 4 * u) (3, 2 * u)).mp hh
    exact hi₃ (he.mp hi₂)
  have hU : A ∪ B = U := by
    ext z
    cases z with
    | inl v =>
      simp only [Set.mem_union, Set.mem_ofPred_eq, A, B]
      rw [hcP, hcP]
      simp only [hi₂, hi₃, true_iff, false_iff]
      simpa only [U, Set.mem_range, Sum.inl.injEq, exists_eq, iff_true] using
        em (initialRow v = 4 * u)
    | inr i =>
      have hfix : P (.inr i) = .inr i := rfl
      have hna : ¬ P.SameCycle h₂ (.inr i) := fun h => by
        simpa only [h₂, reduceCtorEq] using h.eq_of_right hfix
      have hnb : ¬ P.SameCycle h₃ (.inr i) := fun h => by
        simpa only [h₃, reduceCtorEq] using h.eq_of_right hfix
      simp [A, B, hna, hnb, U]
  have hR : (swap h₂ h₃ * P).IsCycleOn U := by
    have hm := merge_cycles P A B hA hB hd (P⁻¹ h₂) (P⁻¹ h₃)
      ((Perm.SameCycle.refl P h₂).symm_apply_right)
      ((Perm.SameCycle.refl P h₃).symm_apply_right)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hU] using hm
  let R := swap h₂ h₃ * P
  have hRt : R t = t := by simp [R, t, P, basePerm, h₂, h₃, swap_apply_def]
  have hRs : R s = s := by simp [R, s, P, basePerm, h₂, h₃, swap_apply_def]
  have h₁U : h₁ ∈ U := ⟨(1, 3 * u), rfl⟩
  have hT : (swap h₁ t * R).IsCycleOn (U ∪ {t}) := by
    have hm := merge_cycles R U {t} hR (Perm.isCycleOn_singleton.mpr hRt)
      (by simp [U, t, Set.disjoint_singleton_right]) (R⁻¹ h₁) t
      (hR.inv.1.1 h₁U) (by simp)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hRt] using hm
  let T := swap h₁ t * R
  have hTs : T s = s := by simp [T, Perm.mul_apply, hRs, h₁, s, t, swap_apply_def]
  have hQ : (swap h₁ s * T).IsCycleOn ((U ∪ {t}) ∪ {s}) := by
    have hm := merge_cycles T (U ∪ {t}) {s} hT (Perm.isCycleOn_singleton.mpr hTs)
      (by simp [U, s, t, Set.disjoint_singleton_right]) (T⁻¹ h₁) s
      (hT.inv.1.1 (Or.inl h₁U)) (by simp)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hTs] using hm
  have hfull : (U ∪ {t}) ∪ {s} = Set.univ := by
    ext z
    cases z with
    | inl v => simp [U]
    | inr i => fin_cases i <;> simp [U, s, t]
  simpa only [hfull, T, R, P, surgery, h₁, h₂, h₃, s, t, mul_assoc] using hQ


private theorem coordinate_injective {K : Type*} [Field K] (u : K) (hu : u ≠ 0)
    (hv : Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0}) :
    Function.Injective (coordinate u) := by
  rintro (v | i) (w | j) he
  · exact congrArg Sum.inl (hv.2.1 trivial trivial he)
  · have hn := hv.1 (Set.mem_univ v)
    have hz := congrArg Prod.fst he
    fin_cases j <;> exact (hn hz).elim
  · have hn := hv.1 (Set.mem_univ w)
    have hz := congrArg Prod.fst he
    fin_cases i <;> exact (hn hz.symm).elim
  · fin_cases i <;> fin_cases j <;> simp_all [coordinate]

/-- Puncturing at the terminal point removes precisely the artificial closing label. -/
private theorem surgery_labels {K : Type*} [Field K] [CharP K 5]
    (r : Kˣ) (u : K)
    (he : Set.BijOn (edgeLabel r (4 * u)) Set.univ {v | v.1 ≠ 0}) :
    Set.BijOn (fun z => coordinate u (surgery r u z) - coordinate u z)
      {z | z ≠ Sum.inr 1} ({v | v.1 ≠ 0} ∪ {(0, u)}) := by
  let s : Carrier K := .inr 0
  let t : Carrier K := .inr 1
  let a : Carrier K := .inl (0, 2 * u)
  let b : Carrier K := .inl (1, u)
  let c : Carrier K := .inl (2, 3 * u)
  let ψ : Perm (Carrier K) := swap s c * swap s a * swap s b
  let L : Carrier K → ZMod 5 × K := fun z =>
    match z with
    | .inl v => edgeLabel r (4 * u) v
    | .inr _ => (0, u)
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hneg₂ : -(2 * u) = 3 * u := by linear_combination -u * h5
  have hneg₁ : -u = 4 * u := by linear_combination -u * h5
  have hneg₃ : -(3 * u) = 2 * u := by linear_combination -u * h5
  have hP₁ : basePerm r (4 * u) a = .inl (1, 3 * u) := by
    simp [basePerm, a, lift, hneg₂]
  have hP₂ : basePerm r (4 * u) b = .inl (2, 4 * u) := by
    simp [basePerm, b, lift, hneg₁]
  have hP₃ : basePerm r (4 * u) c = .inl (3, 2 * u) := by
    simp [basePerm, c, lift, hneg₃]
  have hLt : ψ t = t := by simp [ψ, s, t, a, b, c, swap_apply_def]
  have hψ : Set.BijOn ψ {z | z ≠ t} {z | z ≠ t} :=
    ψ.bijOn (fun z => by
      change ψ z ≠ t ↔ z ≠ t
      conv_lhs => rw [← hLt]
      exact not_congr ψ.injective.eq_iff)
  have hL : Set.BijOn L {z | z ≠ t} ({v | v.1 ≠ 0} ∪ {(0, u)}) := by
    constructor
    · rintro (v | i) hz
      · exact Or.inl (he.1 trivial)
      · exact Or.inr rfl
    constructor
    · rintro (v | i) hz (w | j) hw h
      · exact congrArg Sum.inl (he.2.1 trivial trivial h)
      · have hh := congrArg Prod.fst h
        exact ((he.1 (Set.mem_univ v)) hh).elim
      · have hh := congrArg Prod.fst h
        exact ((he.1 (Set.mem_univ w)) hh.symm).elim
      · have hi : i = 0 := by fin_cases i <;> simp_all [t]
        have hj : j = 0 := by fin_cases j <;> simp_all [t]
        simp [hi, hj]
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨v, _, hv⟩ := he.2.2 hy
        exact ⟨.inl v, by simp [t], hv⟩
      · exact ⟨s, by simp [s, t], hy.symm⟩
  have hdiff (z : Carrier K) (hz : z ≠ t) :
      coordinate u (surgery r u z) - coordinate u z = L (ψ z) := by
    by_cases hza : z = a
    · subst z
      apply Prod.ext
      · norm_num [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₂, hneg₃]
      · simp [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₂, hneg₃]
        ring
    by_cases hzb : z = b
    · subst z
      apply Prod.ext
      · norm_num [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₁]
      · simp [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₁, hneg₂]
        ring
    by_cases hzc : z = c
    · subst z
      apply Prod.ext
      · norm_num [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₃]
      · simp [surgery, coordinate, ψ, L, s, a, b, c,
          basePerm, vertex, column, edgeLabel, lift, swap_apply_def, hneg₃]
        ring
    by_cases hzs : z = s
    · subst z
      apply Prod.ext
      · norm_num [surgery, coordinate, ψ, L, s, a, b, c, basePerm,
          vertex, column, edgeLabel, lift, swap_apply_def]
      · simp [surgery, coordinate, ψ, L, s, a, b, c, basePerm,
          vertex, column, edgeLabel, lift, swap_apply_def]
        linear_combination u * h5
    have hp₁ : basePerm r (4 * u) z ≠ .inl (1, 3 * u) := by
      rw [← hP₁]; exact (basePerm r (4 * u)).injective.ne hza
    have hp₂ : basePerm r (4 * u) z ≠ .inl (2, 4 * u) := by
      rw [← hP₂]; exact (basePerm r (4 * u)).injective.ne hzb
    have hp₃ : basePerm r (4 * u) z ≠ .inl (3, 2 * u) := by
      rw [← hP₃]; exact (basePerm r (4 * u)).injective.ne hzc
    have hps : basePerm r (4 * u) z ≠ s := by
      have hs : basePerm r (4 * u) s = s := rfl
      rw [← hs]; exact (basePerm r (4 * u)).injective.ne hzs
    have hpt : basePerm r (4 * u) z ≠ t := by
      have ht : basePerm r (4 * u) t = t := rfl
      rw [← ht]; exact (basePerm r (4 * u)).injective.ne hz
    have hψz : ψ z = z := by
      simp [ψ, Perm.mul_apply, swap_apply_of_ne_of_ne, hza, hzb, hzc, hzs]
    rw [hψz]
    have hQz : surgery r u z = basePerm r (4 * u) z := by
      simp only [surgery, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hp₂ hp₃,
        swap_apply_of_ne_of_ne hp₁ hpt, swap_apply_of_ne_of_ne hp₁ hps]
    rw [hQz]
    cases z with
    | inl v => rfl
    | inr i => fin_cases i <;> simp_all [s, t]
  exact (hL.comp hψ).congr (fun z hz => (hdiff z hz).symm)


/-- Every finite field of characteristic five admits an exact coefficient-one
relative path with both endpoint prefixes retained. -/
theorem exists_characteristic_five_relative_path (K : Type*)
    [Field K] [Finite K] [CharP K 5] (u : K) (hu : u ≠ 0) :
    let M := 4 * Nat.card K + 1
    ∃ v : ℕ → ZMod 5 × K,
      v 0 = (0, 0) ∧ v M = (0, u) ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
        ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u) := by
  let := Fintype.ofFinite K
  let M := 4 * Nat.card K + 1
  obtain ⟨r, _, hc, he, hv, _⟩ := exists_characteristic_five_lift K (4 * u)
  let Q := surgery r u
  let s : Carrier K := .inr 0
  let t : Carrier K := .inr 1
  let orbit : ℕ → Carrier K := fun n => (Q ^ n) s
  let v : ℕ → ZMod 5 × K := coordinate u ∘ orbit
  have hcard : Fintype.card (Carrier K) = M + 1 := by
    simp only [Carrier, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      M, Nat.card_eq_fintype_card]
  have hcyc : Q.IsCycleOn (Finset.univ : Finset (Carrier K)) := by
    simpa only [Finset.coe_univ] using surgery_cycle r u hu hc
  have hbound : Set.InjOn orbit (Set.Iio (M + 1)) := by
    simpa only [Finset.card_univ, hcard] using hcyc.injOn_pow_apply (Finset.mem_univ s)
  have horbit (z : Carrier K) : ∃ n < M + 1, orbit n = z := by
    simpa only [Finset.card_univ, hcard] using
      hcyc.exists_pow_eq (Finset.mem_univ s) (Finset.mem_univ z)
  have hzero : orbit 0 = s := rfl
  have hQt : Q t = s := by
    simp [Q, surgery, t, s, basePerm, Perm.mul_apply, swap_apply_def]
  have hlast : orbit M = t := by
    apply Q.injective
    rw [hQt]
    have hclose := hcyc.pow_card_apply (Finset.mem_univ s)
    simpa only [Finset.card_univ, hcard, pow_succ', Perm.mul_apply] using hclose
  have hcoord := coordinate_injective u hu hv
  have hvinj : Function.Injective (fun n : Fin (M + 1) => v n.val) := by
    intro i j hij
    exact Fin.ext (hbound i.isLt j.isLt (hcoord hij))
  have hv0 : v 0 = (0, 0) := rfl
  have hvM : v M = (0, u) := by simp [v, Function.comp_apply, hlast, coordinate, t]
  have hinside : Set.BijOn orbit (Set.Ioo 0 M) (Set.range Sum.inl) := by
    constructor
    · intro n hn
      rcases hn with ⟨hn0, hnM⟩
      cases heq : orbit n with
      | inl z => exact ⟨z, rfl⟩
      | inr i =>
        fin_cases i
        · have hh : n = 0 := hbound (x₁ := n) (x₂ := 0)
            (by change n < M + 1; omega) (by change 0 < M + 1; omega)
            (heq.trans hzero.symm)
          omega
        · have hh : n = M := hbound (x₁ := n) (x₂ := M)
            (by change n < M + 1; omega) (by change M < M + 1; omega)
            (heq.trans hlast.symm)
          omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi.2)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj.2) hij
    · rintro z ⟨w, rfl⟩
      obtain ⟨n, hn, heq⟩ := horbit (.inl w)
      have hn0 : n ≠ 0 := by intro h; subst n; cases heq
      have hnM : n ≠ M := by
        intro h
        subst n
        rw [hlast] at heq
        simp only [t, reduceCtorEq] at heq
      exact ⟨n, ⟨by omega, by omega⟩, heq⟩
  have hcoords : Set.BijOn (coordinate u) (Set.range Sum.inl) {z | z.1 ≠ 0} := by
    constructor
    · rintro z ⟨w, rfl⟩
      exact hv.1 trivial
    constructor
    · exact hcoord.injOn
    · intro z hz
      obtain ⟨w, _, hw⟩ := hv.2.2 hz
      exact ⟨.inl w, ⟨w, rfl⟩, hw⟩
  have hpunctured : Set.BijOn orbit (Set.Iio M) {z | z ≠ t} := by
    constructor
    · intro n hn heq
      change n < M at hn
      have hh : n = M := hbound (x₁ := n) (x₂ := M)
            (by change n < M + 1; omega) (by change M < M + 1; omega)
            (heq.trans hlast.symm)
      omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hnM : n ≠ M := by intro h; subst n; exact hz (heq.symm.trans hlast)
      exact ⟨n, (show n < M from by omega), heq⟩
  have hlabels := (surgery_labels r u he).comp hpunctured
  have hstep (n : ℕ) : orbit (n + 1) = Q (orbit n) := by
    simp only [orbit, pow_succ', Perm.mul_apply]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, (v (i + 1) - v i)) = v n - v 0 :=
    Finset.sum_range_sub v n
  refine ⟨v, hv0, hvM, hvinj, hcoords.comp hinside, ?_, ?_, ?_, ?_⟩
  · exact hlabels.congr (fun n _ => by
      change coordinate u (Q (orbit n)) - coordinate u (orbit n) =
        coordinate u (orbit (n + 1)) - coordinate u (orbit n)
      rw [hstep])
  · intro i j heq
    apply hvinj
    simpa only [hsum, sub_left_inj] using heq
  · intro a b hab hb hzero
    have hinterval : (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) = v b - v a := by
      rw [Finset.sum_Ico_eq_sub _ hab.le, hsum, hsum]
      abel
    have heq : v b = v a := sub_eq_zero.mp (hinterval.symm.trans hzero)
    have hij := hvinj (a₁ := ⟨b, by omega⟩) (a₂ := ⟨a, by omega⟩) heq
    have heqb : b = a := congrArg Fin.val hij
    omega
  · rw [hsum, hv0, hvM]
    simp

#print axioms exists_characteristic_five_relative_path

end

end D5.S1.Words.Sequenceability.CharacteristicFiveDetour
