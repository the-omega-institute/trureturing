/- GID: D5/S3/HomologicalAlgebra/CocycleDiagonalCubic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized elementary two-group three-cocycles have cubic diagonals. -/

import D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
import D5.S3.HomologicalAlgebra.SplitQuadraticSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Coordinate expansions of the cyclic diagonal of a normalized three-cocycle. -/

open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.CocycleDiagonalCubic

open CocycleDiagonalQuadratic (quadratic_sum_pairs)
open ElementaryTwoThirdCohomologyDetection (product_diagonal_quadratic)

private theorem quadratic_support_expansion {V M ι : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup M]
    (q : V → M) (hq0 : q 0 = 0) (htwo : ∀ x, q x + q x = 0)
    (hpolar : ∀ x y z, QuadraticMap.polar q (x + y) z =
      QuadraticMap.polar q x z + QuadraticMap.polar q y z)
    (v : ι → V) :
    ∃ c : Finset ι → M, c ∅ = 0 ∧ (∀ t, 2 < t.card → c t = 0) ∧
      ∀ s, q (∑ i ∈ s, v i) = ∑ t ∈ s.powerset, c t := by
  classical
  let L (t : Finset ι) := q (∑ i ∈ t, v i)
  let Q (t : Finset ι) := L t - ∑ i ∈ t, q (v i)
  refine ⟨fun t => (if t.card = 1 then L t else 0) +
    (if t.card = 2 then Q t else 0), by simp, ?_, ?_⟩
  · intro t ht
    have h1 : t.card ≠ 1 := by omega
    have h2 : t.card ≠ 2 := by omega
    simp [h1, h2]
  intro s
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.powersetCard_eq_filter, ← Finset.powersetCard_eq_filter]
  rw [quadratic_sum_pairs q hq0 htwo hpolar s v]
  have hL : (∑ t ∈ s.powersetCard 1, L t) = ∑ i ∈ s, q (v i) := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    simp [L]
  rw [hL]
  congr 1
  apply Finset.sum_nbij Sym2.toFinset
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_powersetCard.mpr
      ⟨fun _ hx => Finset.mem_sym2_iff.mp hp.1 _ (Sym2.mem_toFinset.mp hx),
        Sym2.card_toFinset_of_not_isDiag p hp.2⟩
  · intro p hp p' hp' h
    induction p using Sym2.ind with
    | h a b =>
      induction p' using Sym2.ind with
      | h x y =>
        have hab : a ≠ b := by simpa using (Finset.mem_filter.mp hp).2
        have hxy : x ≠ y := by simpa using (Finset.mem_filter.mp hp').2
        simp only [Sym2.toFinset_mk_eq] at h
        have ha : a = x ∨ a = y := by
          have hm : a ∈ ({a, b} : Finset ι) := by simp
          rw [h] at hm
          simpa using hm
        have hb : b = x ∨ b = y := by
          have hm : b ∈ ({a, b} : Finset ι) := by simp
          rw [h] at hm
          simpa using hm
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · intro t ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
    have hsub := (Finset.mem_powersetCard.mp ht).1
    exact ⟨s(a, b), Finset.mem_filter.mpr
      ⟨Finset.mk_mem_sym2_iff.mpr ⟨hsub (by simp), hsub (by simp)⟩, by simpa⟩,
      Sym2.toFinset_mk_eq⟩
  · intro p hp
    induction p using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by simpa using (Finset.mem_filter.mp hp).2
      simp [Q, L, hab, Sym2.toFinset_mk_eq, QuadraticMap.polar, sub_sub]

abbrev Bit := ZMod 2

private def indicator {ι : Type*} [DecidableEq ι] (s : Finset ι) : ι → Bit :=
  ∑ i ∈ s, Pi.single i 1

private theorem extend_support {ι M : Type*} [DecidableEq ι] [AddCommGroup M]
    {a : ι} {s : Finset ι} (ha : a ∉ s) (d : Finset ι → M)
    (c b : Finset ι → M) (h : M)
    (hc : ∀ t ⊆ s, d t = ∑ u ∈ t.powerset, c u)
    (hb : ∀ t, a ∉ t → d (insert a t) = d t + h + ∑ u ∈ t.powerset, b u) :
    ∀ t ⊆ insert a s, d t =
      ∑ u ∈ t.powerset, if a ∈ u then
        (if u.erase a = ∅ then h else 0) + b (u.erase a) else c u := by
  intro t ht
  by_cases hat : a ∈ t
  · let v := t.erase a
    have hav : a ∉ v := Finset.notMem_erase a t
    have hv : v ⊆ s := by
      intro i hi
      have hm := Finset.mem_erase.mp hi
      exact (Finset.mem_insert.mp (ht hm.2)).resolve_left hm.1
    have htv : insert a v = t := Finset.insert_erase hat
    rw [← htv, hb v hav, hc v hv, Finset.sum_powerset_insert hav]
    have hnot (u : Finset ι) (hu : u ∈ v.powerset) : a ∉ u :=
      Finset.notMem_of_mem_powerset_of_notMem hu hav
    have hfirst : (∑ u ∈ v.powerset, if a ∈ u then
        (if u.erase a = ∅ then h else 0) + b (u.erase a) else c u) =
        ∑ u ∈ v.powerset, c u :=
      Finset.sum_congr rfl (fun u hu => ite_eq_right (hnot u hu))
    have hsecond : (∑ u ∈ v.powerset, if a ∈ insert a u then
        (if (insert a u).erase a = ∅ then h else 0) + b ((insert a u).erase a)
        else c (insert a u)) =
        ∑ u ∈ v.powerset, ((if u = ∅ then h else 0) + b u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [Finset.erase_insert (hnot u hu)]
    rw [hfirst, hsecond, Finset.sum_add_distrib]
    have hs₀ : (∑ u ∈ v.powerset, if u = ∅ then h else 0) = h := by simp
    rw [hs₀, add_assoc]
  · have hts : t ⊆ s := by
      intro i hi
      exact (Finset.mem_insert.mp (ht hi)).resolve_left (fun e => hat (e ▸ hi))
    rw [hc _ hts]
    apply Finset.sum_congr rfl
    intro u hu
    rw [ite_eq_right (Finset.notMem_of_mem_powerset_of_notMem hu hat)]

/-- The diagonal of a normalized 3-cocycle on an elementary two-group is
represented on coordinate supports by a square-free polynomial of degree
at most three. -/
theorem diagonal_cubic {ι M : Type} [Finite ι] [DecidableEq ι] [AddCommGroup M]
    (half : ∀ m : M, ∃ k, k + k = m)
    (f : Multiplicative (ι → Bit) → Multiplicative (ι → Bit) →
      Multiplicative (ι → Bit) → M)
    (hc : ∀ a b c d, f b c d - f (a * b) c d + f a (b * c) d -
      f a b (c * d) + f a b c = 0)
    (hn : ∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0) :
    ∃ c : Finset ι → M, c ∅ = 0 ∧ (∀ t, 3 < t.card → c t = 0) ∧
      ∀ s, let x := Multiplicative.ofAdd (indicator s)
        f x x x = ∑ t ∈ s.powerset, c t := by
  classical
  letI := Fintype.ofFinite ι
  let G := Multiplicative (ι → Bit)
  let C := Multiplicative Bit
  let T : C := Multiplicative.ofAdd (1 : Bit)
  let d (s : Finset ι) := let x : G := Multiplicative.ofAdd (indicator s); f x x x
  have hzero : d ∅ = 0 := by simp [d, indicator, (hn 1 1).1]
  have build (s : Finset ι) : ∃ c : Finset ι → M, c ∅ = 0 ∧
      (∀ t, 3 < t.card → c t = 0) ∧
      ∀ t ⊆ s, d t = ∑ u ∈ t.powerset, c u := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, rfl, fun _ _ => rfl, ?_⟩
      intro t ht
      rw [Finset.subset_empty.mp ht, hzero]
      simp
    | @insert a s ha ih =>
      obtain ⟨c, hc₀, hc₃, hc_eval⟩ := ih
      let j : G × C →* G :=
        { toFun := fun x => Multiplicative.ofAdd (x.1.toAdd + Pi.single a x.2.toAdd)
          map_one' := by simp
          map_mul' := by
            intro x y
            apply Multiplicative.toAdd.injective
            change (x.1.toAdd + y.1.toAdd) + Pi.single a (x.2.toAdd + y.2.toAdd) =
              (x.1.toAdd + Pi.single a x.2.toAdd) + (y.1.toAdd + Pi.single a y.2.toAdd)
            rw [Pi.single_add]
            abel }
      let F (x y z : G × C) := f (j x) (j y) (j z)
      have hG (u : G) : u * u = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        exact CharTwo.add_self_eq_zero _
      obtain ⟨q, hq₀, hq₂, hqPolar, hq⟩ := product_diagonal_quadratic hG half F
        (fun x y z v => by simpa [F, map_mul] using hc (j x) (j y) (j z) (j v))
        (fun x y => by simpa [F, map_one] using hn (j x) (j y))
      let q' (x : ι → Bit) := q (Additive.ofMul (Multiplicative.ofAdd x))
      have hpolar (x y z : ι → Bit) : QuadraticMap.polar q' (x + y) z =
          QuadraticMap.polar q' x z + QuadraticMap.polar q' y z :=
        hqPolar (Additive.ofMul (Multiplicative.ofAdd x))
          (Additive.ofMul (Multiplicative.ofAdd y)) (Additive.ofMul (Multiplicative.ofAdd z))
      obtain ⟨b, _, hb₂, hb⟩ := quadratic_support_expansion q' hq₀
        (fun x => hq₂ (Additive.ofMul (Multiplicative.ofAdd x))) hpolar
        (fun i => Pi.single i 1)
      let c' (t : Finset ι) := if a ∈ t then
        (if t.erase a = ∅ then d {a} else 0) + b (t.erase a)
        else c t
      have hshift : ∀ t, a ∉ t → d (insert a t) = d t + d {a} +
          ∑ u ∈ t.powerset, b u := by
        intro t ht
        let x : G := Multiplicative.ofAdd (indicator t)
        have hJ₁ : j (x, 1) = x := by simp [j]
        have hJT : j (1, T) = Multiplicative.ofAdd (indicator {a}) := by
          simp [j, T, indicator]
        have hJx : j (x, T) = Multiplicative.ofAdd (indicator (insert a t)) := by
          simp [j, x, T, indicator, Finset.sum_insert ht, add_comm]
        have hq_eval := hq x
        change f (j (x, T)) (j (x, T)) (j (x, T)) =
          f (j (x, 1)) (j (x, 1)) (j (x, 1)) +
          f (j (1, T)) (j (1, T)) (j (1, T)) + q (Additive.ofMul x) at hq_eval
        rw [hJx, hJ₁, hJT] at hq_eval
        have hqsum : q (Additive.ofMul x) = ∑ u ∈ t.powerset, b u := hb t
        rw [hqsum] at hq_eval
        exact hq_eval
      refine ⟨c', by simp [c', hc₀], ?_, extend_support ha d c b (d {a}) hc_eval hshift⟩
      intro t ht
      by_cases hat : a ∈ t
      · have herase := Finset.card_erase_add_one hat
        have hn₀ : t.erase a ≠ ∅ := by
          intro he
          rw [he, Finset.card_empty] at herase
          omega
        simp [c', hat, hn₀, hb₂ _ (by omega : 2 < (t.erase a).card)]
      · simp [c', hat, hc₃ _ ht]
  obtain ⟨c, hc₀, hc₃, hc_eval⟩ := build Finset.univ
  exact ⟨c, hc₀, hc₃, fun s => hc_eval s (Finset.subset_univ _)⟩

/-- When the two-torsion is identified with `ZMod 2`, the cubic diagonal
has coefficients in that field. -/
theorem diagonal_bit_cubic {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (half : ∀ m : M, ∃ k, k + k = m)
    (σ : Bit →+ M) (hinj : Function.Injective σ)
    (htwo : ∀ m : M, m + m = 0 → ∃ e, σ e = m)
    (f : Multiplicative (ι → Bit) → Multiplicative (ι → Bit) →
      Multiplicative (ι → Bit) → M)
    (hc : ∀ a b c d, f b c d - f (a * b) c d + f a (b * c) d -
      f a b (c * d) + f a b c = 0)
    (hn : ∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0) :
    ∃ c : Finset ι → Bit, c ∅ = 0 ∧ (∀ t, 3 < t.card → c t = 0) ∧
      ∀ s, let x := Multiplicative.ofAdd (indicator s)
        f x x x = σ (∑ t ∈ s.powerset, c t) := by
  classical
  obtain ⟨d, hd₀, hd₃, hd⟩ := diagonal_cubic half f hc hn
  have hdiag (x : Multiplicative (ι → Bit)) : f x x x + f x x x = 0 := by
    have hx : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      exact CharTwo.add_self_eq_zero (x.toAdd i)
    have h := hc x x x x
    simpa only [hx, (hn x x).1, (hn x x).2.1, (hn x x).2.2, sub_zero, add_zero] using h
  have hd₂ (s : Finset ι) : d s + d s = 0 := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      have h := hdiag (Multiplicative.ofAdd (indicator s))
      rw [hd s, ← Finset.sum_add_distrib, Finset.sum_eq_single s] at h
      · exact h
      · intro t ht hne
        exact ih t (lt_of_le_of_ne (Finset.mem_powerset.mp ht) hne)
      · exact fun hnot => (hnot (Finset.mem_powerset_self s)).elim
  choose c hσ using fun t => htwo (d t) (hd₂ t)
  refine ⟨c, hinj (by rw [hσ, hd₀, map_zero]), ?_, ?_⟩
  · intro t ht
    exact hinj (by rw [hσ, hd₃ t ht, map_zero])
  · intro s
    change f _ _ _ = _
    rw [hd s, map_sum]
    exact Finset.sum_congr rfl (fun t _ => (hσ t).symm)

private theorem indicator_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) :
    indicator s i = (if i ∈ s then 1 else 0 : Bit) := by
  simp [indicator, Finset.sum_apply, Pi.single_apply, eq_comm]

/-- If a normalized three-cocycle diagonal vanishes on the zero cone of
the split quadratic form, it is that form times an affine character. -/
theorem diagonal_factor_on_split_zero_cone {ι M : Type} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [AddCommGroup M] (half : ∀ m : M, ∃ k, k + k = m)
    (σ : Bit →+ M) (hinj : Function.Injective σ)
    (htwo : ∀ m : M, m + m = 0 → ∃ e, σ e = m)
    (f : Multiplicative ((ι × Bool) → Bit) → Multiplicative ((ι × Bool) → Bit) →
      Multiplicative ((ι × Bool) → Bit) → M)
    (hc : ∀ a b c d, f b c d - f (a * b) c d + f a (b * c) d -
      f a b (c * d) + f a b c = 0)
    (hn : ∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0)
    (hsing : ∀ x : (ι × Bool) → Bit, (∑ i, x (i, false) * x (i, true)) = 0 →
      let a := Multiplicative.ofAdd x
      f a a a = 0) :
    ∃ e : Bit, ∃ ℓ : ((ι × Bool) → Bit) →+ Bit, ∀ x : (ι × Bool) → Bit,
      let a := Multiplicative.ofAdd x
      f a a a = σ ((∑ i, x (i, false) * x (i, true)) * (e + ℓ x)) := by
  classical
  obtain ⟨c, _, hc₃, hpoly⟩ := diagonal_bit_cubic half σ hinj htwo f hc hn
  obtain ⟨e, B, C, hfactor⟩ := SplitQuadraticSupport.factor_support_sum c hc₃ (by
    intro s hs
    have h := hsing (indicator s) (by simpa only [indicator_apply] using hs)
    dsimp only at h
    rw [hpoly s] at h
    exact hinj (by simpa only [map_zero] using h))
  let ℓ : ((ι × Bool) → Bit) →+ Bit :=
    { toFun := fun x => SplitQuadraticCubic.form B (fun i => x (i, false)) +
        SplitQuadraticCubic.form C (fun i => x (i, true))
      map_zero' := by simp [SplitQuadraticCubic.form]
      map_add' := by
        intro x y
        simp only [SplitQuadraticCubic.form, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        abel }
  refine ⟨e, ℓ, fun x => ?_⟩
  let s := Finset.univ.filter (fun p => x p = 1)
  have hs : indicator s = x := by
    funext p
    rw [indicator_apply]
    have hbit : ∀ b : Bit, b = 0 ∨ b = 1 := by decide +kernel
    rcases hbit (x p) with hx | hx <;> simp [s, hx]
  have h := hpoly s
  rw [hs, hfactor s] at h
  simpa [ℓ, SplitQuadraticCubic.quadratic, ← indicator_apply, hs, add_assoc] using h

end D5.S3.HomologicalAlgebra.CocycleDiagonalCubic
