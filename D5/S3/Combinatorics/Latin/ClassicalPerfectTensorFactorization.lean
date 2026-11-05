/- GID: D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect classical six-leg circuits have perfect two-wire factors. -/

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-! Index-one orthogonal arrays for the classical factorization question of Pozsgay and Wanless,
arXiv:2308.07042v3, with the wire convention of equation (4.2). -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization

universe u v

/-- Every selection of distinct columns contains every tuple exactly once. With
`|R| = |X|^s`, this is the source's strength-`s` orthogonal array with `D^s` rows. -/
def IsIndexOneOA {r : Type v} {x : Type u} [Fintype r] [Fintype x] {c : ℕ}
    (rows : r → Fin c → x) (s : ℕ) : Prop :=
  ∀ cols : Fin s → Fin c, Function.Injective cols →
    Function.Bijective (fun t => fun i => rows t (cols i))

/-- The four columns are the two input and two output symbols of the gate. -/
def gateGraph {x : Type u} (f : x × x → x × x) (t : x × x) : Fin 4 → x :=
  ![t.1, t.2, (f t).1, (f t).2]

/-- Apply the gates on wires `(1,2)`, `(1,3)`, and `(2,3)`, respectively. -/
def circuit {x : Type u} (a b c : x × x → x × x) (t : x × x × x) : x × x × x :=
  let ab := a (t.1, t.2.1)
  let pc := b (ab.1, t.2.2)
  let qr := c (ab.2, pc.2)
  (pc.1, qr.1, qr.2)

/-- The graph has columns `(x,y,z,p,q,r)` in the source's wire convention. -/
def circuitGraph {x : Type u} (a b c : x × x → x × x)
    (t : x × x × x) : Fin 6 → x :=
  ![t.1, t.2.1, t.2.2, (circuit a b c t).1,
    (circuit a b c t).2.1, (circuit a b c t).2.2]

/-- The nonlinear six-leg classical factorization assertion. -/
def claim : Prop :=
  ∀ (x : Type u) [Fintype x] (a b c : x × x → x × x),
    IsIndexOneOA (circuitGraph a b c) 3 →
      IsIndexOneOA (gateGraph a) 2 ∧ IsIndexOneOA (gateGraph b) 2 ∧
        IsIndexOneOA (gateGraph c) 2

private def IsLatin {x : Type u} (f : x × x → x) : Prop :=
  (∀ t, Function.Bijective (fun s => f (s, t))) ∧
    (∀ s, Function.Bijective (fun t => f (s, t)))

private theorem oa_injective {r : Type v} {x : Type u} [Fintype r] [Fintype x]
    {n : ℕ} {rows : r → Fin n → x} (h : IsIndexOneOA rows 3)
    (i j k : Fin n) (hc : Function.Injective ![i, j, k]) {s t : r}
    (hi : rows s i = rows t i) (hj : rows s j = rows t j)
    (hk : rows s k = rows t k) : s = t := by
  apply (h ![i, j, k] hc).1
  funext l
  fin_cases l
  · exact hi
  · exact hj
  · exact hk

private theorem oa_surjective {r : Type v} {x : Type u} [Fintype r] [Fintype x]
    {n : ℕ} {rows : r → Fin n → x} (h : IsIndexOneOA rows 3)
    (i j k : Fin n) (hc : Function.Injective ![i, j, k]) (a b c : x) :
    ∃ t, rows t i = a ∧ rows t j = b ∧ rows t k = c := by
  obtain ⟨t, ht⟩ := (h ![i, j, k] hc).2 ![a, b, c]
  dsimp only at ht
  exact ⟨t, congrFun ht 0, congrFun ht 1, congrFun ht 2⟩

private theorem gate_perfect {x : Type u} [Fintype x] (f : x × x → x × x)
    (hf : Function.Bijective f) (h₁ : IsLatin (fun t => (f t).1))
    (h₂ : IsLatin (fun t => (f t).2)) : IsIndexOneOA (gateGraph f) 2 := by
  have hp (i j : Fin 4) (hne : i ≠ j) (s t : x × x)
      (hi : gateGraph f s i = gateGraph f t i)
      (hj : gateGraph f s j = gateGraph f t j) : s = t := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change s.1 = t.1 at hi
      change s.2 = t.2 at hj
      exact Prod.ext hi hj
    · change s.1 = t.1 at hi
      change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hj
      apply Prod.ext hi
      apply (h₁.2 t.1).1
      simpa only [hi] using hj
    · change s.1 = t.1 at hi
      change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hj
      apply Prod.ext hi
      apply (h₂.2 t.1).1
      simpa only [hi] using hj
    · change s.2 = t.2 at hi
      change s.1 = t.1 at hj
      exact Prod.ext hj hi
    · exact (hne rfl).elim
    · change s.2 = t.2 at hi
      change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hj
      apply Prod.ext _ hi
      apply (h₁.1 t.2).1
      simpa only [hi] using hj
    · change s.2 = t.2 at hi
      change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hj
      apply Prod.ext _ hi
      apply (h₂.1 t.2).1
      simpa only [hi] using hj
    · change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hi
      change s.1 = t.1 at hj
      apply Prod.ext hj
      apply (h₁.2 t.1).1
      simpa only [hj] using hi
    · change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hi
      change s.2 = t.2 at hj
      apply Prod.ext _ hj
      apply (h₁.1 t.2).1
      simpa only [hj] using hi
    · exact (hne rfl).elim
    · change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hi
      change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hj
      exact hf.1 (Prod.ext hi hj)
    · change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hi
      change s.1 = t.1 at hj
      apply Prod.ext hj
      apply (h₂.2 t.1).1
      simpa only [hj] using hi
    · change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hi
      change s.2 = t.2 at hj
      apply Prod.ext _ hj
      apply (h₂.1 t.2).1
      simpa only [hj] using hi
    · change (f (s.1, s.2)).2 = (f (t.1, t.2)).2 at hi
      change (f (s.1, s.2)).1 = (f (t.1, t.2)).1 at hj
      exact hf.1 (Prod.ext hj hi)
    · exact (hne rfl).elim
  intro cols hc
  apply (Function.Bijective.of_comp_iff' (finTwoArrowEquiv x).bijective _).mp
  apply Function.Injective.bijective_of_finite
  intro s t he
  apply hp (cols 0) (cols 1) (fun h => (by decide : (0 : Fin 2) ≠ 1) (hc h)) s t
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

private theorem factors_bijective {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3) :
    Function.Bijective a ∧ Function.Bijective b ∧ Function.Bijective c := by
  let la : x × x × x → x × x × x :=
    fun t => ((a (t.1, t.2.1)).1, (a (t.1, t.2.1)).2, t.2.2)
  let lb : x × x × x → x × x × x :=
    fun t => ((b (t.1, t.2.2)).1, t.2.1, (b (t.1, t.2.2)).2)
  let lc : x × x × x → x × x × x :=
    fun t => (t.1, (c t.2).1, (c t.2).2)
  have hu : Function.Bijective (lc ∘ lb ∘ la) := by
    apply Function.Injective.bijective_of_finite
    intro s t he
    exact oa_injective h 3 4 5 (by decide)
      (congrArg Prod.fst he) (congrArg (fun t => t.2.1) he)
      (congrArg (fun t => t.2.2) he)
  have hla : Function.Bijective la :=
    (show Function.Injective ((lc ∘ lb) ∘ la) from hu.1).of_comp.bijective_of_finite
  have hclb : Function.Bijective (lc ∘ lb) :=
    (Function.Bijective.of_comp_iff _ hla).mp hu
  have hlb : Function.Bijective lb := hclb.1.of_comp.bijective_of_finite
  have hlc : Function.Bijective lc := (Function.Bijective.of_comp_iff _ hlb).mp hclb
  refine ⟨?_, ?_, ?_⟩
  · exact ((Prod.map_bijective (f := a) (g := (id : x → x))).mp
      ((Equiv.prodAssoc x x x).symm.bijective.comp
        (hla.comp (Equiv.prodAssoc x x x).bijective))).1
  · exact ((Prod.map_bijective (f := b) (g := (id : x → x))).mp
      ((Equiv.prodAssoc x x x).symm.bijective.comp
        ((Equiv.prodCongr (Equiv.refl x) (Equiv.prodComm x x)).bijective.comp
          (hlb.comp ((Equiv.prodCongr (Equiv.refl x) (Equiv.prodComm x x)).bijective.comp
            (Equiv.prodAssoc x x x).bijective))))).1
  · exact ((Prod.map_bijective (f := (id : x → x)) (g := c)).mp hlc).2

private theorem first_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) :
    IsLatin (fun t => (a t).1) ∧ IsLatin (fun t => (b t).1) := by
  classical
  let d : x := Classical.choice inferInstance
  have hal : ∀ y, Function.Bijective (fun x => (a (x, y)).1) := by
    intro y
    apply Function.Injective.bijective_of_finite
    intro s t he
    dsimp only at he
    have hp : (circuit a b c (s, y, d)).1 = (circuit a b c (t, y, d)).1 := by
      change (b ((a (s, y)).1, d)).1 = (b ((a (t, y)).1, d)).1
      rw [he]
    exact congrArg Prod.fst (oa_injective h 1 2 3 (by decide)
        (s := (s, y, d)) (t := (t, y, d)) rfl rfl hp)
  have har : ∀ x, Function.Bijective (fun y => (a (x, y)).1) := by
    intro w
    apply Function.Injective.bijective_of_finite
    intro s t he
    dsimp only at he
    have hp : (circuit a b c (w, s, d)).1 = (circuit a b c (w, t, d)).1 := by
      change (b ((a (w, s)).1, d)).1 = (b ((a (w, t)).1, d)).1
      rw [he]
    exact congrArg (fun v : x × x × x => v.2.1)
      (oa_injective h 0 2 3 (by decide)
        (s := (w, s, d)) (t := (w, t, d)) rfl rfl hp)
  refine ⟨⟨hal, har⟩, ?_, ?_⟩
  · intro z
    apply Function.Injective.bijective_of_finite
    intro s t he
    dsimp only at he
    obtain ⟨u, hu⟩ := (hal d).2 s
    dsimp only at hu
    obtain ⟨v, hv⟩ := (hal d).2 t
    dsimp only at hv
    have hp : (circuit a b c (u, d, z)).1 = (circuit a b c (v, d, z)).1 := by
      change (b ((a (u, d)).1, z)).1 = (b ((a (v, d)).1, z)).1
      rw [hu, hv, he]
    have huv := congrArg Prod.fst (oa_injective h 1 2 3 (by decide)
      (s := (u, d, z)) (t := (v, d, z)) rfl rfl hp)
    exact hu.symm.trans ((congrArg (fun w => (a (w, d)).1) huv).trans hv)
  · intro s
    apply Function.Injective.bijective_of_finite
    intro u v he
    dsimp only at he
    obtain ⟨t, ht⟩ := ha.2 (s, d)
    have ht₁ := congrArg Prod.fst ht
    have hp : (circuit a b c (t.1, t.2, u)).1 =
        (circuit a b c (t.1, t.2, v)).1 := by
      change (b ((a t).1, u)).1 = (b ((a t).1, v)).1
      dsimp only at *
      rw [ht₁, he]
    exact congrArg (fun w : x × x × x => w.2.2)
      (oa_injective h 0 1 3 (by decide)
        (s := (t.1, t.2, u)) (t := (t.1, t.2, v)) rfl rfl hp)

private theorem second_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) (hc : Function.Bijective c)
    (h₁ : IsLatin (fun t => (a t).1)) :
    IsLatin (fun t => (a t).2) ∧ IsLatin (fun t => (b t).2) := by
  classical
  let d : x := Classical.choice inferInstance
  have hal : ∀ y, Function.Bijective (fun x => (a (x, y)).2) := by
    intro y
    apply Function.Surjective.bijective_of_finite
    intro v
    obtain ⟨t, hy, hq, hr⟩ := oa_surjective h 1 4 5 (by decide)
      y (c (v, d)).1 (c (v, d)).2
    change t.2.1 = y at hy
    have he : c ((a (t.1, t.2.1)).2, (b ((a (t.1, t.2.1)).1, t.2.2)).2) =
        c (v, d) := Prod.ext hq hr
    have hv := congrArg Prod.fst (hc.1 he)
    exact ⟨t.1, by simpa only [hy] using hv⟩
  have har : ∀ x, Function.Bijective (fun y => (a (x, y)).2) := by
    intro x
    apply Function.Surjective.bijective_of_finite
    intro v
    obtain ⟨t, hx, hq, hr⟩ := oa_surjective h 0 4 5 (by decide)
      x (c (v, d)).1 (c (v, d)).2
    change t.1 = x at hx
    have he : c ((a (t.1, t.2.1)).2, (b ((a (t.1, t.2.1)).1, t.2.2)).2) =
        c (v, d) := Prod.ext hq hr
    have hv := congrArg Prod.fst (hc.1 he)
    exact ⟨t.2.1, by simpa only [hx] using hv⟩
  refine ⟨⟨hal, har⟩, ?_, ?_⟩
  · intro z
    apply Function.Injective.bijective_of_finite
    intro u v he
    dsimp only at he
    obtain ⟨s, hs⟩ := ha.2 (u, d)
    obtain ⟨t, ht⟩ := ha.2 (v, d)
    have hqr : c ((a s).2, (b ((a s).1, z)).2) =
        c ((a t).2, (b ((a t).1, z)).2) := by
      rw [hs, ht]
      change c (d, (b (u, z)).2) = c (d, (b (v, z)).2)
      rw [he]
    have hst : (s.1, s.2, z) = (t.1, t.2, z) :=
      oa_injective h 2 4 5 (by decide) rfl
        (congrArg Prod.fst hqr) (congrArg Prod.snd hqr)
    have heq : s = t := congrArg (fun w : x × x × x => (w.1, w.2.1)) hst
    exact (congrArg Prod.fst hs).symm.trans
      ((congrArg (fun w => (a w).1) heq).trans (congrArg Prod.fst ht))
  · intro v
    apply Function.Injective.bijective_of_finite
    intro s t he
    dsimp only at he
    obtain ⟨u, hu⟩ := (h₁.1 d).2 v
    dsimp only at hu
    have hqr : c ((a (u, d)).2, (b ((a (u, d)).1, s)).2) =
        c ((a (u, d)).2, (b ((a (u, d)).1, t)).2) := by
      rw [hu, he]
    exact congrArg (fun w : x × x × x => w.2.2)
      (oa_injective h 1 4 5 (by decide)
        (s := (u, d, s)) (t := (u, d, t)) rfl
        (congrArg Prod.fst hqr) (congrArg Prod.snd hqr))

private theorem last_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) (h₂ : IsLatin (fun t => (b t).2)) :
    IsLatin (fun t => (c t).1) ∧ IsLatin (fun t => (c t).2) := by
  classical
  let d : x := Classical.choice inferInstance
  constructor
  · constructor
    · intro v
      apply Function.Injective.bijective_of_finite
      intro s t he
      dsimp only at he
      obtain ⟨w, hw⟩ := (h₂.1 d).2 v
      dsimp only at hw
      obtain ⟨u, hu⟩ := ha.2 (w, s)
      obtain ⟨v, hv⟩ := ha.2 (w, t)
      have hp : (circuit a b c (u.1, u.2, d)).1 =
          (circuit a b c (v.1, v.2, d)).1 := by
        change (b ((a u).1, d)).1 = (b ((a v).1, d)).1
        rw [hu, hv]
      have ho : (circuit a b c (u.1, u.2, d)).2.1 =
          (circuit a b c (v.1, v.2, d)).2.1 := by
        change (c ((a u).2, (b ((a u).1, d)).2)).1 =
          (c ((a v).2, (b ((a v).1, d)).2)).1
        rw [hu, hv]
        change (c (s, (b (w, d)).2)).1 = (c (t, (b (w, d)).2)).1
        rw [hw, he]
      have huv : u = v := congrArg (fun w : x × x × x => (w.1, w.2.1))
        (oa_injective h 2 3 4 (by decide)
          (s := (u.1, u.2, d)) (t := (v.1, v.2, d)) rfl hp ho)
      exact (congrArg Prod.snd hu).symm.trans
        ((congrArg (fun w => (a w).2) huv).trans (congrArg Prod.snd hv))
    · intro v
      apply Function.Injective.bijective_of_finite
      intro s t he
      dsimp only at he
      obtain ⟨w, hw⟩ := ha.2 (d, v)
      obtain ⟨u, hu⟩ := (h₂.2 d).2 s
      dsimp only at hu
      obtain ⟨v, hv⟩ := (h₂.2 d).2 t
      dsimp only at hv
      have ho : (circuit a b c (w.1, w.2, u)).2.1 =
          (circuit a b c (w.1, w.2, v)).2.1 := by
        change (c ((a w).2, (b ((a w).1, u)).2)).1 =
          (c ((a w).2, (b ((a w).1, v)).2)).1
        rw [hw]
        change (c (_, (b (d, u)).2)).1 = (c (_, (b (d, v)).2)).1
        dsimp only at *
        rw [hu, hv, he]
      have huv := congrArg (fun w : x × x × x => w.2.2)
        (oa_injective h 0 1 4 (by decide)
          (s := (w.1, w.2, u)) (t := (w.1, w.2, v)) rfl rfl ho)
      exact hu.symm.trans ((congrArg (fun w => (b (d, w)).2) huv).trans hv)
  · constructor
    · intro v
      apply Function.Injective.bijective_of_finite
      intro s t he
      dsimp only at he
      obtain ⟨w, hw⟩ := (h₂.1 d).2 v
      dsimp only at hw
      obtain ⟨u, hu⟩ := ha.2 (w, s)
      obtain ⟨v, hv⟩ := ha.2 (w, t)
      have hp : (circuit a b c (u.1, u.2, d)).1 =
          (circuit a b c (v.1, v.2, d)).1 := by
        change (b ((a u).1, d)).1 = (b ((a v).1, d)).1
        rw [hu, hv]
      have ho : (circuit a b c (u.1, u.2, d)).2.2 =
          (circuit a b c (v.1, v.2, d)).2.2 := by
        change (c ((a u).2, (b ((a u).1, d)).2)).2 =
          (c ((a v).2, (b ((a v).1, d)).2)).2
        rw [hu, hv]
        change (c (s, (b (w, d)).2)).2 = (c (t, (b (w, d)).2)).2
        rw [hw, he]
      have huv : u = v := congrArg (fun w : x × x × x => (w.1, w.2.1))
        (oa_injective h 2 3 5 (by decide)
          (s := (u.1, u.2, d)) (t := (v.1, v.2, d)) rfl hp ho)
      exact (congrArg Prod.snd hu).symm.trans
        ((congrArg (fun w => (a w).2) huv).trans (congrArg Prod.snd hv))
    · intro v
      apply Function.Injective.bijective_of_finite
      intro s t he
      dsimp only at he
      obtain ⟨w, hw⟩ := ha.2 (d, v)
      obtain ⟨u, hu⟩ := (h₂.2 d).2 s
      dsimp only at hu
      obtain ⟨v, hv⟩ := (h₂.2 d).2 t
      dsimp only at hv
      have ho : (circuit a b c (w.1, w.2, u)).2.2 =
          (circuit a b c (w.1, w.2, v)).2.2 := by
        change (c ((a w).2, (b ((a w).1, u)).2)).2 =
          (c ((a w).2, (b ((a w).1, v)).2)).2
        rw [hw]
        change (c (_, (b (d, u)).2)).2 = (c (_, (b (d, v)).2)).2
        dsimp only at *
        rw [hu, hv, he]
      have huv := congrArg (fun w : x × x × x => w.2.2)
        (oa_injective h 0 1 5 (by decide)
          (s := (w.1, w.2, u)) (t := (w.1, w.2, v)) rfl rfl ho)
      exact hu.symm.trans ((congrArg (fun w => (b (d, w)).2) huv).trans hv)

/-- All factors of an index-one strength-three classical circuit are perfect. -/
theorem result : claim := by
  intro x _ a b c h
  by_cases hn : Nonempty x
  · have := hn
    obtain ⟨ha, hb, hc⟩ := factors_bijective a b c h
    obtain ⟨ha₁, hb₁⟩ := first_latin a b c h ha
    obtain ⟨ha₂, hb₂⟩ := second_latin a b c h ha hc ha₁
    obtain ⟨hc₁, hc₂⟩ := last_latin a b c h ha hb₂
    exact ⟨gate_perfect a ha ha₁ ha₂, gate_perfect b hb hb₁ hb₂,
      gate_perfect c hc hc₁ hc₂⟩
  · have : IsEmpty x := not_nonempty_iff.mp hn
    have he (f : x × x → x × x) : IsIndexOneOA (gateGraph f) 2 := by
      intro cols _
      exact Function.Bijective.of_isEmpty _
    exact ⟨he a, he b, he c⟩

end D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
