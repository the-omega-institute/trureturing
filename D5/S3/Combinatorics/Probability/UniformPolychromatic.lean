/- GID: D5/S3/Combinatorics/Probability/UniformPolychromatic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/UniformPolychromatic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Probability/FiniteLovaszLocalLemma]
   utility: none
   digest: A finite hypergraph has a coloring using every color on every edge under the symmetric local-lemma bound. -/

import D5.S3.Combinatorics.Probability.FiniteLovaszLocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Independent uniform vertex colors give each edge a missing-color probability at most
L * ((L - 1) / L)^s. Disjoint vertex supports supply independence from an arbitrary
conjunction of nonneighbor events. The finite symmetric local lemma then gives one
coloring in which every edge contains all colors. This is the classical
Erdos-Lovasz polychromatic argument with the exponential symmetric criterion.
-/

open scoped BigOperators
open Finset

namespace FinitePolychromatic
noncomputable section
attribute [local instance] Classical.propDecidable

private def avg {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card X

private def ind (p : Prop) : ℝ := if p then 1 else 0

private theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind, hp, hq]

private theorem avg_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [e.sum_comp, Fintype.card_congr e]

private theorem avg_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → ℝ) (g : Y → ℝ) :
    avg (fun z : X × Y => f z.1 * g z.2) = avg f * avg g := by
  dsimp [avg]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Fintype.card_prod, Nat.cast_mul]
  ring

private theorem avg_const {X : Type*} [Fintype X] [Nonempty X] (a : ℝ) :
    avg (fun _ : X => a) = a := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [avg, hc]

private theorem avg_mono {X : Type*} [Fintype X] {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

private theorem avg_sum {X C : Type*} [Fintype X] [Fintype C] (f : C → X → ℝ) :
    avg (fun x => ∑ c, f c x) = ∑ c, avg (f c) := by
  simp only [avg, Finset.sum_div]
  exact Finset.sum_comm

-- Uniform product averaging inherits the two-block product factorization.
private theorem split_avg {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V]
    (s : Finset V) (f : (s → C) → ℝ)
    (g : ({v : V // v ∉ s} → C) → ℝ) :
    avg (fun w : V → C => f (fun v => w v) * g (fun v => w v)) = avg f * avg g := by
  let e := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ s) (fun _ => C)
  exact (avg_equiv e (fun z => f z.1 * g z.2)).trans (avg_prod f g)

private theorem local_avg {V C : Type*} [Fintype V] [Fintype C] [Nonempty C] [DecidableEq V]
    (s : Finset V) (f : (s → C) → ℝ) :
    avg (fun w : V → C => f (fun v => w v)) = avg f := by
  have hh := split_avg s f (fun _ => (1 : ℝ))
  simpa only [mul_one, avg_const] using hh

-- Missing a prescribed color on a finite block.
private theorem missing_color_avg {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
    [DecidableEq V] (s : Finset V) (c : C) :
    avg (fun w : V → C => ind (∀ v ∈ s, w v ≠ c)) =
      ((Fintype.card C - 1 : ℝ) / Fintype.card C) ^ s.card := by
  classical
  have hind (w : s → C) : ind (∀ v : s, w v ≠ c) = ∏ v : s, ind (w v ≠ c) := by
    unfold ind
    by_cases hh : ∀ v : s, w v ≠ c
    · rw [if_pos hh]
      symm
      exact prod_eq_one (fun v _ => if_pos (hh v))
    · rw [if_neg hh]
      obtain ⟨v, hv⟩ := not_forall.mp hh
      exact (prod_eq_zero (mem_univ v) (if_neg hv)).symm
  have hsum : (∑ w : s → C, ind (∀ v : s, w v ≠ c)) =
      ((Fintype.card C : ℝ) - 1) ^ s.card := by
    simp only [hind]
    rw [← Fintype.prod_sum (fun (_ : s) (b : C) => ind (b ≠ c))]
    have hc : (∑ b : C, ind (b ≠ c)) = (Fintype.card C : ℝ) - 1 := by
      have hh (b : C) : ind (b ≠ c) = 1 - ind (b = c) := by
        by_cases heq : b = c <;> simp [ind, heq]
      simp_rw [hh]
      simp [Finset.sum_sub_distrib, ind]
    simp only [hc, Finset.prod_const, card_univ, Fintype.card_coe]
  have hlocal := local_avg s (fun w : s → C => ind (∀ v : s, w v ≠ c))
  have heq : (fun w : V → C => ind (∀ v ∈ s, w v ≠ c)) =
      (fun w : V → C => ind (∀ v : s, w v ≠ c)) := by
    funext w
    congr 1
    exact propext ⟨fun h v => h v v.property, fun h v hv => h ⟨v,hv⟩⟩
  rw [heq, hlocal]
  simp only [avg, hsum, Fintype.card_fun, Fintype.card_coe, Nat.cast_pow, div_pow]

-- Dependence only on one block means independence from the complementary block.
private theorem local_independence {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
    [DecidableEq V] (s : Finset V) (P Q : (V → C) → Prop)
    (hP : ∀ w w', (∀ v ∈ s, w v = w' v) → (P w ↔ P w'))
    (hQ : ∀ w w', (∀ v, v ∉ s → w v = w' v) → (Q w ↔ Q w')) :
    avg (fun w => ind (P w ∧ Q w)) =
      avg (fun w => ind (P w)) * avg (fun w => ind (Q w)) := by
  classical
  let c : C := Classical.choice inferInstance
  let extendS (w : s → C) : V → C := fun v => if h : v ∈ s then w ⟨v,h⟩ else c
  let extendT (w : {v : V // v ∉ s} → C) : V → C :=
    fun v => if h : v ∈ s then c else w ⟨v,h⟩
  let f := fun w : s → C => ind (P (extendS w))
  let g := fun w : {v : V // v ∉ s} → C => ind (Q (extendT w))
  have hp (w : V → C) : ind (P w) = f (fun v => w v) := by
    dsimp [f]
    rw [propext (hP w (extendS (fun v => w v)) (by intro v hv; simp [extendS,hv]))]
  have hq (w : V → C) : ind (Q w) = g (fun v => w v) := by
    dsimp [g]
    rw [propext (hQ w (extendT (fun v => w v)) (by intro v hv; simp [extendT,hv]))]
  simp_rw [ind_and, hp, hq]
  rw [split_avg]
  have hf := local_avg s f
  have hg := split_avg s (fun _ => (1 : ℝ)) g
  simp only [one_mul, avg_const] at hg
  rw [hf, hg]

open MathlibExt.Probability.Combinatorics.LovaszLocalLemma

private theorem ind_exists_le {C : Type*} [Fintype C] (P : C → Prop) :
    ind (∃ c, P c) ≤ ∑ c, ind (P c) := by
  classical
  by_cases h : ∃ c, P c
  · obtain ⟨c, hc⟩ := h
    have hh := Finset.single_le_sum (f := fun c => ind (P c))
      (fun c _ => by dsimp [ind]; split_ifs <;> norm_num) (mem_univ c)
    calc
      ind (∃ c, P c) = 1 := if_pos ⟨c,hc⟩
      _ = ind (P c) := (if_pos hc).symm
      _ ≤ _ := hh
  · have hh : ∀ c, ¬P c := by simpa using h
    simp [ind, hh]

private def bad {V C : Type*} (s : Finset V) (w : V → C) : Prop :=
  ∃ c : C, ∀ v ∈ s, w v ≠ c

private theorem bad_probability_bound {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
    [DecidableEq V] (s : Finset V) :
    avg (fun w : V → C => ind (bad s w)) ≤
      (Fintype.card C : ℝ) * (((Fintype.card C : ℝ)-1)/Fintype.card C)^s.card := by
  calc
    _ ≤ avg (fun w : V → C => ∑ c : C, ind (∀ v ∈ s, w v ≠ c)) :=
      avg_mono (fun w => ind_exists_le (fun c : C => ∀ v ∈ s, w v ≠ c))
    _ = ∑ c : C, avg (fun w : V → C => ind (∀ v ∈ s, w v ≠ c)) := avg_sum _
    _ = _ := by simp only [missing_color_avg, sum_const, card_univ, nsmul_eq_mul]

private theorem bad_local {V C : Type*} (s : Finset V) (w w' : V → C)
    (h : ∀ v ∈ s, w v = w' v) : bad s w ↔ bad s w' := by
  constructor <;> rintro ⟨c,hc⟩ <;> refine ⟨c,?_⟩
  · intro v hv; rw [← h v hv]; exact hc v hv
  · intro v hv; rw [h v hv]; exact hc v hv

private theorem uniform_event {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    (∑ x : X, if P x then (Fintype.card X : ℝ)⁻¹ else 0) = avg (fun x => ind (P x)) := by
  simp only [avg, sum_div]
  apply sum_congr rfl
  intro x hx
  by_cases hp : P x <;> simp [ind, hp]

private def intersectionGraph {V I : Type*} (E : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ¬Disjoint (E i) (E j)
  symm := ⟨by intro i j h; exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem finite_polychromatic_of_symmetric_LLL
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (E : I → Finset V) (L s D : Nat) (hL : 0 < L)
    (hsize : ∀ i, s ≤ (E i).card)
    (hdegree : ∀ i, ((univ : Finset I).filter fun j => j ≠ i ∧ ¬Disjoint (E i) (E j)).card ≤ D)
    (hLLL : Real.exp 1 * ((L : ℝ) * (((L : ℝ)-1)/L)^s) * ((D : ℝ)+1) ≤ 1) :
    ∃ color : V → Fin L, ∀ i c, ∃ v ∈ E i, color v = c := by
  classical
  let : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  let Ω := V → Fin L
  let pmf := fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹
  let A : I → Set Ω := fun i => {w | bad (E i) w}
  let G := intersectionGraph E
  let p : ℝ := (L : ℝ) * (((L : ℝ)-1)/L)^s
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hfrac : 0 ≤ ((L : ℝ)-1)/L := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hfracOne : ((L : ℝ)-1)/L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
    linarith
  have hpmf : ∑ w, pmf w = 1 := by
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [pmf, hc]
  have hdeg : G.maxDegree ≤ D := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro i
    have heq : G.neighborFinset i = univ.filter (fun j => j ≠ i ∧ ¬Disjoint (E i) (E j)) := by
      ext j
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
      change (i ≠ j ∧ ¬Disjoint (E i) (E j)) ↔ (j ∈ univ ∧ j ≠ i ∧ ¬Disjoint (E i) (E j))
      simp only [mem_univ, true_and, ne_comm]
    simpa only [SimpleGraph.degree, heq] using hdegree i
  have hbound (i : I) : (∑ w : Ω, if w ∈ A i then pmf w else 0) ≤ p := by
    change (∑ w : V → Fin L, if bad (E i) w then (Fintype.card Ω : ℝ)⁻¹ else 0) ≤ p
    rw [uniform_event]
    calc
      _ ≤ (L : ℝ) * (((L : ℝ)-1)/L)^(E i).card := by
        simpa only [Fintype.card_fin] using (bad_probability_bound (C := Fin L) (E i))
      _ ≤ p := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hfrac hfracOne (hsize i)) (Nat.cast_nonneg _)
  have hdep (i : I) (S : Finset I)
      (hS : ∀ j ∈ S, j ∉ Set.insert i (G.neighborSet i)) :
      (∑ w : Ω, if w ∈ A i ∧ ∀ j ∈ S, w ∈ A j then pmf w else 0) =
        (∑ w : Ω, if w ∈ A i then pmf w else 0) *
        (∑ w : Ω, if ∀ j ∈ S, w ∈ A j then pmf w else 0) := by
    change (∑ w : Ω, if bad (E i) w ∧ ∀ j ∈ S, bad (E j) w then (Fintype.card Ω : ℝ)⁻¹ else 0) =
      (∑ w : Ω, if bad (E i) w then (Fintype.card Ω : ℝ)⁻¹ else 0) *
      (∑ w : Ω, if ∀ j ∈ S, bad (E j) w then (Fintype.card Ω : ℝ)⁻¹ else 0)
    simp only [uniform_event]
    apply local_independence (E i) (fun w => bad (E i) w) (fun w => ∀ j ∈ S, bad (E j) w)
    · exact bad_local (E i)
    · intro w w' hw
      have hd (j : I) (hj : j ∈ S) : Disjoint (E i) (E j) := by
        have hn := hS j hj
        by_contra hdis
        have hne : j ≠ i := fun heq => hn (Or.inl heq)
        apply hn
        exact Or.inr ⟨Ne.symm hne,hdis⟩
      apply forall_congr'
      intro j
      apply imp_congr_right
      intro hj
      apply bad_local (E j)
      intro v hv
      exact hw v (fun hi => (Finset.disjoint_left.mp (hd j hj)) hi hv)
  have hpositive := lovasz_local_lemma_symmetric_finite pmf
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hpmf A G p D
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hfrac _)) hdeg hbound hdep hLLL
  have hex : ∃ w : Ω, ∀ i, w ∉ A i := by
    by_contra hn
    push Not at hn
    have hz : (∑ w : Ω, if ∀ i, w ∉ A i then pmf w else 0) = 0 := by
      apply sum_eq_zero
      intro w _
      obtain ⟨i,hi⟩ := hn w
      exact if_neg (fun h => h i hi)
    rw [hz] at hpositive
    exact (lt_irrefl 0) hpositive
  obtain ⟨w,hgood⟩ := hex
  refine ⟨w,?_⟩
  intro i c
  have hn : ¬bad (E i) w := hgood i
  by_contra h
  apply hn
  refine ⟨c,?_⟩
  simpa only [not_exists, not_and] using h

end
end FinitePolychromatic
