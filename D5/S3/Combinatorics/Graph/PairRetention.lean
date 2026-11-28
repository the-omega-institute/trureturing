/- GID: D5/S3/Combinatorics/Graph/PairRetention
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp extension along a retained pair, and recursive pair-clique layers. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

Sharp extension along a retained pair, and recursive pair-clique layers.
-/

open scoped BigOperators
namespace SimpleGraph.PairRetention
noncomputable section

variable {V E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

def defect (g : V → V → E) (a b c : V) : E := g a b + g b c - g a c

def residual (g : V → V → E) (q : V → E) (a b : V) : E :=
  g a b - (q b - q a)

lemma diagonal_zero (g : V → V → E) (hrev : ∀ a b, g b a = -g a b) (a : V) :
    g a a = 0 := by
  have h : (2 : ℝ) • g a a = 0 := by
    rw [two_smul, eq_neg_iff_add_eq_zero.mp (hrev a a)]
  calc
    g a a = (1/2 : ℝ) • ((2 : ℝ) • g a a) := by rw [smul_smul]; norm_num
    _ = 0 := by rw [h, smul_zero]

omit [NormedSpace ℝ E] in
lemma residual_reverse (g : V → V → E) (q : V → E)
    (hrev : ∀ a b, g b a = -g a b) (a b : V) :
    residual g q b a = -residual g q a b := by
  unfold residual
  rw [hrev a b]
  abel

omit [NormedSpace ℝ E] in
/-- A norm bound with a specified finite set of zero summands. -/
lemma norm_sum_erase_bound [DecidableEq V] (N : Finset V) (Z : Finset V)
    (hZ : Z ⊆ N) (f : V → E) (ε : ℝ)
    (hz : ∀ x ∈ Z, f x = 0) (hf : ∀ x ∈ N, x ∉ Z → ‖f x‖ ≤ ε) :
    ‖∑ x ∈ N, f x‖ ≤ ((N.card : ℝ) - Z.card) * ε := by
  have he : ∑ x ∈ N, f x = ∑ x ∈ N \ Z, f x := by
    symm
    apply Finset.sum_subset (Finset.sdiff_subset)
    intro x hx hnx
    exact hz x (by simpa [hx] using hnx)
  rw [he]
  calc
    _ ≤ ∑ x ∈ N \ Z, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ N \ Z, ε := Finset.sum_le_sum fun x hx =>
      hf x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hZ,
        Nat.cast_sub (Finset.card_le_card hZ)]

/-- The explicit correction to the midpoint extension. -/
def correction [DecidableEq V] (g : V → V → E) (N : Finset V)
    (a b : V) (t : ℝ) (v : V) : E :=
  t • ∑ j ∈ N, (defect g a j v + defect g b j v)

def pairPotential [DecidableEq V] (g : V → V → E) (N : Finset V)
    (a b : V) (qa qb : E) (t : ℝ) (v : V) : E :=
  (1/2 : ℝ) • (qa + qb + g a v + g b v) + correction g N a b t v

lemma correction_difference [DecidableEq V] (g : V → V → E) (N : Finset V)
    (a b u v : V) (t : ℝ) :
    correction g N a b t v - correction g N a b t u =
      (t * N.card) • (defect g a u v + defect g b u v) -
        (2*t) • ∑ j ∈ N, defect g j u v := by
  unfold correction
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  have he (j : V) :
      (defect g a j v + defect g b j v) - (defect g a j u + defect g b j u) =
      (defect g a u v + defect g b u v) - (2 : ℝ) • defect g j u v := by
    unfold defect
    module
  simp_rw [he]
  simp [Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, mul_comm]

lemma pair_internal_identity [DecidableEq V] (g : V → V → E) (N : Finset V)
    (a b u v : V) (qa qb : E) (t : ℝ) :
    g u v - (pairPotential g N a b qa qb t v - pairPotential g N a b qa qb t u) =
      (1/2 - t*N.card) • (defect g a u v + defect g b u v) +
        (2*t) • ∑ j ∈ N, defect g j u v := by
  unfold pairPotential
  rw [show ((1/2 : ℝ) • (qa + qb + g a v + g b v) + correction g N a b t v) -
      ((1/2 : ℝ) • (qa + qb + g a u + g b u) + correction g N a b t u) =
      (1/2 : ℝ) • (qa + qb + g a v + g b v) -
      (1/2 : ℝ) • (qa + qb + g a u + g b u) +
      (correction g N a b t v - correction g N a b t u) by abel]
  rw [correction_difference]
  unfold defect
  module

/-- Sharp pair extension: old endpoint potentials remain fixed. No completeness or
nontriviality assumption on the real normed target is needed for the upper bound. -/
theorem sharp_pair_extension [DecidableEq V] (g : V → V → E)
    (hrev : ∀ a b, g b a = -g a b)
    (N : Finset V) (a b : V) (_ha : a ∉ N) (_hb : b ∉ N) (_hab : a ≠ b)
    (qa qb : E) (C ε : ℝ) (hC : 0 ≤ C) (hC1 : C ≤ 1) (hε : 0 ≤ ε)
    (hold : ‖g a b - (qb - qa)‖ ≤ C * ε)
    (htri : ∀ x ∈ insert a (insert b N), ∀ y ∈ insert a (insert b N),
      ∀ z ∈ insert a (insert b N), x ≠ y → y ≠ z → x ≠ z →
      ‖defect g x y z‖ ≤ ε) :
    ∃ p : V → E,
      (∀ v ∈ N, ‖g a v - (p v - qa)‖ ≤ (1-(1-C)/(N.card+1)) * ε) ∧
      (∀ v ∈ N, ‖g b v - (p v - qb)‖ ≤ (1-(1-C)/(N.card+1)) * ε) ∧
      (∀ u ∈ N, ∀ v ∈ N, u ≠ v →
        ‖g u v - (p v - p u)‖ ≤ (1-(1-C)/(N.card+1)) * ε) := by
  let n : ℝ := N.card
  let t : ℝ := (1-C)/(4*(n+1))
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hn1 : 0 < n+1 := by linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have ht' : 0 ≤ 1/2-t*n := by
    have he : t * (4*(n+1)) = 1-C := div_mul_cancel₀ _ (by positivity)
    have : 0 ≤ t := ht
    nlinarith
  have hdiag := diagonal_zero g hrev
  have tri (x y z : V) (hx : x ∈ insert a (insert b N))
      (hy : y ∈ insert a (insert b N)) (hz : z ∈ insert a (insert b N)) :
      ‖defect g x y z‖ ≤ ε := by
    by_cases hxy : x = y
    · subst y; simpa [defect, hdiag] using hε
    by_cases hyz : y = z
    · subst z; simpa [defect, hdiag] using hε
    by_cases hxz : x = z
    · subst z; simpa [defect, hdiag, hrev x y] using hε
    exact htri x hx y hy z hz hxy hyz hxz
  let p := pairPotential g N a b qa qb t
  have corr (v : V) (hv : v ∈ N) : ‖correction g N a b t v‖ ≤
      t * (2*(n-1)*ε) := by
    have he : defect g a v v + defect g b v v = 0 := by simp [defect, hdiag]
    have hs := norm_sum_erase_bound N {v} (by simpa using hv)
      (fun j => defect g a j v + defect g b j v) (2*ε)
      (by simpa using he)
      (by
        intro j hj _
        exact (norm_add_le _ _).trans (by
          linarith [tri a j v (by simp) (by simp [hj]) (by simp [hv]),
            tri b j v (by simp) (by simp [hj]) (by simp [hv])]))
    rw [correction, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hs ht).trans_eq (by simp only [Finset.card_singleton, Nat.cast_one]; dsimp [n]; ring)
  have crossA (v : V) (hv : v ∈ N) : ‖g a v - (p v - qa)‖ ≤
      (1-(1-C)/(N.card+1)) * ε := by
    have he : g a v - ((1/2 : ℝ) • (qa+qb+g a v+g b v) - qa) =
        (1/2 : ℝ) • (defect g b a v - (g b a - (qa-qb))) := by
      unfold defect
      module
    have hr : ‖g b a - (qa-qb)‖ ≤ C*ε := by
      rw [hrev a b, show -g a b - (qa-qb) = -(g a b-(qb-qa)) by abel, norm_neg]
      exact hold
    have hm : ‖g a v - ((1/2 : ℝ) • (qa+qb+g a v+g b v) - qa)‖ ≤
        (1+C)/2*ε := by
      rw [he, norm_smul]
      norm_num
      have hh := (norm_sub_le _ _).trans (add_le_add
        (tri b a v (by simp) (by simp) (by simp [hv])) hr)
      linarith
    have he' : g a v - (p v-qa) =
        (g a v - ((1/2 : ℝ) • (qa+qb+g a v+g b v)-qa)) - correction g N a b t v := by
      dsimp [p, pairPotential]
      abel
    rw [he']
    calc
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hm (corr v hv))
      _ = _ := by dsimp [t, n]; field_simp; ring
  refine ⟨p, crossA, ?_, ?_⟩
  · intro v hv
    have he : g b v - ((1/2 : ℝ) • (qa+qb+g a v+g b v) - qb) =
        (1/2 : ℝ) • (defect g a b v - (g a b - (qb-qa))) := by
      unfold defect
      module
    have hm : ‖g b v - ((1/2 : ℝ) • (qa+qb+g a v+g b v) - qb)‖ ≤
        (1+C)/2*ε := by
      rw [he, norm_smul]
      norm_num
      have hh := (norm_sub_le _ _).trans (add_le_add
        (tri a b v (by simp) (by simp) (by simp [hv])) hold)
      linarith
    have he' : g b v - (p v-qb) =
        (g b v - ((1/2 : ℝ) • (qa+qb+g a v+g b v)-qb)) - correction g N a b t v := by
      dsimp [p, pairPotential]
      abel
    rw [he']
    calc
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hm (corr v hv))
      _ = _ := by dsimp [t, n]; field_simp; ring
  · intro u hu v hv huv
    have hs := norm_sum_erase_bound N {u,v} (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu,hv⟩)
      (fun j => defect g j u v) ε
      (by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [defect, hdiag]
        · have : j=v := Finset.mem_singleton.mp hj
          subst j
          simp [defect, hdiag, hrev u v])
      (by intro j hj _; exact tri j u v (by simp [hj]) (by simp [hu]) (by simp [hv]))
    have hpair : ‖defect g a u v + defect g b u v‖ ≤ 2*ε := by
      have ha' := tri a u v (by simp) (by simp [hu]) (by simp [hv])
      have hb' := tri b u v (by simp) (by simp [hu]) (by simp [hv])
      exact (norm_add_le _ _).trans (by linarith)
    change ‖g u v - (pairPotential g N a b qa qb t v -
      pairPotential g N a b qa qb t u)‖ ≤ _
    rw [pair_internal_identity]
    have h2t : 0 ≤ 2*t := by positivity
    calc
      _ ≤ ‖(1/2-t*N.card) • (defect g a u v + defect g b u v)‖ +
          ‖(2*t) • ∑ j ∈ N, defect g j u v‖ := norm_add_le _ _
      _ = (1/2-t*n) * ‖defect g a u v + defect g b u v‖ +
          (2*t) * ‖∑ j ∈ N, defect g j u v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ht', abs_of_nonneg h2t]
      _ ≤ (1/2-t*n)*(2*ε) + (2*t)*((n-2)*ε) := by
        apply add_le_add (mul_le_mul_of_nonneg_left hpair ht')
        apply mul_le_mul_of_nonneg_left _ h2t
        simpa [n, huv, Finset.card_pair] using hs
      _ = _ := by dsimp [t,n]; field_simp; ring

section Layers
variable {I : Type*}

/-- Simultaneously attach disjoint `n`-vertex cliques along specified old edges.
The index retains the parent-bag identity, so repeated pairs in different bags
produce distinct fresh vertices. -/
def attach (G : SimpleGraph V) (a b : I → V) (n : ℕ) :
    SimpleGraph (V ⊕ (I × Fin n)) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr v => u = a v.1 ∨ u = b v.1
    | .inr u, .inl v => v = a u.1 ∨ v = b u.1
    | .inr u, .inr v => u.1 = v.1 ∧ u.2 ≠ v.2
  symm := ⟨by
    intro u v h
    cases u <;> cases v
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by
    rintro (v | ⟨i,j⟩) h
    · exact G.loopless.irrefl v h
    · exact h.2 rfl⟩

def fresh [DecidableEq V] [DecidableEq I] (n : ℕ) (i : I) :
    Finset (V ⊕ (I × Fin n)) :=
  Finset.univ.map ⟨fun j => .inr (i,j), by intro j k h; cases h; rfl⟩

@[simp] lemma mem_fresh [DecidableEq V] [DecidableEq I] (n : ℕ) (i : I)
    (v : V ⊕ (I × Fin n)) : v ∈ fresh n i ↔ ∃ j, v = .inr (i,j) := by
  simp only [fresh, Finset.mem_map, Finset.mem_univ, true_and]
  change (∃ j, Sum.inr (i,j) = v) ↔ ∃ j, v = Sum.inr (i,j)
  simp only [eq_comm]

@[simp] lemma card_fresh [DecidableEq V] [DecidableEq I] (n : ℕ) (i : I) :
    (fresh (V := V) n i).card = n := by simp [fresh]

def childBag [DecidableEq V] [DecidableEq I] (a b : I → V) (n : ℕ) (i : I) :
    Finset (V ⊕ (I × Fin n)) := insert (.inl (a i)) (insert (.inl (b i)) (fresh n i))

lemma childBag_clique [DecidableEq V] [DecidableEq I] (G : SimpleGraph V)
    (a b : I → V) (n : ℕ) (h : ∀ i, G.Adj (a i) (b i)) (i : I) :
    (attach G a b n).IsClique (childBag a b n i : Set _) := by
  intro u hu v hv huv
  simp only [childBag, Finset.mem_coe, Finset.mem_insert, mem_fresh] at hu hv
  rcases hu with rfl | rfl | ⟨j,rfl⟩ <;>
    rcases hv with rfl | rfl | ⟨k,rfl⟩
  · exact (huv rfl).elim
  · exact h i
  · exact Or.inl rfl
  · exact (h i).symm
  · exact (huv rfl).elim
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact ⟨rfl, fun hh => huv (by change j=k at hh; rw [hh])⟩

/-- Every attachment in a layer shares exactly its own retained pair with the old
vertex set, and all layer extensions are performed without conflicting assignments. -/
theorem attach_upper (G : SimpleGraph V) (a b : I → V) (n : ℕ)
    (hedge : ∀ i, G.Adj (a i) (b i))
    (g : (V ⊕ (I × Fin n)) → (V ⊕ (I × Fin n)) → E)
    (hrev : ∀ u v, g v u = -g u v)
    (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (htri : ∀ u v w, (attach G a b n).Adj u v → (attach G a b n).Adj v w →
      (attach G a b n).Adj u w → ‖defect g u v w‖ ≤ ε)
    (q : V → E)
    (hq : ∀ u v, G.Adj u v → ‖g (.inl u) (.inl v) - (q v-q u)‖ ≤ C*ε) :
    ∃ p : (V ⊕ (I × Fin n)) → E,
      (∀ v, p (.inl v) = q v) ∧
      ∀ u v, (attach G a b n).Adj u v →
        ‖residual g p u v‖ ≤ (1-(1-C)/(n+1)) * ε := by
  classical
  have hlocal (i : I) := sharp_pair_extension g hrev (fresh n i)
    (.inl (a i)) (.inl (b i)) (by simp) (by simp)
    (fun h => (hedge i).ne (Sum.inl.inj h)) (q (a i)) (q (b i)) C ε hC hC1 hε
    (hq _ _ (hedge i))
    (by
      intro u hu v hv w hw huv hvw huw
      have hc := childBag_clique G a b n hedge i
      exact htri u v w (hc hu hv huv) (hc hv hw hvw) (hc hu hw huw))
  choose f hfA hfB hfN using hlocal
  let p : (V ⊕ (I × Fin n)) → E := Sum.elim q (fun v => f v.1 (.inr v))
  have pnew (i : I) (j : Fin n) : p (.inr (i,j)) = f i (.inr (i,j)) := rfl
  have hmono : C ≤ 1-(1-C)/(n+1 : ℝ) := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have he : (1-(1-C)/(n+1 : ℝ)-C)*(n+1) = (1-C)*n := by field_simp; ring
    nlinarith
  refine ⟨p, fun _ => rfl, ?_⟩
  intro u v huv
  cases u with
  | inl u =>
    cases v with
    | inl v => exact (hq u v huv).trans (mul_le_mul_of_nonneg_right hmono hε)
    | inr v =>
      rcases v with ⟨i,j⟩
      rcases huv with rfl | rfl
      · simpa [residual, pnew, p] using hfA i (.inr (i,j)) (by simp)
      · simpa [residual, pnew, p] using hfB i (.inr (i,j)) (by simp)
  | inr u =>
    cases v with
    | inl v =>
      rw [residual_reverse g p hrev, norm_neg]
      rcases u with ⟨i,j⟩
      rcases huv with rfl | rfl
      · simpa [residual, pnew, p] using hfA i (.inr (i,j)) (by simp)
      · simpa [residual, pnew, p] using hfB i (.inr (i,j)) (by simp)
    | inr v =>
      rcases u with ⟨i,j⟩
      rcases v with ⟨k,l⟩
      obtain ⟨rfl,hjl⟩ := huv
      simpa [residual, pnew, p] using hfN i (.inr (i,j)) (by simp)
        (.inr (i,l)) (by simp) (by simpa using hjl)

/-- All normalized triangle-defect cochains admit this residual coefficient. -/
def Upper (G : SimpleGraph V) (E : Type*) [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ℝ) : Prop :=
  ∀ (g : V → V → E), (∀ u v, g v u = -g u v) →
    (∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖defect g u v w‖ ≤ 1) →
    ∃ p : V → E, ∀ u v, G.Adj u v → ‖residual g p u v‖ ≤ C

theorem upper_attach (G : SimpleGraph V) (a b : I → V) (n : ℕ)
    (hedge : ∀ i, G.Adj (a i) (b i)) (C : ℝ) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (h : Upper G E C) : Upper (attach G a b n) E (1-(1-C)/(n+1)) := by
  intro g hrev htri
  obtain ⟨q,hq⟩ := h (fun u v => g (.inl u) (.inl v))
    (fun u v => hrev (.inl u) (.inl v))
    (fun u v w huv hvw huw => htri _ _ _ huv hvw huw)
  obtain ⟨p,_,hp⟩ := attach_upper G a b n hedge g hrev 1 C (by norm_num) hC hC1 htri q
    (by simpa [residual] using hq)
  exact ⟨p, by simpa using hp⟩
end Layers

/-- A finite graph with its current generation of clique bags. -/
structure System where
  Vertex : Type
  vertexFintype : Fintype Vertex
  Bag : Type
  bagFintype : Fintype Bag
  graph : SimpleGraph Vertex
  members : Bag → Finset Vertex
  clique : ∀ i, graph.IsClique (members i : Set Vertex)

attribute [instance] System.vertexFintype System.bagFintype

instance (S : System) : DecidableEq S.Vertex := Classical.decEq _

def System.PairIndex (S : System) :=
  {z : S.Bag × Finset S.Vertex // z.2 ⊆ S.members z.1 ∧ z.2.card = 2}

instance (S : System) : Fintype S.PairIndex := by
  classical
  unfold System.PairIndex
  infer_instance

def ends {W : Type*} [DecidableEq W] (s : Finset W) (hs : s.card = 2) : W × W :=
  let h := Finset.card_eq_two.mp hs
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

lemma ends_spec {W : Type*} [DecidableEq W] (s : Finset W) (hs : s.card = 2) :
    (ends s hs).1 ≠ (ends s hs).2 ∧ s = {(ends s hs).1, (ends s hs).2} :=
  Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp hs))

def System.left (S : System) (i : S.PairIndex) : S.Vertex := by
  classical
  exact (ends i.val.2 i.property.2).1

def System.right (S : System) (i : S.PairIndex) : S.Vertex := by
  classical
  exact (ends i.val.2 i.property.2).2

lemma System.endpoints (S : System) (i : S.PairIndex) :
    S.left i ≠ S.right i ∧ i.val.2 = {S.left i,S.right i} := by
  classical
  exact ends_spec i.val.2 i.property.2

lemma System.endpoints_adj (S : System) (i : S.PairIndex) :
    S.graph.Adj (S.left i) (S.right i) := by
  have he := S.endpoints i
  apply S.clique i.val.1 (i.property.1 ?_) (i.property.1 ?_) he.1
  · rw [he.2]; simp
  · rw [he.2]; simp

/-- One child for every unordered pair of every current bag. -/
def System.next (S : System) (n : ℕ) : System := by
  classical
  exact {
    Vertex := S.Vertex ⊕ (S.PairIndex × Fin n)
    vertexFintype := inferInstance
    Bag := S.PairIndex
    bagFintype := inferInstance
    graph := attach S.graph S.left S.right n
    members := childBag S.left S.right n
    clique := childBag_clique S.graph S.left S.right n S.endpoints_adj }

def System.iterate (S : System) (n : ℕ) : ℕ → System
  | 0 => S
  | D+1 => (S.iterate n D).next n

def rootSystem (m : ℕ) : System where
  Vertex := Fin m
  vertexFintype := inferInstance
  Bag := Unit
  bagFintype := inferInstance
  graph := ⊤
  members _ := Finset.univ
  clique _ := by intro u _ v _ huv; exact huv

/-- The actual bag-by-bag pair-retention family from the oracle statement. -/
def family (m n D : ℕ) : System := (rootSystem m).iterate n D

/-- Recursion over the actual clique family. The only input coefficient is for the
initial graph; the extension step and all subsequent generations are proved here. -/
theorem System.upper_iterate (S : System) (n D : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hC1 : C ≤ 1) (hbase : Upper S.graph E C) :
    Upper (S.iterate n D).graph E (1-(1-C)/(n+1 : ℝ)^D) := by
  induction D with
  | zero => simpa [System.iterate] using hbase
  | succ D ih =>
    have hn : 0 < (n+1 : ℝ) := by positivity
    have hp : 1 ≤ (n+1 : ℝ)^D := one_le_pow₀ (by
      have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    have hc0 : 0 ≤ 1-(1-C)/(n+1 : ℝ)^D := by
      have : (1-C)/(n+1 : ℝ)^D ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith
    have hc1 : 1-(1-C)/(n+1 : ℝ)^D ≤ 1 := by
      have : 0 ≤ (1-C)/(n+1 : ℝ)^D := div_nonneg (by linarith) (by positivity)
      linarith
    have h := upper_attach (S.iterate n D).graph (S.iterate n D).left
      (S.iterate n D).right n (S.iterate n D).endpoints_adj _ hc0 hc1 ih
    have he : 1-(1-(1-(1-C)/(n+1 : ℝ)^D))/(n+1 : ℝ) =
        1-(1-C)/(n+1 : ℝ)^(D+1) := by
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he] at h
    exact h

/-- The root bound is exactly the already frozen complete-graph upper ingredient;
this theorem propagates it through every actual pair-retention generation. -/
theorem family_upper_from_complete (m n D : ℕ)
    (hm : 2 ≤ m) (hroot : Upper (⊤ : SimpleGraph (Fin m)) E (1-2/(m : ℝ))) :
    Upper (family m n D).graph E (1-2/((m : ℝ)*(n+1 : ℝ)^D)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hc : 0 ≤ 1-2/(m : ℝ) := by
    have : 2/(m : ℝ) ≤ 1 := (div_le_one hm0).mpr hmR
    linarith
  have hc1 : 1-2/(m : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 2/(m : ℝ) := by positivity
    linarith
  have h := (rootSystem m).upper_iterate n D (1-2/(m : ℝ)) hc hc1 hroot
  have he : 1-(1-(1-2/(m : ℝ)))/(n+1 : ℝ)^D =
      1-2/((m : ℝ)*(n+1 : ℝ)^D) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  exact h

/-- An embedded cyclic list, with no repeated vertices. -/
def HasCycle (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ c : Fin L ↪ V, ∀ i, G.Adj (c i) (c (finRotate L i))

lemma rotate_val {L : ℕ} (i : Fin L) :
    (finRotate L i).val = (i.val+1)%L := by
  cases L with
  | zero => exact i.elim0
  | succ k =>
    rw [coe_finRotate]
    split_ifs with hi
    · subst i; simp
    · rw [Nat.mod_eq_of_lt (by have := Fin.val_lt_last hi; omega)]

lemma rotate_no_two {L : ℕ} (hL : 3 ≤ L) (i : Fin L) :
    finRotate L (finRotate L i) ≠ i := by
  cases L with
  | zero => omega
  | succ k =>
    intro he
    have h₁ : (finRotate (k+1) i).val = if i = Fin.last k then 0 else i.val+1 := coe_finRotate i
    have h₂ : (finRotate (k+1) (finRotate (k+1) i)).val =
        if finRotate (k+1) i = Fin.last k then 0 else (finRotate (k+1) i).val+1 :=
      coe_finRotate (finRotate (k+1) i)
    have h₃ : (finRotate (k+1) (finRotate (k+1) i)).val = i.val := congrArg Fin.val he
    change 3 ≤ k+1 at hL
    simp only [Fin.ext_iff, Fin.val_last] at h₁ h₂
    split_ifs at h₁ h₂ <;> omega

lemma cycle_indices_injective [DecidableEq V] {I : Type*} {L : ℕ} (hL : 3 ≤ L)
    (c : Fin L ↪ V) (idx : Fin L → I) (s : I → Finset V)
    (hs : ∀ i, s (idx i) = {c i,c (finRotate L i)}) : Function.Injective idx := by
  classical
  intro i j hij
  have he : ({c i,c (finRotate L i)} : Finset V) = {c j,c (finRotate L j)} := by
    rw [← hs i, hij, hs j]
  have h₁ : c i = c j ∨ c i = c (finRotate L j) := by
    have : c i ∈ ({c j,c (finRotate L j)} : Finset V) := by rw [← he]; simp
    simpa using this
  rcases h₁ with h₁ | h₁
  · exact c.injective h₁
  have h₂ : c (finRotate L i) = c j ∨ c (finRotate L i) = c (finRotate L j) := by
    have : c (finRotate L i) ∈ ({c j,c (finRotate L j)} : Finset V) := by rw [← he]; simp
    simpa using this
  rcases h₂ with h₂ | h₂
  · have hi := c.injective h₁
    have hj := c.injective h₂
    exact (rotate_no_two hL j (by rw [← hi,hj])).elim
  · exact (finRotate L).injective (c.injective h₂)

/-- Vertex map obtained by inserting one full fresh block on each cyclic edge. -/
def expandVertices {I : Type*} {L : ℕ} (n : ℕ) (c : Fin L ↪ V)
    (idx : Fin L → I) (z : Fin L × Fin (n+1)) : V ⊕ (I × Fin n) :=
  if h : z.2.val = 0 then .inl (c z.1)
  else .inr (idx z.1, ⟨z.2.val-1, by have := z.2.isLt; omega⟩)

lemma expandVertices_injective {I : Type*} {L : ℕ} (n : ℕ) (c : Fin L ↪ V)
    (idx : Fin L → I) (hidx : Function.Injective idx) :
    Function.Injective (expandVertices n c idx) := by
  intro z w he
  rcases z with ⟨i,j⟩
  rcases w with ⟨k,l⟩
  by_cases hj : j.val = 0
  · by_cases hl : l.val = 0
    · simp only [expandVertices, hj, hl, dite_true] at he
      have hik := c.injective (Sum.inl.inj he)
      have hjl : j = l := Fin.ext (hj.trans hl.symm)
      exact Prod.ext hik hjl
    · simp only [expandVertices, hj, hl, dite_true, dite_false] at he
      cases he
  · by_cases hl : l.val = 0
    · simp only [expandVertices, hj, hl, dite_true, dite_false] at he
      cases he
    · simp only [expandVertices, hj, hl, dite_false] at he
      have hh := Sum.inr.inj he
      have hik := hidx (congrArg Prod.fst hh)
      have hjl : j.val-1 = l.val-1 := congrArg (fun z => z.2.val) hh
      have hval : j.val = l.val := by omega
      exact Prod.ext hik (Fin.ext hval)

lemma rotate_product_internal {L n : ℕ} (i : Fin L) (j : Fin (n+1))
    (hj : j.val < n) :
    finRotate (L*(n+1)) (finProdFinEquiv (i,j)) =
      finProdFinEquiv (i,(⟨j.val+1,by omega⟩ : Fin (n+1))) := by
  apply Fin.ext
  rw [rotate_val]
  change (j.val+(n+1)*i.val+1)%(L*(n+1)) = j.val+1+(n+1)*i.val
  rw [Nat.mod_eq_of_lt]
  · omega
  · have hm := Nat.mul_le_mul_left (n+1) i.isLt
    nlinarith

lemma rotate_product_last {L n : ℕ} (i : Fin L) :
    finRotate (L*(n+1)) (finProdFinEquiv (i,Fin.last n)) =
      finProdFinEquiv (finRotate L i,(0 : Fin (n+1))) := by
  apply Fin.ext
  rw [rotate_val]
  change (n+(n+1)*i.val+1)%(L*(n+1)) = 0+(n+1)*(finRotate L i).val
  rw [rotate_val]
  rw [show n+(n+1)*i.val+1 = (n+1)*(i.val+1) by ring,
    Nat.mul_comm L (n+1), Nat.mul_mod_mul_left]
  simp

/-- A layer multiplies an embedded cycle length by `n+1`, using distinct attachment
indices for its distinct retained pairs. -/
theorem attach_cycle [DecidableEq V] {I : Type*} (G : SimpleGraph V) (a b : I → V)
    (n L : ℕ) (hL : 3 ≤ L) (hedges : ∀ i, G.Adj (a i) (b i))
    (c : Fin L ↪ V) (idx : Fin L → I) (hidx : Function.Injective idx)
    (hpairs : ∀ i, ({a (idx i), b (idx i)} : Finset V) = {c i,c (finRotate L i)}) :
    HasCycle (attach G a b n) (L*(n+1)) := by
  classical
  let e : Fin (L*(n+1)) ↪ (V ⊕ (I × Fin n)) :=
    ⟨fun z => expandVertices n c idx (finProdFinEquiv.symm z),
      (expandVertices_injective n c idx hidx).comp finProdFinEquiv.symm.injective⟩
  have eapply (i : Fin L) (j : Fin (n+1)) : e (finProdFinEquiv (i,j)) =
      expandVertices n c idx (i,j) := by
    change expandVertices n c idx (finProdFinEquiv.symm (finProdFinEquiv (i,j))) = _
    rw [Equiv.symm_apply_apply]
  have hstart (i : Fin L) : Sum.inl (c i) ∈ childBag a b n (idx i) := by
    have hm : c i ∈ ({a (idx i),b (idx i)} : Finset V) := by rw [hpairs i]; simp
    have hm' : c i = a (idx i) ∨ c i = b (idx i) := by simpa using hm
    rcases hm' with h | h
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl h))))
  have hfinish (i : Fin L) : Sum.inl (c (finRotate L i)) ∈ childBag a b n (idx i) := by
    have hm : c (finRotate L i) ∈ ({a (idx i),b (idx i)} : Finset V) := by rw [hpairs i]; simp
    have hm' : c (finRotate L i) = a (idx i) ∨ c (finRotate L i) = b (idx i) := by simpa using hm
    rcases hm' with h | h
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl h))))
  have hmem (i : Fin L) (j : Fin (n+1)) :
      expandVertices n c idx (i,j) ∈ childBag a b n (idx i) := by
    unfold expandVertices
    split_ifs with hj
    · exact hstart i
    · simp [childBag]
  refine ⟨e, ?_⟩
  intro z
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective z
  have hc := childBag_clique G a b n hedges (idx i)
  have neRotate : finProdFinEquiv (i,j) ≠ finRotate (L*(n+1)) (finProdFinEquiv (i,j)) := by
    intro he
    have hv := congrArg Fin.val he
    rw [rotate_val] at hv
    have htwo : 2 ≤ L*(n+1) := by nlinarith
    have hlt := (finProdFinEquiv (i,j)).isLt
    by_cases hlt' : (finProdFinEquiv (i,j)).val+1 < L*(n+1)
    · rw [Nat.mod_eq_of_lt hlt'] at hv
      omega
    · have heq : (finProdFinEquiv (i,j)).val+1 = L*(n+1) := by omega
      rw [heq,Nat.mod_self] at hv
      omega
  by_cases hj : j.val < n
  · have hneq := e.injective.ne neRotate
    rw [rotate_product_internal i j hj, eapply, eapply] at hneq ⊢
    exact hc (hmem i j) (hmem i ⟨j.val+1,by omega⟩) hneq
  · have hjlast : j = Fin.last n := Fin.ext (by have := j.isLt; dsimp; omega)
    subst j
    have hneq := e.injective.ne neRotate
    rw [rotate_product_last, eapply, eapply] at hneq ⊢
    have hlastmem := hmem i (Fin.last n)
    have hzeromem : expandVertices n c idx (finRotate L i,(0 : Fin (n+1))) ∈
        childBag a b n (idx i) := by simpa [expandVertices] using hfinish i
    exact hc hlastmem hzeromem hneq

def System.CoversEdges (S : System) : Prop :=
  ∀ u v, S.graph.Adj u v → ∃ b, u ∈ S.members b ∧ v ∈ S.members b

lemma System.index_for_edge (S : System) (hcover : S.CoversEdges) (u v : S.Vertex)
    (h : S.graph.Adj u v) : ∃ i : S.PairIndex, i.val.2 = {u,v} := by
  obtain ⟨b,hu,hv⟩ := hcover u v h
  refine ⟨⟨(b,{u,v}), ?_, ?_⟩, rfl⟩
  · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hu,hv⟩
  · simp [h.ne]

lemma System.old_mem_child (S : System) (n : ℕ) (i : S.PairIndex) (v : S.Vertex) :
    Sum.inl v ∈ (S.next n).members i ↔ v ∈ i.val.2 := by
  classical
  change Sum.inl v ∈ childBag S.left S.right n i ↔ _
  rw [(S.endpoints i).2]
  simp [childBag]

lemma System.next_covers (S : System) (n : ℕ) (hcover : S.CoversEdges) :
    (S.next n).CoversEdges := by
  classical
  intro u v h
  change (attach S.graph S.left S.right n).Adj u v at h
  change ∃ i, u ∈ childBag S.left S.right n i ∧ v ∈ childBag S.left S.right n i
  have hnew (i : S.PairIndex) (j : Fin n) :
      Sum.inr (i,j) ∈ childBag S.left S.right n i := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact (mem_fresh n i _).mpr ⟨j,rfl⟩
  have hleft (i : S.PairIndex) : Sum.inl (S.left i) ∈ childBag S.left S.right n i :=
    Finset.mem_insert_self _ _
  have hright (i : S.PairIndex) : Sum.inl (S.right i) ∈ childBag S.left S.right n i :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  rcases u with u | ⟨i,j⟩
  · rcases v with v | ⟨i,j⟩
    · obtain ⟨i,hi⟩ := S.index_for_edge hcover u v h
      refine ⟨i, ?_, ?_⟩
      · change Sum.inl u ∈ (S.next n).members i
        rw [S.old_mem_child,hi]; simp
      · change Sum.inl v ∈ (S.next n).members i
        rw [S.old_mem_child,hi]; simp
    · refine ⟨i, ?_, hnew i j⟩
      rcases h with rfl | rfl
      · exact hleft i
      · exact hright i
  · rcases v with v | ⟨k,l⟩
    · refine ⟨i, hnew i j, ?_⟩
      rcases h with rfl | rfl
      · exact hleft i
      · exact hright i
    · obtain ⟨rfl,_⟩ := h
      exact ⟨i, hnew i j, hnew i l⟩

lemma System.iterate_covers (S : System) (n D : ℕ) (hcover : S.CoversEdges) :
    (S.iterate n D).CoversEdges := by
  induction D with
  | zero => exact hcover
  | succ D ih => exact (S.iterate n D).next_covers n ih

lemma System.next_cycle (S : System) (n L : ℕ) (hL : 3 ≤ L)
    (hcover : S.CoversEdges) (hc : HasCycle S.graph L) :
    HasCycle (S.next n).graph (L*(n+1)) := by
  classical
  obtain ⟨c,hedge⟩ := hc
  have hidx (j : Fin L) := S.index_for_edge hcover _ _ (hedge j)
  choose idx hidx using hidx
  have hi : Function.Injective idx := cycle_indices_injective hL c idx
    (fun i => i.val.2) hidx
  have hpairs (j : Fin L) : ({S.left (idx j),S.right (idx j)} : Finset S.Vertex) =
      {c j,c (finRotate L j)} := (S.endpoints (idx j)).2.symm.trans (hidx j)
  exact attach_cycle S.graph S.left S.right n L hL S.endpoints_adj c idx hi hpairs

/-- The actual recursive clique family contains the exponentially long simple cycle,
without any cycle, circulation, or reconstruction premise at a later generation. -/
theorem System.iterate_cycle (S : System) (n D L : ℕ) (hL : 3 ≤ L)
    (hcover : S.CoversEdges) (hc : HasCycle S.graph L) :
    HasCycle (S.iterate n D).graph (L*(n+1)^D) := by
  induction D with
  | zero => simpa [System.iterate] using hc
  | succ D ih =>
    have hp : 1 ≤ (n+1)^D := one_le_pow₀ (by omega)
    have hl : 3 ≤ L*(n+1)^D := by nlinarith
    have h := (S.iterate n D).next_cycle n _ hl (S.iterate_covers n D hcover) ih
    simpa [System.iterate, pow_succ, Nat.mul_assoc] using h

theorem family_cycle (m n D : ℕ) (hm : 3 ≤ m) :
    HasCycle (family m n D).graph (m*(n+1)^D) := by
  have hcover : (rootSystem m).CoversEdges := by
    intro u v _
    exact ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩
  have hc : HasCycle (rootSystem m).graph m := by
    refine ⟨Function.Embedding.refl _, ?_⟩
    intro i
    change i ≠ finRotate m i
    intro he
    exact rotate_no_two hm i (by
      calc
        finRotate m (finRotate m i) = finRotate m i := congrArg (finRotate m) he.symm
        _ = i := he.symm)
  exact (rootSystem m).iterate_cycle n D m hm hcover hc

section CycleLower

def orderedGain (rank : V → ℕ) (x : E) (u v : V) : E :=
  if rank u < rank v then x else if rank v < rank u then -x else 0

omit [NormedSpace ℝ E] in
lemma orderedGain_reverse (rank : V → ℕ) (x : E) (u v : V) :
    orderedGain rank x v u = -orderedGain rank x u v := by
  unfold orderedGain
  split_ifs <;> (try omega) <;> simp

omit [NormedSpace ℝ E] in
lemma orderedGain_triangle (rank : V → ℕ) (x : E) (hx : ‖x‖ = 1) (a b c : V) :
    ‖defect (orderedGain rank x) a b c‖ ≤ 1 := by
  unfold defect orderedGain
  split_ifs <;> (try omega) <;> simp_all

def cycleRank {L : ℕ} (c : Fin L ↪ V) (v : V) : ℕ := by
  classical
  exact if h : ∃ i, c i = v then (Classical.choose h).val else L

@[simp] lemma cycleRank_apply {L : ℕ} (c : Fin L ↪ V) (i : Fin L) :
    cycleRank c (c i) = i.val := by
  unfold cycleRank
  split_ifs with h
  · exact congrArg Fin.val (c.injective (Classical.choose_spec h))
  · exact (h ⟨i,rfl⟩).elim

/-- The ordered unit cochain is a sharp scalar obstruction on every embedded cycle.
It works in each target containing a unit vector, with all vertex potentials free. -/
theorem cycle_lower (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (c : Fin (k+1) ↪ V)
    (hedge : ∀ i, G.Adj (c i) (c (finRotate (k+1) i)))
    (x : E) (hx : ‖x‖ = 1) :
    ∃ g : V → V → E,
      (∀ u v, g v u = -g u v) ∧
      (∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖defect g u v w‖ ≤ 1) ∧
      ∀ q : V → E, ∃ u v, G.Adj u v ∧
        (1-2/(k+1 : ℝ)) ≤ ‖residual g q u v‖ := by
  classical
  let g := orderedGain (cycleRank c) x
  have hg (i : Fin (k+1)) : g (c i) (c (finRotate (k+1) i)) =
      if i = Fin.last k then -x else x := by
    by_cases hi : i = Fin.last k
    · subst i
      have hk0 : 0 < k := by omega
      simp [g, orderedGain, cycleRank_apply, hk0]
    · simp [g, orderedGain, cycleRank_apply, hi]
  have hsum : (∑ i : Fin (k+1), g (c i) (c (finRotate (k+1) i))) =
      ((k+1 : ℝ)-2) • x := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last k))]
    rw [hg, ite_eq_left rfl]
    have he : (∑ i ∈ Finset.univ.erase (Fin.last k),
        g (c i) (c (finRotate (k+1) i))) = k • x := by
      calc
        _ = ∑ _i ∈ Finset.univ.erase (Fin.last k), x := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hg, ite_eq_right (Finset.mem_erase.mp hi).1]
        _ = _ := by simp
    rw [he, ← Nat.cast_smul_eq_nsmul ℝ]
    module
  refine ⟨g, orderedGain_reverse _ _, ?_, ?_⟩
  · intro u v w _ _ _
    exact orderedGain_triangle _ x hx u v w
  · intro q
    by_contra! h
    have tel : (∑ i : Fin (k+1), (q (c (finRotate (k+1) i))-q (c i))) = 0 := by
      have heq : (∑ i : Fin (k+1), q (c (finRotate (k+1) i))) =
          ∑ i : Fin (k+1), q (c i) :=
        Equiv.sum_comp (finRotate (k+1)) (fun i => q (c i))
      rw [Finset.sum_sub_distrib, heq]
      exact sub_self _
    have hs : (∑ i : Fin (k+1), residual g q (c i) (c (finRotate (k+1) i))) =
        ((k+1 : ℝ)-2) • x := by
      simp only [residual]
      rw [Finset.sum_sub_distrib, hsum, tel, sub_zero]
    have hn : (0 : ℝ) < k+1 := by positivity
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hb : (k+1 : ℝ)-2 ≤ ∑ i : Fin (k+1),
        ‖residual g q (c i) (c (finRotate (k+1) i))‖ := by
      have hh := norm_sum_le Finset.univ
        (fun i => residual g q (c i) (c (finRotate (k+1) i)))
      rw [hs, norm_smul, Real.norm_eq_abs, hx, mul_one,
        abs_of_nonneg (by linarith)] at hh
      exact hh
    have hl : (∑ i : Fin (k+1), ‖residual g q (c i) (c (finRotate (k+1) i))‖) <
        (k+1 : ℝ) * (1-2/(k+1 : ℝ)) := by
      calc
        _ < ∑ _i : Fin (k+1), (1-2/(k+1 : ℝ)) :=
          Finset.sum_lt_sum_of_nonempty ⟨0,Finset.mem_univ _⟩
            (fun i _ => h _ _ (hedge i))
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have he : (k+1 : ℝ) * (1-2/(k+1 : ℝ)) = (k+1 : ℝ)-2 := by
      field_simp
    rw [he] at hl
    exact hl.not_ge hb
end CycleLower

section NonzeroTarget
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

/-- A long simple cycle gives the same obstruction in every nonzero real normed
space. Completeness is unnecessary. -/
theorem hasCycle_lower (G : SimpleGraph V) (L : ℕ) (hL : 3 ≤ L)
    (hc : HasCycle G L) :
    ∃ g : V → V → F,
      (∀ u v, g v u = -g u v) ∧
      (∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖defect g u v w‖ ≤ 1) ∧
      ∀ q : V → F, ∃ u v, G.Adj u v ∧
        (1-2/(L : ℝ)) ≤ ‖residual g q u v‖ := by
  obtain ⟨y,hy⟩ := exists_ne (0 : F)
  let x : F := ‖y‖⁻¹ • y
  have hx : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  cases L with
  | zero => omega
  | succ k =>
    obtain ⟨c,hedge⟩ := hc
    simpa only [Nat.cast_add,Nat.cast_one] using cycle_lower G k (by omega) c hedge x hx

/-- The unconditional matching lower ingredient on the actual arbitrary-depth
pair-retention family, for every nonzero normed (hence every nonzero Banach) target. -/
theorem family_lower (m n D : ℕ) (hm : 3 ≤ m) :
    ∃ g : (family m n D).Vertex → (family m n D).Vertex → F,
      (∀ u v, g v u = -g u v) ∧
      (∀ u v w, (family m n D).graph.Adj u v → (family m n D).graph.Adj v w →
        (family m n D).graph.Adj u w → ‖defect g u v w‖ ≤ 1) ∧
      ∀ q : (family m n D).Vertex → F, ∃ u v, (family m n D).graph.Adj u v ∧
        (1-2/((m : ℝ)*(n+1 : ℝ)^D)) ≤ ‖residual g q u v‖ := by
  have hp : 1 ≤ (n+1)^D := one_le_pow₀ (by omega)
  have hL : 3 ≤ m*(n+1)^D := by nlinarith
  have h := hasCycle_lower (F := F) (family m n D).graph _ hL (family_cycle m n D hm)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h

/-- All recursive upper and lower ingredients, on one actual graph and in the same
arbitrary nonzero target. The sole upper premise concerns the initial complete
clique, whose averaging theorem is already frozen in the repository. -/
theorem family_matching_bounds (m n D : ℕ) (hm : 3 ≤ m)
    (hroot : Upper (⊤ : SimpleGraph (Fin m)) F (1-2/(m : ℝ))) :
    Upper (family m n D).graph F (1-2/((m : ℝ)*(n+1 : ℝ)^D)) ∧
    ∃ g : (family m n D).Vertex → (family m n D).Vertex → F,
      (∀ u v, g v u = -g u v) ∧
      (∀ u v w, (family m n D).graph.Adj u v → (family m n D).graph.Adj v w →
        (family m n D).graph.Adj u w → ‖defect g u v w‖ ≤ 1) ∧
      ∀ q : (family m n D).Vertex → F, ∃ u v, (family m n D).graph.Adj u v ∧
        (1-2/((m : ℝ)*(n+1 : ℝ)^D)) ≤ ‖residual g q u v‖ :=
  ⟨family_upper_from_complete m n D (by omega) hroot, family_lower m n D hm⟩
end NonzeroTarget

end
end SimpleGraph.PairRetention
