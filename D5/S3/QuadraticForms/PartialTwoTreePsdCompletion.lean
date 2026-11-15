/- GID: D5/S3/QuadraticForms/PartialTwoTreePsdCompletion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/PartialTwoTreePsdCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed-walk reduction for simultaneous partial two-tree angle completion. -/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Paths
open SimpleGraph
open scoped BigOperators
namespace D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
variable {V : Type*}
private def liftGraph (G : SimpleGraph V) : SimpleGraph (V × Bool) where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩
private def project (G : SimpleGraph V) : liftGraph G →g G where
  toFun := Prod.fst
  map_rel' h := h
private noncomputable def weight (θ : V → V → ℝ) (a b : V × Bool) : ℝ :=
  if a.2 = b.2 then θ a.1 b.1 else Real.pi - θ a.1 b.1
private noncomputable def total {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    {a b : W} (p : K.Walk a b) : ℝ :=
  (p.darts.map fun d => w d.fst d.snd).sum
@[simp] private lemma total_nil {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ) (a : W) :
    total w (Walk.nil : K.Walk a a) = 0 := rfl
@[simp] private lemma total_cons {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    {a b c : W} (h : K.Adj a b) (p : K.Walk b c) :
    total w (Walk.cons h p) = w a b + total w p := rfl
@[simp] private lemma total_append {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    {a b c : W} (p : K.Walk a b) (q : K.Walk b c) :
    total w (p.append q) = total w p + total w q := by
  simp [total, Walk.darts_append, List.map_append, List.sum_append]
@[simp] private lemma total_copy {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    {a b c d : W} (p : K.Walk a b) (h : a = c) (h' : b = d) :
    total w (p.copy h h') = total w p := by subst_vars; rfl
private lemma total_nonneg {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    (hw : ∀ a b, K.Adj a b → 0 ≤ w a b) {a b : W} (p : K.Walk a b) :
    0 ≤ total w p := by
  induction p with
  | nil => simp
  | @cons a b c h p ih => simpa using add_nonneg (hw a b h) ih
private lemma total_subwalk_le {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    (hw : ∀ a b, K.Adj a b → 0 ≤ w a b) {a b c d : W}
    (p : K.Walk a b) (q : K.Walk c d) (h : q.IsSubwalk p) : total w q ≤ total w p := by
  obtain ⟨r,s,rfl⟩ := h
  simp only [total_append]
  linarith [total_nonneg w hw r, total_nonneg w hw s]
private lemma weight_nonneg (G : SimpleGraph V) (θ : V → V → ℝ)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (a b : V × Bool) (h : (liftGraph G).Adj a b) : 0 ≤ weight θ a b := by
  dsimp [weight]
  split_ifs <;> linarith [(hθ a.1 b.1 h).1, (hθ a.1 b.1 h).2]
private lemma odd_walk_reduction (G : SimpleGraph V) (θ : V → V → ℝ)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (elementary : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → (p.map (project G)).tail.IsPath →
      Real.pi ≤ total (weight θ) p) :
    ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p := by
  classical
  have hw := weight_nonneg G θ hθ
  suffices aux : ∀ n : ℕ, ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      p.length = n → a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p by
    intro a b p hab hbc
    exact aux p.length p rfl hab hbc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hp hab hbc
    by_contra hbad
    have hlt : total (weight θ) p < Real.pi := lt_of_not_ge hbad
    have hel : (p.map (project G)).tail.IsPath := by
      apply (Walk.IsPath.getVert_injOn_iff _).mp
      suffices ordered : ∀ i j : ℕ, i ≤ (p.map (project G)).tail.length →
          j ≤ (p.map (project G)).tail.length →
          (p.map (project G)).tail.getVert i = (p.map (project G)).tail.getVert j →
          i < j → False by
        intro i hi j hj heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact ordered i j hi hj heq h
        · exact ordered j i hj hi heq.symm h
      intro i j hi hj heq hij
      have hip : i + 1 ≤ p.length := by
        have : (p.map (project G)).tail.length + 1 = p.length := by
          rw [← Walk.length_map (project G) p]
          apply Walk.length_tail_add_one
          rw [Walk.nil_map_iff]
          intro hn
          exact hbc (congrArg Prod.snd hn.eq)
        omega
      have hjp : j + 1 ≤ p.length := by
        have : (p.map (project G)).tail.length + 1 = p.length := by
          rw [← Walk.length_map (project G) p]
          apply Walk.length_tail_add_one
          rw [Walk.nil_map_iff]
          intro hn
          exact hbc (congrArg Prod.snd hn.eq)
        omega
      have he : (p.getVert (i + 1)).1 = (p.getVert (j + 1)).1 := by
        rw [Walk.getVert_tail, Walk.getVert_tail, Walk.getVert_map, Walk.getVert_map] at heq
        exact heq
      let q := ((p.drop (i + 1)).take (j - i)).copy rfl
        (by rw [Walk.drop_getVert]; congr 1; omega :
          (p.drop (i + 1)).getVert (j - i) = p.getVert (j + 1))
      have hql : q.length < n := by
        simp only [q, Walk.length_copy, Walk.take_length, Walk.drop_length]
        omega
      have hqsub : q.IsSubwalk p := by
        apply Walk.IsSubwalk.trans (p₂ := p.drop (i + 1))
        · exact ((p.drop (i + 1)).isSubwalk_take (j - i)).copy rfl _ rfl rfl
        · exact p.isSubwalk_drop (i + 1)
      by_cases hb : (p.getVert (i + 1)).2 = (p.getVert (j + 1)).2
      · have hev : p.getVert (i + 1) = p.getVert (j + 1) := Prod.ext he hb
        let r := (p.take (i + 1)).append ((p.drop (j + 1)).copy hev.symm rfl)
        have hrl : r.length < n := by
          simp only [r, Walk.length_append, Walk.take_length, Walk.length_copy,
            Walk.drop_length]
          omega
        have hmono := total_subwalk_le (weight θ) hw (p.take (j + 1)) (p.take (i + 1))
          (p.take_isSubwalk_take (by omega))
        have hrle : total (weight θ) r ≤ total (weight θ) p := by
          have ht := congrArg (total (weight θ)) (p.append_take_drop_eq (j + 1))
          simp only [total_append] at ht
          simp only [r, total_append, total_copy]
          linarith
        have hr := ih r.length hrl r rfl hab hbc
        linarith
      · have hq := ih q.length hql q rfl he hb
        have hle := total_subwalk_le (weight θ) hw p q hqsub
        have hwhole : Real.pi ≤ total (weight θ) p := hq.trans hle
        linarith
    exact hbad (elementary p hab hbc hel)
end D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
