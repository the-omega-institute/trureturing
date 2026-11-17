/- GID: D5/S3/QuadraticForms/PartialTwoTreePsdCompletion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/PartialTwoTreePsdCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All cycle angle inequalities characterize real rank-three completion on partial two-trees. -/

import D5.S3.QuadraticForms.CycleRankThreePsdCompletion
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Order.Preorder.Finite
open SimpleGraph
open scoped BigOperators
namespace D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Fintype.ofFinite
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
private lemma first_new {W : Type*} (K L : SimpleGraph W) (w : W → W → ℝ)
    (N : W → W → Prop)
    (hKL : ∀ a b, L.Adj a b → K.Adj a b ∨ N a b)
    {a b : W} (p : L.Walk a b) :
    (∃ q : K.Walk a b, total w p = total w q) ∨
    ∃ (c d : W) (q : K.Walk a c) (r : L.Walk d b),
      N c d ∧ total w p = total w q + w c d + total w r ∧ r.length < p.length := by
  induction p with
  | nil => exact Or.inl ⟨.nil, rfl⟩
  | @cons a c b h p ih =>
    rcases hKL a c h with hold | hnew
    · rcases ih with ⟨q,hq⟩ | ⟨d,e,q,r,hn,he,hl⟩
      · exact Or.inl ⟨.cons hold q, by simp [hq]⟩
      · exact Or.inr ⟨d,e,.cons hold q,r,hn, by simp [he]; ring, by simp; omega⟩
    · exact Or.inr ⟨a,c,.nil,p,hnew,by simp,by simp⟩

private lemma boundary_gluing {W : Type*} (K L : SimpleGraph W) (w : W → W → ℝ)
    (S : Set W) (δ : W → W → ℝ) (N : W → W → Prop)
    (hKL : ∀ a b, L.Adj a b → K.Adj a b ∨ N a b)
    (hnew : ∀ a b, N a b → a ∈ S ∧ b ∈ S ∧ δ a b ≤ w a b)
    (htri : ∀ a b c, a ∈ S → b ∈ S → c ∈ S → δ a c ≤ δ a b + δ b c)
    (hold : ∀ {a b}, a ∈ S → b ∈ S → ∀ p : K.Walk a b, δ a b ≤ total w p) :
    ∀ {a b}, a ∈ S → b ∈ S → ∀ p : L.Walk a b, δ a b ≤ total w p := by
  suffices aux : ∀ n : ℕ, ∀ {a b}, a ∈ S → b ∈ S →
      ∀ p : L.Walk a b, p.length = n → δ a b ≤ total w p by
    intro a b ha hb p
    exact aux p.length ha hb p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b ha hb p hp
    rcases first_new K L w N hKL p with ⟨q,he⟩ | ⟨c,d,q,r,hn,he,hl⟩
    · rw [he]
      exact hold ha hb q
    · obtain ⟨hc,hd,heedge⟩ := hnew c d hn
      have hq := hold ha hc q
      have hr := ih r.length (by omega) hd hb r rfl
      have ht₁ := htri a c b ha hc hb
      have ht₂ := htri c d b hc hd hb
      linarith

private lemma total_reverse {W : Type*} {K : SimpleGraph W} (w : W → W → ℝ)
    (hw : ∀ a b, w a b = w b a) {a b : W} (p : K.Walk a b) :
    total w p.reverse = total w p := by
  induction p with
  | nil => simp
  | @cons a b c h p ih => simp [Walk.reverse_cons, total_append, ih, hw, add_comm]

private def flip (G : SimpleGraph V) : liftGraph G →g liftGraph G where
  toFun a := (a.1, !a.2)
  map_rel' h := h
private lemma total_flip (G : SimpleGraph V) (θ : V → V → ℝ)
    {a b : V × Bool} (p : (liftGraph G).Walk a b) :
    total (weight θ) (p.map (flip G)) = total (weight θ) p := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    simp only [Walk.map_cons, total_cons, ih]
    congr 1
    change (if (!a.2) = (!b.2) then θ a.1 b.1 else Real.pi - θ a.1 b.1) = _
    simp [weight]
private lemma weight_symm (θ : V → V → ℝ) (hθ : ∀ a b, θ a b = θ b a)
    (a b : V × Bool) : weight θ a b = weight θ b a := by
  simp only [weight, hθ a.1 b.1, eq_comm]

private lemma path_interval (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (hclosed : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p)
    (u v : V) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ Real.pi ∧
      (∀ p : (liftGraph G).Walk (u,false) (v,false), x ≤ total (weight θ) p) ∧
      (∀ p : (liftGraph G).Walk (u,false) (v,true), Real.pi - x ≤ total (weight θ) p) := by
  classical
  let L : Set ℝ := insert 0 {z | ∃ p : (liftGraph G).Walk (u,false) (v,true),
      z = Real.pi - total (weight θ) p}
  have hw := weight_nonneg G θ hθ
  have hL : L.Nonempty := ⟨0, Or.inl rfl⟩
  have hupper : ∀ z ∈ L, z ≤ Real.pi := by
    rintro z (rfl | ⟨p,rfl⟩)
    · exact Real.pi_pos.le
    · linarith [total_nonneg (weight θ) hw p]
  have hbounded : BddAbove L := ⟨Real.pi, hupper⟩
  refine ⟨sSup L, le_csSup hbounded (Or.inl rfl), csSup_le hL hupper, ?_, ?_⟩
  · intro p
    apply csSup_le hL
    rintro z (rfl | ⟨q,rfl⟩)
    · exact total_nonneg (weight θ) hw p
    · have hc := hclosed (p.append ((q.map (flip G)).reverse)) rfl (by change false ≠ (!false); decide)
      simp only [total_append, total_reverse _ (weight_symm θ hsym), total_flip] at hc
      linarith
  · intro p
    have hp : Real.pi - total (weight θ) p ∈ L := Or.inr ⟨p,rfl⟩
    have := le_csSup hbounded hp
    linarith

private noncomputable def boundaryDist (x : ℝ) (a b : V × Bool) : ℝ := by
  classical
  exact if a.1 = b.1 then (if a.2 = b.2 then 0 else Real.pi)
  else (if a.2 = b.2 then x else Real.pi - x)
private lemma boundary_triangle {u v : V} (hne : u ≠ v) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi)
    (a b c : V × Bool) (ha : a.1 = u ∨ a.1 = v)
    (hb : b.1 = u ∨ b.1 = v) (hc : c.1 = u ∨ c.1 = v) :
    boundaryDist x a c ≤ boundaryDist x a b + boundaryDist x b c := by
  classical
  rcases a with ⟨a,sa⟩; rcases b with ⟨b,sb⟩; rcases c with ⟨c,sc⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    cases sa <;> cases sb <;> cases sc <;>
    simp_all [boundaryDist, Ne.symm hne] <;> linarith [Real.pi_pos]
private lemma interval_bound (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (hclosed : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p)
    {u v : V} (hne : u ≠ v) {x : ℝ}
    (h₀ : ∀ p : (liftGraph G).Walk (u,false) (v,false), x ≤ total (weight θ) p)
    (h₁ : ∀ p : (liftGraph G).Walk (u,false) (v,true), Real.pi - x ≤ total (weight θ) p)
    {a b : V × Bool} (ha : a.1 = u ∨ a.1 = v) (hb : b.1 = u ∨ b.1 = v)
    (p : (liftGraph G).Walk a b) : boundaryDist x a b ≤ total (weight θ) p := by
  classical
  have hs (a b : V × Bool) : boundaryDist x a b = boundaryDist x b a := by
    simp only [boundaryDist, eq_comm]
  have pair : ∀ (sa sb : Bool) (p : (liftGraph G).Walk (u,sa) (v,sb)),
      boundaryDist x (u,sa) (v,sb) ≤ total (weight θ) p := by
    intro sa sb p
    cases sa <;> cases sb
    · simpa [boundaryDist, hne] using h₀ p
    · simpa [boundaryDist, hne] using h₁ p
    · have hh := h₁ (p.map (flip G))
      simp only [total_flip] at hh
      simpa [boundaryDist, hne] using hh
    · have hh := h₀ (p.map (flip G))
      simp only [total_flip] at hh
      simpa [boundaryDist, hne] using hh
  by_cases hab : a.1 = b.1
  · by_cases hbits : a.2 = b.2
    · simpa [boundaryDist, hab, hbits] using total_nonneg (weight θ) (weight_nonneg G θ hθ) p
    · simpa [boundaryDist, hab, hbits] using hclosed p hab hbits
  · rcases a with ⟨a,sa⟩; rcases b with ⟨b,sb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact pair _ _ p
    · rw [hs, ← total_reverse _ (weight_symm θ hsym) p]
      exact pair _ _ p.reverse
    · exact (hab rfl).elim

private lemma total_congr {W : Type*} {K : SimpleGraph W} (w w' : W → W → ℝ)
    (hw : ∀ a b, K.Adj a b → w a b = w' a b) {a b : W} (p : K.Walk a b) :
    total w p = total w' p := by
  induction p with
  | nil => simp
  | @cons a b c h p ih => simp [hw a b h, ih]

private lemma total_mapLe {W : Type*} {K L : SimpleGraph W} (w : W → W → ℝ) (h : K ≤ L)
    {a b : W} (p : K.Walk a b) : total w (p.mapLe h) = total w p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change w _ _ + total w (p.mapLe _) = w _ _ + total w p
    rw [ih]
    rfl

private noncomputable def insertAngle (θ : V → V → ℝ) (u v : V) (x : ℝ) (a b : V) : ℝ := by
  classical
  exact if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then x else θ a b

private def insertGraph (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧ a ≠ b
  symm := ⟨by intro a b h; rcases h with h | ⟨h,hn⟩
              · exact Or.inl h.symm
              · exact Or.inr ⟨by tauto, Ne.symm hn⟩⟩
  loopless := ⟨by intro a h; rcases h with h | ⟨_,h⟩; exact h.ne rfl; exact h rfl⟩
private lemma extend_one (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (hclosed : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p)
    {u v : V} (hne : u ≠ v) (hnot : ¬ G.Adj u v) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ Real.pi ∧
      ∀ {a b : V × Bool} (p : (liftGraph (insertGraph G u v)).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight (insertAngle θ u v x)) p := by
  classical
  obtain ⟨x,hx₀,hx₁,h₀,h₁⟩ := path_interval G θ hsym hθ hclosed u v
  refine ⟨x,hx₀,hx₁,?_⟩
  let θ' := insertAngle θ u v x
  let S : Set (V × Bool) := {a | a.1 = u ∨ a.1 = v}
  let N : (V × Bool) → (V × Bool) → Prop := fun a b =>
    ((a.1 = u ∧ b.1 = v) ∨ (a.1 = v ∧ b.1 = u))
  have hsame (a b : V × Bool) (h : (liftGraph G).Adj a b) :
      weight θ' a b = weight θ a b := by
    have hn : ¬ ((a.1 = u ∧ b.1 = v) ∨ (a.1 = v ∧ b.1 = u)) := by
      rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
      · exact hnot (ha ▸ hb ▸ h)
      · exact hnot (hb ▸ ha ▸ h.symm)
    simp [weight, θ', insertAngle, hn]
  have hsplit : ∀ a b, (liftGraph (insertGraph G u v)).Adj a b →
      (liftGraph G).Adj a b ∨ N a b := by
    intro a b h
    exact h.elim Or.inl (fun hh => Or.inr hh.1)
  have hold {a b : V × Bool} (ha : a ∈ S) (hb : b ∈ S) (p : (liftGraph G).Walk a b) :
      boundaryDist x a b ≤ total (weight θ') p := by
    rw [total_congr _ _ hsame]
    exact interval_bound G θ hsym hθ hclosed hne h₀ h₁ ha hb p
  have hnew : ∀ a b, N a b → a ∈ S ∧ b ∈ S ∧
      boundaryDist x a b ≤ weight θ' a b := by
    intro a b hn
    change ((a.1 = u ∧ b.1 = v) ∨ (a.1 = v ∧ b.1 = u)) at hn
    have hab : a.1 ≠ b.1 := by
      rcases hn with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · simpa only [ha,hb] using hne
      · simpa only [ha,hb] using Ne.symm hne
    refine ⟨by rcases hn with h | h; exact Or.inl h.1; exact Or.inr h.1,
      by rcases hn with h | h; exact Or.inr h.2; exact Or.inl h.2, ?_⟩
    simp only [boundaryDist, ite_eq_right hab, weight, θ', insertAngle, ite_eq_left hn, le_refl]
  have hbound : ∀ {a b}, a ∈ S → b ∈ S →
      ∀ p : (liftGraph (insertGraph G u v)).Walk a b, boundaryDist x a b ≤ total (weight θ') p := boundary_gluing (liftGraph G) (liftGraph (insertGraph G u v))
    (weight θ') S (boundaryDist x) N hsplit hnew
    (fun a b c ha hb hc => boundary_triangle hne ⟨hx₀,hx₁⟩ a b c ha hb hc) hold
  intro a b p hab hbits
  rcases first_new (liftGraph G) (liftGraph (insertGraph G u v)) (weight θ') N hsplit p with
    ⟨q,he⟩ | ⟨c,d,q,r,hn,he,hl⟩
  · rw [he, total_congr _ _ hsame]
    exact hclosed q hab hbits
  · change ((c.1 = u ∧ d.1 = v) ∨ (c.1 = v ∧ d.1 = u)) at hn
    have hflip : (flip G) a = b := by
      change (a.1,!a.2) = b
      apply Prod.ext (show (a.1,!a.2).1 = b.1 from hab)
      change (!a.2) = b.2
      cases ha : a.2 <;> cases hb : b.2 <;> simp only [ha,hb] at hbits ⊢ <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_true_eq_false, not_false_eq_true]
    let q' := (q.map (flip G)).copy hflip rfl
    have hq' : total (weight θ') q' = total (weight θ') q := by
      simp only [q', total_copy]
      rw [total_congr _ _ hsame, total_flip,
        total_congr _ _ hsame]
    have hcd := hnew c d hn
    have hqbound := hbound hcd.2.1
      (by change (flip G c).1 = u ∨ (flip G c).1 = v; exact hcd.1)
      (r.append (q'.mapLe (show liftGraph G ≤ liftGraph (insertGraph G u v) from fun i j h => Or.inl h)))
    rw [total_append, total_mapLe, hq'] at hqbound
    have hsum : boundaryDist x d (flip G c) + weight θ' c d = Real.pi := by
      have hnecd : c.1 ≠ d.1 := by
        rcases hn with ⟨hc,hd⟩ | ⟨hc,hd⟩
        · simpa only [hc,hd] using hne
        · simpa only [hc,hd] using Ne.symm hne
      change boundaryDist x d (c.1,!c.2) + weight θ' c d = _
      simp only [boundaryDist, ite_eq_right (Ne.symm hnecd), weight, θ', insertAngle, ite_eq_left hn]
      cases hc : c.2 <;> cases hd : d.2 <;>
        simp only [hc,hd,Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.true_eq_false,
          ite_true,ite_false] <;> ring
    linarith
private lemma darts_sum {W R : Type*} [AddCommMonoid R] {K : SimpleGraph W}
    {a b : W} (p : K.Walk a b) (f : K.Dart → R) :
    (p.darts.map f).sum = ∑ i : Fin p.length,
      f ⟨(p.getVert i, p.getVert (i + 1)),p.adj_getVert_succ i.isLt⟩ := by
  have he : p.darts = List.ofFn (fun i : Fin p.length =>
      (⟨(p.getVert i, p.getVert (i + 1)),p.adj_getVert_succ i.isLt⟩ : K.Dart)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact p.darts_getElem_eq_getVert i hi
  rw [he, List.map_ofFn, List.sum_ofFn]
  rfl

private noncomputable def flips {a b : V × Bool} {G : SimpleGraph V} (p : (liftGraph G).Walk a b) : ℕ :=
  (p.darts.map fun d => if d.fst.2 = d.snd.2 then 0 else 1).sum
private lemma flips_parity {G : SimpleGraph V} {a b : V × Bool} (p : (liftGraph G).Walk a b) :
    Odd (flips p) ↔ a.2 ≠ b.2 := by
  induction p with
  | nil => simp [flips]
  | @cons a b c h p ih =>
    change Odd ((if a.2 = b.2 then 0 else 1) + flips p) ↔ _
    cases ha : a.2 <;> cases hb : b.2 <;> cases hc : c.2 <;>
      simp only [ha,hb,hc] at ih ⊢ <;>
      simp_all

private lemma elementary_cost (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a)
    (hcycles : ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, θ (c i) (c (finRotate m i))) -
        (∑ i ∈ Finset.univ \ F, θ (c i) (c (finRotate m i))) ≤
          ((F.card : ℝ) - 1) * Real.pi)
    {a b : V × Bool} (p : (liftGraph G).Walk a b)
    (hab : a.1 = b.1) (hbits : a.2 ≠ b.2) (hp : (p.map (project G)).tail.IsPath) :
    Real.pi ≤ total (weight θ) p := by
  classical
  have hpos : 0 < p.length := by
    by_contra hn
    have hh := Walk.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
    exact hbits (congrArg Prod.snd hh.eq)
  have htwo : 1 < p.length := by
    by_contra hn
    have hlen : p.length = 1 := by omega
    have hh := p.adj_getVert_succ hpos
    have he : p.getVert (0 + 1) = b := by simpa [hlen] using p.getVert_length
    rw [he, Walk.getVert_zero] at hh
    exact (show G.Adj a.1 b.1 from hh).ne hab
  have hlast : (p.getVert p.length).1 = (p.getVert 0).1 := by simpa using hab.symm
  have hnext (i : Fin p.length) :
      (p.getVert (finRotate p.length i)).1 = (p.getVert (i + 1)).1 := by
    have : NeZero p.length := ⟨by omega⟩
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt htwo]
    by_cases hi : i.val + 1 < p.length
    · rw [Nat.mod_eq_of_lt hi]
    · have hlast' : i.val + 1 = p.length := by omega
      rw [hlast', Nat.mod_self]
      exact hlast.symm

  by_cases hsmall : p.length < 3
  · cases p with
    | nil => simp at hpos
    | @cons a c b h q =>
      cases q with
      | nil => exact (show G.Adj a.1 b.1 from h).ne hab |>.elim
      | @cons c d b h' r =>
        have hr : r.Nil := by apply Walk.length_eq_zero_iff.mp; simp only [Walk.length_cons] at hsmall; omega
        cases hr
        simp only [total_cons, total_nil, add_zero, weight]
        have hsym' : θ a.1 c.1 = θ c.1 b.1 := by rw [hsym,hab]
        cases ha : a.2 <;> cases hc : c.2 <;> cases hb : b.2 <;>
          simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
            ite_true, ite_false, ne_eq, not_true_eq_false] <;> linarith
  · let c : Fin p.length → V := fun i => (p.getVert i).1
    have hinj : Function.Injective c := by
      intro i j he
      apply Fin.ext
      by_cases hi : i.val = 0
      · by_cases hj : j.val = 0
        · omega
        · have hj' : j.val - 1 ≤ (p.map (project G)).tail.length := by
            rw [Walk.length_tail]; simp; omega
          have hn' : p.length - 1 ≤ (p.map (project G)).tail.length := by
            rw [Walk.length_tail]; simp
          have hhe : (p.map (project G)).tail.getVert (j.val - 1) =
              (p.map (project G)).tail.getVert (p.length - 1) := by
            simp only [Walk.getVert_tail, Walk.getVert_map]
            change (p.getVert (j.val - 1 + 1)).1 = (p.getVert (p.length - 1 + 1)).1
            rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
            exact he.symm.trans (by simpa [c,hi] using hab)
          have := hp.getVert_injOn hj' hn' hhe
          omega
      · by_cases hj : j.val = 0
        · have hi' : i.val - 1 ≤ (p.map (project G)).tail.length := by rw [Walk.length_tail]; simp; omega
          have hn' : p.length - 1 ≤ (p.map (project G)).tail.length := by rw [Walk.length_tail]; simp
          have hhe : (p.map (project G)).tail.getVert (i.val - 1) =
              (p.map (project G)).tail.getVert (p.length - 1) := by
            simp only [Walk.getVert_tail, Walk.getVert_map]
            change (p.getVert (i.val - 1 + 1)).1 = (p.getVert (p.length - 1 + 1)).1
            rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
            exact he.trans (by simpa [c,hj] using hab)
          have := hp.getVert_injOn hi' hn' hhe
          omega
        · have hi' : i.val - 1 ≤ (p.map (project G)).tail.length := by rw [Walk.length_tail]; simp; omega
          have hj' : j.val - 1 ≤ (p.map (project G)).tail.length := by rw [Walk.length_tail]; simp; omega
          have hhe : (p.map (project G)).tail.getVert (i.val - 1) =
              (p.map (project G)).tail.getVert (j.val - 1) := by
            simp only [Walk.getVert_tail, Walk.getVert_map]
            change (p.getVert (i.val - 1 + 1)).1 = (p.getVert (j.val - 1 + 1)).1
            rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
            exact he
          have := hp.getVert_injOn hi' hj' hhe
          omega
    let F : Finset (Fin p.length) := Finset.univ.filter fun i =>
      (p.getVert i).2 ≠ (p.getVert (i + 1)).2
    have hcard : F.card = flips p := by
      rw [flips, darts_sum]
      change (Finset.univ.filter (fun i : Fin p.length => (p.getVert i).2 ≠ (p.getVert (i+1)).2)).card = _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ne_eq]
      split_ifs <;> simp_all
    have hodd : Odd F.card := hcard ▸ (flips_parity p).mpr hbits
    have hedges (i : Fin p.length) : G.Adj (c i) (c (finRotate p.length i)) := by
      change G.Adj (p.getVert i).1 (p.getVert (finRotate p.length i)).1
      rw [hnext]
      exact p.adj_getVert_succ i.isLt
    have hh := hcycles p.length (by omega) c hinj hedges F hodd
    have hecost : total (weight θ) p = (F.card : ℝ) * Real.pi -
        (∑ i ∈ F, θ (c i) (c (finRotate p.length i))) +
        (∑ i ∈ Finset.univ \ F, θ (c i) (c (finRotate p.length i))) := by
      rw [total, darts_sum]
      simp only [weight]
      have heq (i : Fin p.length) :
        (if (p.getVert i).2 = (p.getVert (i+1)).2 then θ (p.getVert i).1 (p.getVert (i+1)).1
          else Real.pi - θ (p.getVert i).1 (p.getVert (i+1)).1) =
        if i ∈ F then Real.pi - θ (c i) (c (finRotate p.length i)) else θ (c i) (c (finRotate p.length i)) := by
        simp only [c, hnext, F, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs <;> simp_all
      simp_rw [heq]
      rw [Finset.sum_ite]
      have hcomp : Finset.univ.filter (fun i : Fin p.length => i ∉ F) = Finset.univ \ F := by ext; simp
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, hcomp, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
    linarith
private lemma complete_extension [Finite V] (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a) (hd : ∀ a, θ a a = 0)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (hclosed : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p) :
    ∃ Γ : V → V → ℝ, (∀ a b, Γ a b = Γ b a) ∧ (∀ a, Γ a a = 0) ∧
      (∀ a b, a ≠ b → 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi) ∧
      (∀ a b, G.Adj a b → Γ a b = θ a b) ∧
      ∀ {a b : V × Bool} (p : (liftGraph (⊤ : SimpleGraph V)).Walk a b),
        a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight Γ) p := by
  classical
  let P : Set (SimpleGraph V) := {K | G ≤ K ∧ ∃ Γ : V → V → ℝ,
    (∀ a b, Γ a b = Γ b a) ∧ (∀ a, Γ a a = 0) ∧
    (∀ a b, K.Adj a b → 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi) ∧
    (∀ a b, G.Adj a b → Γ a b = θ a b) ∧
    ∀ {a b : V × Bool} (p : (liftGraph K).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight Γ) p}
  have hP : P.Nonempty := ⟨G,le_refl G,θ,hsym,hd,hθ,by intros; rfl,hclosed⟩
  obtain ⟨K,hK,hmax⟩ := P.toFinite.exists_maximal hP
  obtain ⟨hGK,Γ,hs,hdΓ,hbΓ,heΓ,hcΓ⟩ := hK
  have htop : K = ⊤ := by
    apply top_unique
    intro u v huv
    by_contra hn
    have hne : u ≠ v := huv
    obtain ⟨x,hx₀,hx₁,hx⟩ := extend_one K Γ hs hbΓ hcΓ hne hn
    have hle : K ≤ insertGraph K u v := fun _ _ h => Or.inl h
    have hpres (a b : V) (h : K.Adj a b) : insertAngle Γ u v x a b = Γ a b := by
      have hnot : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
        rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · exact hn h
        · exact hn h.symm
      simp only [insertAngle, ite_eq_right hnot]
    have hnew : insertGraph K u v ∈ P := by
      refine ⟨le_trans hGK hle, insertAngle Γ u v x, ?_, ?_, ?_, ?_, hx⟩
      · intro a b
        simp only [insertAngle]
        split_ifs <;> first | rfl | exact hs a b | tauto
      · intro a
        have hn : ¬ ((a = u ∧ a = v) ∨ (a = v ∧ a = u)) := by
          rintro (⟨ha,hb⟩ | ⟨hb,ha⟩) <;> exact hne (ha.symm.trans hb)
        simp only [insertAngle, ite_eq_right hn, hdΓ]
      · intro a b h
        rcases h with h | ⟨hh,hne'⟩
        · rw [hpres a b h]
          exact hbΓ a b h
        · simp only [insertAngle, ite_eq_left hh]
          exact ⟨hx₀,hx₁⟩
      · intro a b h
        exact (hpres a b (hGK h)).trans (heΓ a b h)
    have hback : insertGraph K u v ≤ K := hmax hnew hle
    exact hn (hback (Or.inr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩))
  subst K
  exact ⟨Γ,hs,hdΓ,hbΓ,heΓ,hcΓ⟩
theorem exists_joint_angle_table [Finite V] (G : SimpleGraph V) (θ : V → V → ℝ)
    (hsym : ∀ a b, θ a b = θ b a) (hd : ∀ a, θ a a = 0)
    (hθ : ∀ a b, G.Adj a b → 0 ≤ θ a b ∧ θ a b ≤ Real.pi)
    (hcycles : ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, θ (c i) (c (finRotate m i))) -
        (∑ i ∈ Finset.univ \ F, θ (c i) (c (finRotate m i))) ≤
          ((F.card : ℝ) - 1) * Real.pi) :
    ∃ Γ : V → V → ℝ, (∀ a b, Γ a b = Γ b a) ∧ (∀ a, Γ a a = 0) ∧
      (∀ a b, 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi) ∧
      (∀ a b, G.Adj a b → Γ a b = θ a b) ∧
      (∀ a b c, Γ a b ≤ Γ a c + Γ c b) ∧
      (∀ a b c, Γ a b + Γ b c + Γ c a ≤ 2 * Real.pi) := by
  have hc : ∀ {a b : V × Bool} (p : (liftGraph G).Walk a b),
      a.1 = b.1 → a.2 ≠ b.2 → Real.pi ≤ total (weight θ) p := odd_walk_reduction G θ hθ (fun p hab hbits hp =>
    elementary_cost G θ hsym hcycles p hab hbits hp)
  obtain ⟨Γ,hs,hdΓ,hb,he,hcl⟩ := complete_extension G θ hsym hd hθ hc
  have hb' (a b : V) : 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi := by
    by_cases h : a = b
    · subst b; simp [hdΓ,Real.pi_pos.le]
    · exact hb a b h
  have htri (a b c : V) : Γ a b ≤ Γ a c + Γ c b := by
    by_cases hab : a = b
    · subst b; rw [hdΓ]; linarith [(hb' a c).1,(hb' c a).1]
    by_cases hac : a = c
    · subst c; simp [hdΓ]
    by_cases hcb : c = b
    · subst c; simp [hdΓ]
    let p : (liftGraph (⊤ : SimpleGraph V)).Walk (a,false) (a,true) :=
      Walk.cons (u := (a,false)) (v := (c,false)) (show (⊤ : SimpleGraph V).Adj a c from hac)
        (Walk.cons (u := (c,false)) (v := (b,false)) (show (⊤ : SimpleGraph V).Adj c b from hcb)
          (Walk.cons (u := (b,false)) (v := (a,true)) (show (⊤ : SimpleGraph V).Adj b a from Ne.symm hab) Walk.nil))
    have hh := hcl p rfl (by change false ≠ true; decide)
    simp only [p,total_cons,total_nil,weight,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false] at hh
    rw [hs b a] at hh
    linarith
  refine ⟨Γ,hs,hdΓ,hb',he,htri,?_⟩
  intro a b c
  by_cases hab : a = b
  · subst b; rw [hdΓ]; linarith [(hb' a c).2,(hb' c a).2]
  by_cases hbc : b = c
  · subst c; rw [hdΓ]; linarith [(hb' a b).2,(hb' b a).2]
  by_cases hca : c = a
  · subst c; rw [hdΓ]; linarith [(hb' a b).2,(hb' b a).2]
  let p : (liftGraph (⊤ : SimpleGraph V)).Walk (a,false) (a,true) :=
    Walk.cons (u := (a,false)) (v := (b,true)) (show (⊤ : SimpleGraph V).Adj a b from hab)
      (Walk.cons (u := (b,true)) (v := (c,false)) (show (⊤ : SimpleGraph V).Adj b c from hbc)
        (Walk.cons (u := (c,false)) (v := (a,true)) (show (⊤ : SimpleGraph V).Adj c a from hca) Walk.nil))
  -- The signs alternate at every step, including the final edge.
  change (liftGraph (⊤ : SimpleGraph V)).Walk (a,false) (a,true) at p
  have hh := hcl p rfl (by change false ≠ true; decide)
  simp only [p,total_cons,total_nil,weight,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false] at hh
  linarith
private lemma triangle_constraints (Γ : V → V → ℝ)
    (hs : ∀ a b, Γ a b = Γ b a)
    (ht : ∀ a b c, Γ a b ≤ Γ a c + Γ c b)
    (hp : ∀ a b c, Γ a b + Γ b c + Γ c a ≤ 2 * Real.pi)
    (f : Fin 3 → V) : ∀ F : Finset (Fin 3), Odd F.card →
      (∑ i ∈ F, Γ (f i) (f (finRotate 3 i))) -
        (∑ i ∈ Finset.univ \ F, Γ (f i) (f (finRotate 3 i))) ≤
          ((F.card : ℝ) - 1) * Real.pi := by
  intro F hF
  have hcard := F.card_le_univ
  simp only [Fintype.card_fin] at hcard
  have hodd : F.card = 1 ∨ F.card = 3 := by obtain ⟨k,hk⟩ := hF; omega
  rcases hodd with h | h
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
    fin_cases i <;>
      norm_num [Fin.sum_univ_succ, Finset.sum_sdiff_eq_sub, finRotate_apply] <;>
      linarith [ht (f 0) (f 1) (f 2),ht (f 1) (f 2) (f 0),
        ht (f 2) (f 0) (f 1),hs (f 0) (f 1),hs (f 0) (f 2),hs (f 1) (f 2)]
  · have he : F = Finset.univ := Finset.eq_univ_of_card F (by simpa using h)
    subst F
    norm_num [Fin.sum_univ_succ, finRotate_apply]
    linarith [hp (f 0) (f 1) (f 2)]

private lemma small_psd {C : Type*} [Finite C] (Γ : C → C → ℝ)
    (hcard : Nat.card C ≤ 3)
    (hs : ∀ a b, Γ a b = Γ b a) (hd : ∀ a, Γ a a = 0)
    (hb : ∀ a b, 0 ≤ Γ a b ∧ Γ a b ≤ Real.pi)
    (ht : ∀ a b c, Γ a b ≤ Γ a c + Γ c b)
    (hp : ∀ a b c, Γ a b + Γ b c + Γ c a ≤ 2 * Real.pi) :
    Matrix.PosSemidef (Matrix.of (fun a b : C => Real.cos (Γ a b))) ∧
      Matrix.rank (Matrix.of (fun a b : C => Real.cos (Γ a b))) ≤ 3 := by
  classical
  letI := Fintype.ofFinite C
  have hcard' : Fintype.card C ≤ 3 := by simpa only [Nat.card_eq_fintype_card] using hcard
  refine ⟨?_, (Matrix.rank_le_card_width _).trans hcard'⟩
  cases isEmpty_or_nonempty C with
  | inl h =>
    letI := h
    have he : (Matrix.of (fun a b : C => Real.cos (Γ a b))) = 0 := by ext a; exact isEmptyElim a
    rw [he]
    exact Matrix.PosSemidef.zero
  | inr h =>
    letI := h
    let e : C ↪ Fin 3 := (Fintype.equivFin C).toEmbedding.trans (Fin.castLEEmb hcard')
    let f : Fin 3 → C := Function.invFun e
    have hfe : ∀ a, f (e a) = a := Function.leftInverse_invFun e.injective
    have hc := triangle_constraints Γ hs ht hp f
    have hc' : ∀ F : Finset (Fin 3), Odd F.card →
        (∑ i ∈ F, Real.arccos (Real.cos (Γ (f i) (f (finRotate 3 i))))) -
        (∑ i ∈ Finset.univ \ F, Real.arccos (Real.cos (Γ (f i) (f (finRotate 3 i))))) ≤
          ((F.card : ℝ) - 1) * Real.pi := by
      have hacc (a b : C) : Real.arccos (Real.cos (Γ a b)) = Γ a b := Real.arccos_cos (hb a b).1 (hb a b).2
      simpa only [hacc] using hc
    obtain ⟨B,hB,_,hdiag,hedge⟩ :=
      (D5.S3.QuadraticForms.CycleRankThreePsdCompletion.cycle_rank_three_iff (n := 3)
        (by omega) (fun i => Real.cos (Γ (f i) (f (finRotate 3 i))))
        (fun i => ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)).mpr hc'
    have hentry : ∀ i j : Fin 3, B i j = Real.cos (Γ (f i) (f j)) := by
      intro i j
      have hsym (i j : Fin 3) : B i j = B j i := by simpa using hB.isHermitian.apply j i
      have h00 (i : Fin 3) : B i i = Real.cos (Γ (f i) (f i)) := by rw [hdiag,hd,Real.cos_zero]
      have h01 : B 0 1 = Real.cos (Γ (f 0) (f 1)) := by
        simpa only [show finRotate 3 0 = 1 from rfl] using hedge 0
      have h12 : B 1 2 = Real.cos (Γ (f 1) (f 2)) := by
        simpa only [show finRotate 3 1 = 2 from rfl] using hedge 1
      have h20 : B 2 0 = Real.cos (Γ (f 2) (f 0)) := by
        simpa only [show finRotate 3 2 = 0 from rfl] using hedge 2
      fin_cases i <;> fin_cases j
      · exact h00 0
      · exact h01
      · exact (hsym 0 2).trans (h20.trans (congrArg Real.cos (hs (f 2) (f 0))))
      · exact (hsym 1 0).trans (h01.trans (congrArg Real.cos (hs (f 0) (f 1))))
      · exact h00 1
      · exact h12
      · exact h20
      · exact (hsym 2 1).trans (h12.trans (congrArg Real.cos (hs (f 1) (f 2))))
      · exact h00 2
    have heq : (Matrix.of (fun a b : C => Real.cos (Γ a b))) = B.submatrix e e := by
      ext a b
      simp only [Matrix.of_apply,Matrix.submatrix_apply,hentry,hfe]
    rw [heq]
    exact hB.submatrix e
set_option maxHeartbeats 800000 in
theorem partial_two_tree_rank_three_iff [Finite V] (G : SimpleGraph V)
    (hG : ∃ H : SimpleGraph V, G ≤ H ∧ H.IsChordal ∧
      ∀ C : Set V, H.IsClique C → Nat.card C ≤ 3)
    (A : Matrix V V ℝ) (hsym : ∀ i j, A i j = A j i)
    (hdiag : ∀ i, A i i = 1)
    (hbound : ∀ i j, G.Adj i j → -1 ≤ A i j ∧ A i j ≤ 1) :
    (∃ B : Matrix V V ℝ, B.PosSemidef ∧ B.rank ≤ 3 ∧
      (∀ i, B i i = 1) ∧ (∀ i j, G.Adj i j → B i j = A i j)) ↔
    ∀ (m : ℕ), 3 ≤ m → ∀ c : Fin m → V, Function.Injective c →
      (∀ i, G.Adj (c i) (c (finRotate m i))) →
      ∀ F : Finset (Fin m), Odd F.card →
      (∑ i ∈ F, Real.arccos (A (c i) (c (finRotate m i)))) -
        (∑ i ∈ Finset.univ \ F, Real.arccos (A (c i) (c (finRotate m i)))) ≤
          ((F.card : ℝ) - 1) * Real.pi := by
  classical
  letI := Fintype.ofFinite V
  constructor
  · rintro ⟨B,hB,hr,hd,he⟩ m hm c hc hadj
    apply (D5.S3.QuadraticForms.CycleRankThreePsdCompletion.cycle_rank_three_iff
      hm (fun i => A (c i) (c (finRotate m i))) (fun i => hbound _ _ (hadj i))).mp
    refine ⟨B.submatrix c c,hB.submatrix c, (B.rank_submatrix_le c c).trans hr,?_,?_⟩
    · intro i; exact hd (c i)
    · intro i; exact he _ _ (hadj i)
  · intro hcycles
    obtain ⟨Γ,hΓs,hΓd,hΓb,hΓe,hΓt,hΓp⟩ := exists_joint_angle_table G
      (fun i j => Real.arccos (A i j))
      (fun i j => congrArg Real.arccos (hsym i j))
      (fun i => by rw [hdiag,Real.arccos_one])
      (fun i j _ => ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩) hcycles
    obtain ⟨H,hGH,hH,hcard⟩ := hG
    let T : Matrix V V ℝ := fun i j => Real.cos (Γ i j)
    have hlocal (C : Set V) (hC : H.IsClique C) :
        (T.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).PosSemidef ∧
        (T.submatrix (Subtype.val : C → V) (Subtype.val : C → V)).rank ≤ 3 := by
      simpa only [T,Matrix.submatrix,Matrix.rank_eq_finrank_span_cols] using small_psd (fun i j : C => Γ i j) (hcard C hC)
        (fun i j => hΓs i j) (fun i => hΓd i) (fun i j => hΓb i j)
        (fun i j k => hΓt i j k) (fun i j k => hΓp i j k)
    obtain ⟨B,hB,hr,he⟩ :=
      D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le
        3 H hH T (fun C hC => by
          simpa only [Matrix.rank_eq_finrank_span_cols] using hlocal C hC)
    refine ⟨B,hB,hr,?_,?_⟩
    · intro i
      rw [he i i (Or.inl rfl)]
      simp only [T,hΓd,Real.cos_zero]
    · intro i j hij
      rw [he i j (Or.inr (hGH hij))]
      change Real.cos (Γ i j) = A i j
      rw [hΓe i j hij, Real.cos_arccos (hbound i j hij).1 (hbound i j hij).2]
end D5.S3.QuadraticForms.PartialTwoTreePsdCompletion
