/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/WeightedTwoStepBFS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary predecessor laws obey the four-defect weighted BFS bound. -/

import D5.S3.Combinatorics.Graph.Chordal.CliqueBoundedBanachPotential

/-! # The weighted two-step BFS potential -/

namespace SimpleGraph

open CliqueBoundedBanach (predecessors diagonal_zero)
open scoped BigOperators

noncomputable section

variable {V : Type*}

abbrev bfsPred [Fintype V] (G : SimpleGraph V) (o u : V) : Finset V :=
  @predecessors V G o u _ (Classical.decPred _)

private theorem mem_bfsPred [Fintype V] {G : SimpleGraph V} {o b u : V} :
    b ∈ bfsPred G o u ↔ G.Adj b u ∧ G.dist o b + 1 = G.dist o u := by
  classical
  simp [bfsPred, predecessors]

/-- A skew gain with triangle defect bounded by one. -/
def IsTriangleOneGain (G : SimpleGraph V) (g : V → V → ℝ) : Prop :=
  (∀ a b, g b a = -g a b) ∧ ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
    |g a b + g b c - g a c| ≤ 1

/-- Common predecessors chosen in the parent shadows, with the root at depth one. -/
def ValidShadowAnchors (G : SimpleGraph V) (o : V)
    (a : (k : ℕ) → Component G o (k + 1) → V) : Prop :=
  (∀ C, a 0 C = o) ∧ ∀ k (C : Component G o (k + 2)),
    a (k + 1) C ∈ Shadow G o (parent G o C) ∧
    ∀ b ∈ Shadow G o C, G.Adj (a (k + 1) C) b

/-- Each nonroot vertex carries a probability distribution on its predecessors. -/
def ValidPredecessorWeights [Fintype V] (G : SimpleGraph V) (o : V) (w : V → V → ℝ) : Prop :=
  (∀ u b, 0 ≤ w u b) ∧ (∀ u b, b ∉ bfsPred G o u → w u b = 0) ∧
    ∀ u ≠ o, ∑ b ∈ bfsPred G o u, w u b = 1

abbrev transport {G : SimpleGraph V} {o : V} (g : V → V → ℝ)
    (a : (k : ℕ) → Component G o (k + 1) → V)
    (k : ℕ) (C : Component G o (k + 1)) : ℝ :=
  (anchorGain (fun x y => Multiplicative.ofAdd (g x y)) a k C).toAdd

private theorem transport_succ {G : SimpleGraph V} {o : V} {g : V → V → ℝ}
    {a : (k : ℕ) → Component G o (k + 1) → V} (k : ℕ) (C : Component G o (k + 2)) :
    transport g a (k + 1) C =
      transport g a k (parent G o C) + g (a k (parent G o C)) (a (k + 1) C) := rfl

def potentialAt [Fintype V] (G : SimpleGraph V) (o : V)
    (a : (k : ℕ) → Component G o (k + 1) → V) (w g : V → V → ℝ) (u : V) :
    (d : ℕ) → G.dist o u = d → ℝ
  | 0, _ => 0
  | k + 1, h =>
    let C := componentOf G o (k + 1) u h.ge
    transport g a k C + ∑ b ∈ bfsPred G o u, w u b * (g (a k C) b + g b u)

/-- Transport along the anchors and average the two-edge paths through the predecessors. -/
def twoStepBFSPotential [Fintype V] (G : SimpleGraph V) (o : V)
    (a : (k : ℕ) → Component G o (k + 1) → V)
    (w g : V → V → ℝ) (u : V) : ℝ := potentialAt G o a w g u (G.dist o u) rfl

private theorem potential_at [Fintype V] {G : SimpleGraph V} {o u : V}
    {a : (k : ℕ) → Component G o (k + 1) → V} {w g : V → V → ℝ} {d : ℕ}
    (h : G.dist o u = d) : twoStepBFSPotential G o a w g u = potentialAt G o a w g u d h := by
  subst d
  rfl

private theorem potential_eval [Fintype V] {G : SimpleGraph V} {o u : V} {k : ℕ}
    {a : (k : ℕ) → Component G o (k + 1) → V} {w g : V → V → ℝ}
    (h : G.dist o u = k + 1) :
    let C := componentOf G o (k + 1) u h.ge
    twoStepBFSPotential G o a w g u =
      transport g a k C + ∑ b ∈ bfsPred G o u, w u b * (g (a k C) b + g b u) :=
  potential_at h

private theorem average_interval {s : Finset V} {w f : V → ℝ} {l h : ℝ}
    (hw : ∀ b ∈ s, 0 ≤ w b) (hs : ∑ b ∈ s, w b = 1)
    (hf : ∀ b ∈ s, l ≤ f b ∧ f b ≤ h) :
    l ≤ ∑ b ∈ s, w b * f b ∧ ∑ b ∈ s, w b * f b ≤ h := by
  constructor
  · calc
      l = ∑ b ∈ s, w b * l := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hf b hb).1 (hw b hb)
  · calc
      _ ≤ ∑ b ∈ s, w b * h :=
        Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hf b hb).2 (hw b hb)
      _ = h := by rw [← Finset.sum_mul, hs, one_mul]

private theorem triangle_near {G : SimpleGraph V} {g : V → V → ℝ}
    (hg : IsTriangleOneGain G g) {a b c : V}
    (hab : a = b ∨ G.Adj a b) (hbc : b = c ∨ G.Adj b c) (hac : a = c ∨ G.Adj a c) :
    |g a b + g b c - g a c| ≤ 1 := by
  rcases hab with rfl | hab
  · simp [diagonal_zero hg.1]
  rcases hbc with rfl | hbc
  · simp [diagonal_zero hg.1]
  rcases hac with rfl | hac
  · simp [diagonal_zero hg.1, hg.1 a b]
  exact hg.2 a b c hab hbc hac

private theorem weighted_difference_bound {sx sy : Finset V} {w v f h : V → ℝ}
    {c B : ℝ} (hw : ∀ b ∈ sx, 0 ≤ w b) (hv : ∀ b ∈ sy, 0 ≤ v b)
    (sw : ∑ b ∈ sx, w b = 1) (sv : ∑ b ∈ sy, v b = 1)
    (hf : ∀ b ∈ sx, ∀ t ∈ sy, |c + f b - h t| ≤ B) :
    |c + (∑ b ∈ sx, w b * f b) - ∑ t ∈ sy, v t * h t| ≤ B := by
  let y := ∑ t ∈ sy, v t * h t
  have inner (b : V) (hb : b ∈ sx) : -B ≤ c + f b - y ∧ c + f b - y ≤ B := by
    have hsum : ∑ t ∈ sy, v t * (c + f b - h t) = c + f b - y := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sv, one_mul, y]
    rw [← hsum]
    exact average_interval hv sv fun t ht => abs_le.mp (hf b hb t ht)
  have hsum : ∑ b ∈ sx, w b * (c + f b - y) = c + (∑ b ∈ sx, w b * f b) - y := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, sw, one_mul]
  rw [← hsum, abs_le]
  exact average_interval hw sw inner

/-- In a connected chordal graph the weighted two-step potential has residual at most four. -/
theorem two_step_residual_bound [Fintype V] {G : SimpleGraph V} (hG : G.IsChordal)
    (hconn : G.Connected) {r : V} {a : (l : ℕ) → Component G r (l + 1) → V}
    {w g : V → V → ℝ} (ha : ValidShadowAnchors G r a) (hw : ValidPredecessorWeights G r w)
    (hg : IsTriangleOneGain G g) {u v : V} (huv : G.Adj u v) :
    |g u v - (twoStepBFSPotential G r a w g v - twoStepBFSPotential G r a w g u)| ≤ 4 := by
  let φ := twoStepBFSPotential G r a w g
  have nz {x : V} {k : ℕ} (h : G.dist r x = k + 1) : x ≠ r :=
    fun he => by subst x; simpa using h
  have eval {x : V} {k : ℕ} (h : G.dist r x = k + 1) :
      let C := componentOf G r (k + 1) x h.ge
      φ x = transport g a k C + ∑ b ∈ bfsPred G r x, w x b * (g (a k C) b + g b x) :=
    potential_eval h
  have near {k : ℕ} {C : Component G r (k + 1)} {b : V} (hb : b ∈ Shadow G r C) :
      a k C = b ∨ G.Adj (a k C) b := by
    cases k with
    | zero => exact Or.inl ((ha.1 C).trans (hconn.dist_eq_zero_iff.mp hb.1))
    | succ k => exact Or.inr ((ha.2 k C).2 b hb)
  have nearShadow {k : ℕ} {C : Component G r (k + 1)} {b t : V}
      (hb : b ∈ Shadow G r C) (ht : t ∈ Shadow G r C) : b = t ∨ G.Adj b t :=
    (eq_or_ne b t).imp_right (shadow_clique hG hconn C hb ht)
  have predecessor {x b : V} {k : ℕ} (hx : G.dist r x = k + 1) (hb : b ∈ bfsPred G r x) :
      G.Adj b x ∧ b ∈ Shadow G r (componentOf G r (k + 1) x hx.ge) := by
    obtain ⟨hb, hd⟩ := mem_bfsPred.mp hb
    exact ⟨hb, mem_shadow_of_adj (by omega) hx.ge hb⟩
  have forward {x y : V} (hxy : G.Adj x y) (hle : G.dist r x ≤ G.dist r y) :
      |g x y - (φ y - φ x)| ≤ 4 := by
    cases hx : G.dist r x with
    | zero =>
      have hr := hconn.dist_eq_zero_iff.mp hx
      subst x
      have hy := dist_eq_one_iff_adj.mpr hxy
      have hp : bfsPred G r y = {r} := by
        classical
        ext b
        simp only [mem_bfsPred, hy, Nat.add_eq_right, hconn.dist_eq_zero_iff, Finset.mem_singleton]
        refine ⟨fun h => h.2.symm, fun hb => ?_⟩
        subst b
        exact ⟨hxy, rfl⟩
      have hs := hw.2.2 y hxy.ne.symm
      rw [hp, Finset.sum_singleton] at hs
      rw [show φ r = 0 from potential_at hx, eval hy, hp, Finset.sum_singleton, ha.1, hs,
        diagonal_zero hg.1]
      change |g r y - ((0 : ℝ) + 1 * (0 + g r y) - 0)| ≤ 4
      simp
    | succ k =>
      have hd := hxy.diff_dist_adj (u := r)
      have hy : G.dist r y = k + 1 ∨ G.dist r y = k + 2 := by omega
      let C := componentOf G r (k + 1) x hx.ge
      let d := a k C
      let f := fun b => g d b + g b x
      have sw := hw.2.2 x (nz hx)
      rcases hy with hy | hy
      · let D := componentOf G r (k + 1) y hy.ge
        have he : C = D := componentOf_adj hx.ge hy.ge hxy
        rw [eval hx, eval hy]
        change |g x y - ((transport g a k D +
            ∑ t ∈ bfsPred G r y, w y t * (g (a k D) t + g t y)) -
          (transport g a k C + ∑ b ∈ bfsPred G r x, w x b * f b))| ≤ 4
        rw [← he]
        have hb := weighted_difference_bound (fun b _ => hw.1 x b) (fun b _ => hw.1 y b)
          sw (hw.2.2 y (nz hy)) (c := g x y) (B := 4)
          (f := f) (h := fun t => g d t + g t y) (by
            intro b hb t ht
            obtain ⟨hbx, hbs⟩ := predecessor hx hb
            obtain ⟨hty, hts⟩ := predecessor hy ht
            change t ∈ Shadow G r D at hts
            rw [← he] at hts
            have hbt := nearShadow hbs hts
            have shared : G.Adj b y ∨ G.Adj t x := by
              rcases hbt with rfl | hb'
              · exact Or.inl hty
              · exact four_cycle_diagonal hG hbx hxy hty.symm hb'.symm
                  (fun e => by rw [e] at hbs; have := hbs.1; omega)
                  (fun e => by rw [← e] at hts; have := hts.1; omega) |>.elim Or.inl
                    (fun h => Or.inr h.symm)
            have h₀ := abs_le.mp (triangle_near hg (near hbs) hbt (near hts))
            rw [abs_le]
            rcases shared with hb' | ht'
            · have h₁ := abs_le.mp (hg.2 b x y hbx hxy hb')
              have h₂ := abs_le.mp (triangle_near hg hbt (Or.inr hty) (Or.inr hb'))
              dsimp [f]
              constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]
            · have h₁ := abs_le.mp (hg.2 t x y ht' hxy hty)
              have h₂ := abs_le.mp (triangle_near hg hbt (Or.inr ht') (Or.inr hbx))
              dsimp [f]
              constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2])
        convert hb using 1 <;> dsimp [C, D, d, f] <;> ring
      · let D := componentOf G r (k + 2) y hy.ge
        have hxS : x ∈ Shadow G r D := mem_shadow_of_adj hx hy.ge hxy
        have hp : parent G r D = C := shadow_parent hxS
        let c := a (k + 1) D
        have hcs : c ∈ Shadow G r C := hp ▸ (ha.2 k D).1
        have hcx := (ha.2 k D).2 x hxS
        rw [eval hx, eval hy, transport_succ, hp]
        have hb := weighted_difference_bound (fun b _ => hw.1 x b) (fun b _ => hw.1 y b)
          sw (hw.2.2 y (nz hy)) (c := g x y - g d c) (B := 4)
          (f := f) (h := fun t => g c t + g t y) (by
            intro b hb t ht
            obtain ⟨hbx, hbs⟩ := predecessor hx hb
            obtain ⟨hty, hts⟩ := predecessor hy ht
            have h₀ := abs_le.mp (triangle_near hg (near hbs) (nearShadow hbs hcs) (near hcs))
            have h₁ := abs_le.mp (triangle_near hg (nearShadow hbs hcs) (Or.inr hcx) (Or.inr hbx))
            have h₂ := abs_le.mp (triangle_near hg (Or.inr hcx) (nearShadow hxS hts) (near hts))
            have h₃ := abs_le.mp (triangle_near hg (nearShadow hxS hts) (Or.inr hty) (Or.inr hxy))
            rw [abs_le]
            dsimp [f]
            constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2])
        convert hb using 1 <;> dsimp [C, D, c, d, f] <;> ring
  change |g u v - (φ v - φ u)| ≤ 4
  rcases le_total (G.dist r u) (G.dist r v) with h | h
  · exact forward huv h
  · have h' := forward huv.symm h
    rw [hg.1 u v, show -g u v - (φ u - φ v) = -(g u v - (φ v - φ u)) by ring, abs_neg] at h'
    exact h'




end
end SimpleGraph
