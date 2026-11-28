import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeSpines

compile_only_with_mathlib

/-! Omega original.

Cochain tests supported by prescribed copy choices attenuate under the stabilizer
of a path residual. Each copy layer contributes one factor to the attenuation.
-/

namespace Omega.PureThreeTree
open SimpleGraph Omega.GraphChains Omega.RollingCliques Finset
open scoped BigOperators
noncomputable section

variable {n k : ℕ}
local notation "V" => Vertex n k
local notation "B" => (triangleChain (G := graph n k))
local notation "D" => Fin (n + 1)
local notation "K" => Fin (k + 1)

def stage (v : V) : D := v.val.1.stage

private def later (x y : V) : V := if stage x ≤ stage y then y else x

private theorem stage_le_later_left (x y : V) : stage x ≤ stage (later x y) := by
  unfold later
  split
  · assumption
  · rfl

private theorem stage_le_later_right (x y : V) : stage y ≤ stage (later x y) := by
  unfold later
  split
  · rfl
  · exact le_of_not_ge ‹_›

private theorem stage_clone (i : D) (hi : i ≠ 0) (p : Equiv.Perm K) (v : V) :
    stage (clone i hi p v) = stage v := rfl

private theorem clone_later (i : D) (hi : i ≠ 0) (p : Equiv.Perm K) (x y : V) :
    clone i hi p (later x y) = later (clone i hi p x) (clone i hi p y) := by
  by_cases h : stage x ≤ stage y <;> simp [later, stage_clone, h]

private def branch (s : Finset D) (a : D → K) (v : V) : Prop :=
  ∀ i ∈ s, i ≤ stage v ∧ (v.val.1.step i).2 = a i

private theorem branch_insert_clone {s : Finset D} (a : D → K) {i : D} (hi : i ≠ 0)
    (his : i ∉ s) (b : K) (v : V) :
    branch (insert i s) a (clone i hi (Equiv.swap (a i) b) v) ↔
      (i ≤ stage v ∧ (v.val.1.step i).2 = b) ∧ branch s a v := by
  simp only [branch, Finset.forall_mem_insert]
  have hold (j : D) (hj : j ∈ s) :
      (clone i hi (Equiv.swap (a i) b) v).val.1.step j = v.val.1.step j := by
    have hne : j ≠ i := fun e => his (e ▸ hj)
    change (v.val.1.reclone i hi _).step j = _
    simp [History.reclone, hne]
  have hnew : i ≤ stage v →
      ((clone i hi (Equiv.swap (a i) b) v).val.1.step i).2 =
        Equiv.swap (a i) b (v.val.1.step i).2 := by
    intro hiv
    change ((v.val.1.reclone i hi _).step i).2 = _
    have hiv' : i ≤ v.val.1.stage := hiv
    simp [History.reclone, hiv']
  have swap_cancel (x : K) : Equiv.swap (a i) b x = a i ↔ x = b := by
    have he := Equiv.swap_apply_right (a i) b
    calc
      _ ↔ Equiv.swap (a i) b x = Equiv.swap (a i) b b := by rw [he]
      _ ↔ _ := (Equiv.swap (a i) b).injective.eq_iff
  constructor
  · rintro ⟨⟨hix, hix'⟩, hx⟩
    rw [hnew hix, swap_cancel] at hix'
    exact ⟨⟨hix, hix'⟩, fun j hj => by simpa only [stage_clone, hold j hj] using hx j hj⟩
  · rintro ⟨⟨hix, hix'⟩, hx⟩
    refine ⟨⟨hix, ?_⟩, fun j hj => ?_⟩
    · rw [hnew hix, swap_cancel, hix']
    · simpa only [stage_clone, hold j hj] using hx j hj

private def triangleMap (i : D) (hi : i ≠ 0) (p : Equiv.Perm K)
    (t : Triangles (graph n k)) : Triangles (graph n k) :=
  ⟨(clone i hi p t.1.1, clone i hi p t.1.2.1, clone i hi p t.1.2.2),
    (clone_adj i hi p ..).2 t.2.1, (clone_adj i hi p ..).2 t.2.2.1,
    (clone_adj i hi p ..).2 t.2.2.2⟩

private def triangleAnchor (t : Triangles (graph n k)) : V := later t.1.1 (later t.1.2.1 t.1.2.2)

private theorem triangleAnchor_map (i : D) (hi : i ≠ 0) (p : Equiv.Perm K) (t : Triangles (graph n k)) :
    triangleAnchor (triangleMap i hi p t) = clone i hi p (triangleAnchor t) := by
  simp only [triangleAnchor, triangleMap]
  rw [← clone_later, ← clone_later]

private theorem push_triangle (i : D) (hi : i ≠ 0) (p : Equiv.Perm K) (t : Triangles (graph n k)) :
    pushChain (clone i hi p) (B t) = B (triangleMap i hi p t) := by
  simp only [triangleChain, pushChain_sub, pushChain_add, pushChain_edge, triangleMap]

private structure Masked (s : Finset D) (a : D → K) (L : ℝ) (f : Chains V) : Prop where
  coordinate : ∀ x y, |f (x,y)| ≤ 3 * L
  edge_support : ∀ x y, ¬(graph n k).Adj x y ∨ ¬branch s a (later x y) → f (x,y) = 0
  triangle : ∀ t, |pairing f (B t)| ≤ L
  triangle_support : ∀ t, ¬branch s a (triangleAnchor t) → pairing f (B t) = 0

private def sumPull (i : D) (hi : i ≠ 0) (a : D → K) (f : Chains V) : Chains V :=
  fun e => ∑ b : K, pullCochain (clone i hi (Equiv.swap (a i) b)) f e

private theorem pairing_sumPull (i : D) (hi : i ≠ 0) (a : D → K)
    (f z : Chains V) :
    pairing (sumPull i hi a f) z =
      ∑ b : K, pairing (pullCochain (clone i hi (Equiv.swap (a i) b)) f) z := by
  simp only [pairing, sumPull, Finset.sum_mul]
  exact Finset.sum_comm

private theorem sum_abs_le_of_unique {α : Type*} [Fintype α] [DecidableEq α]
    (u : α → ℝ) (b : α) (h : ∀ c, c ≠ b → u c = 0) (M : ℝ)
    (hM : |u b| ≤ M) : |∑ c, u c| ≤ M := by
  rw [Finset.sum_eq_single b (fun c _ hne => h c hne) (by simp)]
  exact hM

private theorem Masked.sumPull {s : Finset D} {a : D → K} {L : ℝ} {f : Chains V}
    {i : D} (hi : i ≠ 0) (his : i ∉ s) (hf : Masked (insert i s) a L f) :
    Masked s a L (sumPull i hi a f) := by
  let σ (b : K) := clone i hi (Equiv.swap (a i) b)
  have hbc (b : K) (v : V) : branch (insert i s) a (σ b v) ↔
      (i ≤ stage v ∧ (v.val.1.step i).2 = b) ∧ branch s a v :=
    branch_insert_clone a hi his b v
  have he (x y : V) (b : K) (h : ¬(graph n k).Adj x y ∨
      ¬((i ≤ stage (later x y) ∧ ((later x y).val.1.step i).2 = b) ∧
        branch s a (later x y))) :
      f (σ b x, σ b y) = 0 := by
    apply hf.edge_support
    rw [← clone_later, hbc, clone_adj]
    exact h
  have ht (t : Triangles (graph n k)) (b : K) (h :
      ¬((i ≤ stage (triangleAnchor t) ∧ ((triangleAnchor t).val.1.step i).2 = b) ∧
        branch s a (triangleAnchor t))) :
      pairing f (B (triangleMap i hi (Equiv.swap (a i) b) t)) = 0 := by
    apply hf.triangle_support
    rwa [triangleAnchor_map, hbc]
  refine ⟨fun x y => ?_, fun x y h => ?_, fun t => ?_, fun t h => ?_⟩
  · change |∑ b : K, f (σ b x, σ b y)| ≤ 3 * L
    apply sum_abs_le_of_unique _ ((later x y).val.1.step i).2
    · intro b hne
      exact he x y b (Or.inr fun h => hne h.1.2.symm)
    · exact hf.coordinate _ _
  · change (∑ b : K, f (σ b x, σ b y)) = 0
    apply Finset.sum_eq_zero
    intro b _
    exact he x y b (h.imp id (fun hs h' => hs h'.2))
  · rw [pairing_sumPull]
    simp_rw [← pairing_pushChain, push_triangle]
    apply sum_abs_le_of_unique _ ((triangleAnchor t).val.1.step i).2
    · exact fun b hne => ht t b (fun h => hne h.1.2.symm)
    · exact hf.triangle _
  · rw [pairing_sumPull]
    simp_rw [← pairing_pushChain, push_triangle]
    exact Finset.sum_eq_zero (fun b _ => ht t b (fun hb => h hb.2))

private theorem pairing_invariant {z f : Chains V} (σ : Equiv.Perm V)
    (hz : ∀ x y, z (σ x, σ y) = z (x,y)) :
    pairing (pullCochain σ f) z = pairing f z := by
  unfold pairing
  rw [← Equiv.sum_comp (σ.prodCongr σ) (fun e => f e * z e)]
  exact Finset.sum_congr rfl (fun e _ => by
    rcases e with ⟨x,y⟩
    simp [Equiv.prodCongr_apply, pullCochain, hz])

private theorem remove_mask (s : Finset D) (a : D → K) (L : ℝ)
    (z f : Chains V) (hf : Masked s a L f)
    (hroot : ∀ i ∈ s, i ≠ 0)
    (hinv : ∀ (i : D) (hi : i ≠ 0), i ∈ s → ∀ (p : Equiv.Perm K) (x y : V),
      z (clone i hi p x, clone i hi p y) = z (x,y)) :
    ∃ g : Chains V, Masked ∅ a L g ∧ pairing g z = (k + 1 : ℝ) ^ s.card * pairing f z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | @insert i s his ih =>
    let hi := hroot i (Finset.mem_insert_self _ _)
    let f' := sumPull i hi a f
    have hf' := hf.sumPull hi his
    obtain ⟨g, hg, hp⟩ := ih f' hf'
      (fun j hj => hroot j (Finset.mem_insert_of_mem hj))
      (fun j hj hmem => hinv j hj (Finset.mem_insert_of_mem hmem))
    have he : pairing f' z = (k + 1 : ℝ) * pairing f z := by
      unfold f'
      rw [pairing_sumPull]
      simp_rw [pairing_invariant _ (hinv i hi (Finset.mem_insert_self _ _) _)]
      simp
    exact ⟨g, hg, by rw [hp, he, Finset.card_insert_of_notMem his, pow_succ, mul_assoc]⟩

private theorem supported_orientedEdge {x y : V} (h : (graph n k).Adj x y) :
    Supported (graph n k) (orientedEdge x y) := by
  intro e he
  have h₁ : e ≠ (x,y) := fun q => he (q ▸ h)
  have h₂ : e ≠ (y,x) := fun q => he (q ▸ h.symm)
  simp [orientedEdge, h₁, h₂]

private theorem supported_triangle (t : Triangles (graph n k)) : Supported (graph n k) (B t) := by
  intro e he
  simp [triangleChain, supported_orientedEdge t.2.1 e he,
    supported_orientedEdge t.2.2.1 e he, supported_orientedEdge t.2.2.2 e he]

private theorem pairing_agrees {z f g : Chains V} (hz : Supported (graph n k) z)
    (hfg : ∀ x y, (graph n k).Adj x y → f (x,y) = g (x,y)) :
    pairing f z = pairing g z := by
  unfold pairing
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ _
  by_cases h : (graph n k).Adj x y
  · rw [hfg x y h]
  · rw [hz (x,y) h, mul_zero, mul_zero]

private theorem branch_ancestor {s : Finset D} {a : D → K} {x y : V} (h : pre x y)
    (hx : branch s a x) : branch s a y :=
  fun i hi => ⟨(hx i hi).1.trans h.1, by rw [← h.2 i (hx i hi).1]; exact (hx i hi).2⟩

private theorem pre_later_left {x y : V} (h : (graph n k).Adj x y) : pre x (later x y) := by
  unfold later
  split
  · exact (rolling_earlier data h ‹_›).1
  · exact data.refl _

private theorem pre_later_right {x y : V} (h : (graph n k).Adj x y) : pre y (later x y) := by
  unfold later
  split
  · exact data.refl _
  · exact (rolling_earlier data h.symm (le_of_not_ge ‹_›)).1

private theorem later_adj {x y z : V} (hxy : (graph n k).Adj x y) (hxz : (graph n k).Adj x z) :
    (graph n k).Adj x (later y z) := by
  unfold later
  split <;> assumption

private theorem mask_retract_change (u v : V) (s : Finset D) (a : D → K)
    (hstay : ∀ x : V, ¬branch s a x → retract u.val.1 x = retract v.val.1 x)
    (f : Chains V) (hf : Admissible B f) :
    ∃ f' : Chains V, Masked s a 2 f' ∧
      ∀ z, Supported (graph n k) z → pairing f' z =
        pairing f (pushChain (retract u.val.1) z - pushChain (retract v.val.1) z) := by
  classical
  let A := pullCochain (retract u.val.1) f
  let C := pullCochain (retract v.val.1) f
  let f' (e : V × V) := if (graph n k).Adj e.1 e.2 then A e - C e else 0
  have hc (x y : V) (h : (graph n k).Adj x y) : f' (x,y) = (A - C) (x,y) := by simp [f', h]
  have he (z : Chains V) (hz : Supported (graph n k) z) : pairing f' z =
      pairing f (pushChain (retract u.val.1) z - pushChain (retract v.val.1) z) := by
    rw [pairing_agrees hz hc, pairing_sub, ← pairing_pushChain, ← pairing_pushChain,
      pairing_chain_sub]
  have edge_vanish (x y : V) (hx : ¬branch s a x) (hy : ¬branch s a y) : f' (x,y) = 0 := by
    simp [f', A, C, pullCochain, hstay _ hx, hstay _ hy]
  refine ⟨f', ⟨?_, ?_, ?_, ?_⟩, he⟩
  · intro x y
    dsimp [f']
    split
    · have ha := hf.1 (retract u.val.1 x, retract u.val.1 y)
      have hc := hf.1 (retract v.val.1 x, retract v.val.1 y)
      exact (abs_sub _ _).trans (by dsimp [A, C, pullCochain]; linarith)
    · norm_num
  · rintro x y (hna | hb)
    · simp [f', hna]
    · by_cases ha : (graph n k).Adj x y
      · exact edge_vanish x y (fun h => hb (branch_ancestor (pre_later_left ha) h))
          (fun h => hb (branch_ancestor (pre_later_right ha) h))
      · simp [f', ha]
  · intro t
    rw [he _ (supported_triangle t), pairing_chain_sub]
    refine (abs_sub _ _).trans ?_
    have h₁ := (abs_pairing_le_dualNorm hf (pushChain (retract u.val.1) (B t))).trans
      ((dualNorm_pushChain_le (retract u.val.1) (fun _ _ => retract_edge u.val.1) _).trans
        (dualNorm_triangle B t))
    have h₂ := (abs_pairing_le_dualNorm hf (pushChain (retract v.val.1) (B t))).trans
      ((dualNorm_pushChain_le (retract v.val.1) (fun _ _ => retract_edge v.val.1) _).trans
        (dualNorm_triangle B t))
    linarith
  · intro t ht
    let x := t.1.1
    let y := t.1.2.1
    let z := t.1.2.2
    let h := later_adj t.2.1 t.2.2.2
    have hx : ¬branch s a x := fun hb => ht (branch_ancestor (pre_later_left h) hb)
    have hy : ¬branch s a y := fun hb => ht (branch_ancestor
      (data.trans (pre_later_left t.2.2.1) (pre_later_right h)) hb)
    have hz : ¬branch s a z := fun hb => ht (branch_ancestor
      (data.trans (pre_later_right t.2.2.1) (pre_later_right h)) hb)
    rw [triangleChain, pairing_triangle_alternating]
    change ((f' (x,y) - f' (y,x)) + (f' (y,z) - f' (z,y)) -
      (f' (x,z) - f' (z,x))) / 2 = 0
    simp [edge_vanish _ _ hx hy, edge_vanish _ _ hy hx, edge_vanish _ _ hy hz,
      edge_vanish _ _ hz hy, edge_vanish _ _ hx hz, edge_vanish _ _ hz hx]

/-- If the residual is invariant under recloning at the selected depths, the
difference of two spine retractions costs at most twice its norm, divided by
the number of possible copy strings at those depths. -/
theorem retract_change_le (u v : V) (huv : pre u v) (hstage : stage u < stage v)
    (z : Chains V) (hz : Supported (graph n k) z) (s : Finset D)
    (hs : ∀ j ∈ s, j.val ≤ (stage u).val + 1)
    (hroot : ∀ j ∈ s, j ≠ 0)
    (hinv : ∀ (j : D) (hj : j ≠ 0), j ∈ s → ∀ (p : Equiv.Perm K) (x y : V),
      z (clone j hj p x, clone j hj p y) = z (x,y)) :
    dualNorm B (pushChain (retract u.val.1) z - pushChain (retract v.val.1) z) ≤
      2 * dualNorm B z / (k + 1 : ℝ) ^ s.card := by
  classical
  let i : D := ⟨(stage u).val + 1, (Nat.succ_le_of_lt hstage).trans_lt (stage v).isLt⟩
  have hi : i ≤ stage v := Nat.succ_le_of_lt hstage
  let a (j : D) := (v.val.1.step j).2
  have hstay (x : V) (hx : ¬branch s a x) : retract u.val.1 x = retract v.val.1 x := by
    apply Subtype.ext
    apply spineMap_stable huv i rfl hi x.val
    intro hpre
    apply hx
    intro j hj
    have hji : j ≤ i := hs j hj
    exact ⟨hji.trans hpre.1, by
      have he := congrArg Prod.snd (hpre.2 j hji)
      simpa only [a, History.prefix, ite_eq_left hji] using he.symm⟩
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨f', hm, he⟩ := mask_retract_change u v s a hstay f hf
  obtain ⟨g, hg, hgz⟩ := remove_mask s a 2 z f' hm hroot hinv
  have hscale (x : Chains V) : pairing ((1 / 2 : ℝ) • g) x = (1 / 2) * pairing g x := by
    simp [pairing, Finset.mul_sum, mul_assoc]
  have had : Admissible B ((1 / 2 : ℝ) • g) := by
    refine ⟨fun e => ?_, fun t => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith [hg.coordinate e.1 e.2]
    · rw [hscale, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith [hg.triangle t]
  have hb := abs_pairing_le_dualNorm had z
  rw [hscale, hgz, he _ hz, abs_mul, abs_mul] at hb
  have hp : 0 < (k + 1 : ℝ) ^ s.card := by positivity
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_pos hp] at hb
  apply (le_div_iff₀ hp).2
  linarith

end
end Omega.PureThreeTree
