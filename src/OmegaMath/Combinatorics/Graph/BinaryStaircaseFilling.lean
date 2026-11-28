import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.StaircaseSlab

compile_only_with_mathlib

/-! Omega original.

The three-branching-level binary staircase on five labels. Internal clique
triangles and the two oriented triangle classes of each slab give coordinates
for the full boundary map. Lane circulations are parametrized by their terminal
demands. The edge weights and filling costs are scaled by 200.
-/

namespace FiveLaneRouting.BinaryStaircase

open Finset
open scoped BigOperators
noncomputable section

abbrev Block := Fin 15
abbrev Slab := Fin 14
abbrev Leaf := Fin 8

def parent (s : Slab) : Block := ⟨s.val / 2, by omega⟩
def child (s : Slab) : Block := ⟨s.val + 1, by omega⟩
def leaf (t : Leaf) : Block := ⟨7 + t.val, by omega⟩

abbrev Site := Unit ⊕ (Leaf ⊕ (Slab ⊕ Slab))

def startSite : Site := Sum.inl ()
def endSite (t : Leaf) : Site := Sum.inr (Sum.inl t)
def oldSite (s : Slab) : Site := Sum.inr (Sum.inr (Sum.inl s))
def newSite (s : Slab) : Site := Sum.inr (Sum.inr (Sum.inr s))

def pathContains (b : Block) (t : Leaf) : Bool :=
  decide (b.val = 0 ∨ b.val = 1 + t.val / 4 ∨ b.val = 3 + t.val / 2 ∨ b = leaf t)

def below (a : Site) (t : Leaf) : Bool :=
  match a with
  | .inl _ => true
  | .inr (.inl t') => decide (t' = t)
  | .inr (.inr (.inl s)) => pathContains (child s) t
  | .inr (.inr (.inr s)) => pathContains (child s) t

def aggregate {A : Type*} [AddCommMonoid A] (f : Leaf → A) (a : Site) : A :=
  ∑ t ∈ univ.filter (fun t => below a t), f t

def multiplicity (a : Site) : ℕ := aggregate (fun _ => 1) a

private theorem multiplicity_pos_nat (a : Site) : 0 < multiplicity a := by
  revert a
  decide

private theorem multiplicity_pos (a : Site) : (0 : ℝ) < multiplicity a :=
  Nat.cast_pos.mpr (multiplicity_pos_nat a)

private theorem multiplicity_sum : ∑ a : Site, (multiplicity a : ℝ) = 64 := by
  exact_mod_cast (show ∑ a : Site, multiplicity a = 64 by decide)

def entering (b : Block) (a : Site) : Bool :=
  match a with
  | .inl _ => decide (b = 0)
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr s)) => decide (child s = b)

def leaving (b : Block) (a : Site) : Bool :=
  match a with
  | .inl _ => false
  | .inr (.inl t) => decide (leaf t = b)
  | .inr (.inr (.inl s)) => decide (parent s = b)
  | .inr (.inr (.inr _)) => false

private theorem path_balance_nat (b : Block) (t : Leaf) :
    (∑ a ∈ univ.filter (fun a => entering b a), if below a t then (1 : ℕ) else 0) =
      ∑ a ∈ univ.filter (fun a => leaving b a), if below a t then (1 : ℕ) else 0 := by
  revert b t
  decide

private theorem path_balance (b : Block) (t : Leaf) :
    (∑ a ∈ univ.filter (fun a => entering b a), if below a t then (1 : ℝ) else 0) =
      ∑ a ∈ univ.filter (fun a => leaving b a), if below a t then (1 : ℝ) else 0 := by
  exact_mod_cast path_balance_nat b t

theorem aggregate_balance (b : Block) (q : Leaf → Current) :
    (∑ a ∈ univ.filter (fun a => entering b a), aggregate q a) =
      ∑ a ∈ univ.filter (fun a => leaving b a), aggregate q a := by
  funext i j
  have hagg (a : Site) : aggregate q a i j = ∑ t, if below a t then q t i j else 0 := by
    simp [aggregate, sum_apply, sum_filter]
  simp only [sum_apply, hagg]
  rw [sum_comm, sum_comm (s := univ.filter (fun a => leaving b a))]
  apply sum_congr rfl
  intro t _
  simp_rw [show ∀ a : Site, (if below a t then q t i j else 0) =
      (if below a t then (1 : ℝ) else 0) * q t i j from fun a => by split <;> simp]
  rw [← sum_mul, ← sum_mul, path_balance]

def capSide (q : Current) : TriangleSide := fun k i j => if k = 0 then q i j else 0

theorem project_capSide (q : Current) : projectSide (capSide q) = q := by
  funext i j
  simp [projectSide, capSide]

def liftSide (a : Site) (q : Current) : TriangleSide :=
  match a with
  | .inl _ => capSide q
  | .inr (.inl _) => capSide q
  | .inr (.inr (.inl _)) => slideOld q
  | .inr (.inr (.inr _)) => slideNew q

theorem project_liftSide (a : Site) (q : Current) : projectSide (liftSide a q) = q := by
  rcases a with u | t | s | s
  · exact project_capSide q
  · exact project_capSide q
  · exact project_slideOld q
  · exact project_slideNew q

theorem liftSide_covered {c q : Current} (h : covered c q) (a : Site) :
    sideCovered (liftSide a c) (liftSide a q) := by
  have hcap : sideCovered (capSide c) (capSide q) := by
    intro k i j
    by_cases hk : k = 0
    · simpa [capSide, hk] using h i j
    · simp [capSide, hk]
  rcases a with u | t | s | s
  · exact hcap
  · exact hcap
  · exact slideOld_covered h
  · exact slideNew_covered h

def validSide (a : Site) (x : TriangleSide) : Prop :=
  match a with
  | .inl _ => SkewCurrent (x 0) ∧ ∀ k, k ≠ 0 → x k = 0
  | .inr (.inl _) => SkewCurrent (x 0) ∧ ∀ k, k ≠ 0 → x k = 0
  | .inr (.inr (.inl _)) => OldTriangles x
  | .inr (.inr (.inr _)) => NewTriangles x

theorem liftSide_valid {q : Current} (h : SkewCurrent q) (a : Site) :
    validSide a (liftSide a q) := by
  have hcap : SkewCurrent (capSide q 0) ∧ ∀ k, k ≠ 0 → capSide q k = 0 := by
    exact ⟨fun i j => by simpa [capSide] using h i j, fun k hk => by funext i j; simp [capSide, hk]⟩
  rcases a with u | t | s | s
  · exact hcap
  · exact hcap
  · exact slideOld_valid h
  · exact slideNew_valid h

theorem validSide_skew {a : Site} {x : TriangleSide} (h : validSide a x) :
    ∀ k, SkewCurrent (x k) := by
  have hcap : (SkewCurrent (x 0) ∧ ∀ k, k ≠ 0 → x k = 0) → ∀ k, SkewCurrent (x k) := by
    rintro ⟨hs, hz⟩ k
    by_cases hk : k = 0
    · simpa [hk] using hs
    · simp [hz k hk, SkewCurrent]
  rcases a with u | t | s | s
  · exact hcap h
  · exact hcap h
  · exact h.1
  · exact h.1

abbrev MultiDemand := Leaf → Demand
abbrev Fill := (Site → TriangleSide) × (Block → Label → Current)

def demands (z : MultiDemand) (a : Site) : Imbalance := aggregate (fun t => (z t).val) a

def ValidFill (p : Fill) : Prop :=
  (∀ a, validSide a (p.1 a)) ∧
    ∀ b i j k, p.2 b i j k = -p.2 b j i k ∧ p.2 b i j k = -p.2 b i k j

/-- In the cap equations, the lane currents are the divergence of the cap's
oriented triangles. A slab's boundary uses both triangle orientations. Internal
edges collect the signed incoming and outgoing triangles. -/
structure Fills (p : Fill) (z : MultiDemand) : Prop where
  start : ∀ i, ∑ j, projectSide (p.1 startSite) i j = demands z startSite i
  finish : ∀ t i, ∑ j, projectSide (p.1 (endSite t)) i j = demands z (endSite t) i
  slab : ∀ s, crossBoundary (p.1 (oldSite s)) (p.1 (newSite s)) =
    diagonal (demands z (oldSite s))
  internal : ∀ b i j, (∑ k, p.2 b k i j) +
      (∑ a ∈ univ.filter (fun a => entering b a), projectSide (p.1 a) i j) =
      ∑ a ∈ univ.filter (fun a => leaving b a), projectSide (p.1 a) i j

def admissible (z : MultiDemand) : Prop := ∀ t, unitCube (z t).val

def covers (c p : Fill) : Prop :=
  (∀ a, sideCovered (c.1 a) (p.1 a)) ∧ ∀ b, sideCovered (c.2 b) (p.2 b)

def totalCost (c : Fill) : ℝ :=
  ((∑ a, sideCost (c.1 a)) + (∑ b, sideCost (c.2 b)) / 3) / 200

def Unrestricted (c : Fill) : Prop :=
  ∀ z, admissible z → ∃ p, ValidFill p ∧ Fills p z ∧ covers c p

def Linear (c : Fill) : Prop :=
  ∃ L : MultiDemand →ₗ[ℝ] Fill, ∀ z, admissible z →
    ValidFill (L z) ∧ Fills (L z) z ∧ covers c (L z)

theorem project_filling {p : Fill} {z : MultiDemand} (hv : ValidFill p) (hp : Fills p z)
    (a : Site) : Routes (projectSide (p.1 a)) (demands z a) := by
  rcases a with u | t | s | s
  · cases u
    exact ⟨projectSide_skew (validSide_skew (hv.1 startSite)), hp.start⟩
  · exact ⟨projectSide_skew (validSide_skew (hv.1 (endSite t))), hp.finish t⟩
  · exact old_projection (hv.1 (oldSite s)) (hv.1 (newSite s)) (hp.slab s)
  · exact new_projection (hv.1 (oldSite s)) (hv.1 (newSite s)) (hp.slab s)


def assemble (q : Leaf → Current) : Fill :=
  (fun a => liftSide a (aggregate q a), 0)

def assembledCapacity (c : Current) : Fill :=
  (fun a => liftSide a ((multiplicity a : ℝ) • c), 0)

private theorem aggregate_routes {q : Leaf → Current} {z : MultiDemand}
    (h : ∀ t, Routes (q t) (z t).val) (a : Site) :
    Routes (aggregate q a) (demands z a) := by
  constructor
  · intro i j
    simp only [aggregate, sum_apply]
    simp only [← sum_neg_distrib]
    exact sum_congr rfl fun t _ => (h t).1 i j
  · intro i
    simp only [aggregate, sum_apply, demands]
    rw [sum_comm]
    exact sum_congr rfl fun t _ => (h t).2 i

theorem assemble_fills {q : Leaf → Current} {z : MultiDemand}
    (h : ∀ t, Routes (q t) (z t).val) : ValidFill (assemble q) ∧ Fills (assemble q) z := by
  have ha (a : Site) := aggregate_routes h a
  refine ⟨⟨fun a => liftSide_valid (ha a).1 a, fun b i j k => by simp [assemble]⟩,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i
    simp only [assemble, project_liftSide]
    exact (ha startSite).2 i
  · intro t i
    simp only [assemble, project_liftSide]
    exact (ha (endSite t)).2 i
  · intro s
    change crossBoundary (slideOld (aggregate q (oldSite s))) (slideNew (aggregate q (oldSite s))) = _
    exact crossBoundary_slides (ha (oldSite s))
  · intro b i j
    have hbal := congrFun (congrFun (aggregate_balance b q) i) j
    simpa [assemble, project_liftSide, sum_apply] using hbal

theorem assemble_covered {q : Leaf → Current} {c : Current}
    (h : ∀ t, covered c (q t)) : covers (assembledCapacity c) (assemble q) := by
  refine ⟨fun a => liftSide_covered ?_ a, fun b k i j => by simp [assembledCapacity, assemble]⟩
  intro i j
  simp only [aggregate, sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun t _ => h t i j).trans_eq ?_)
  simp [multiplicity, aggregate, sum_const, nsmul_eq_mul]

private theorem liftSide_add (a : Site) (q r : Current) :
    liftSide a (q + r) = liftSide a q + liftSide a r := by
  funext k i j
  rcases a with u | t | s | s <;>
    simp only [liftSide, capSide, slideOld, slideNew, Pi.add_apply] <;>
    split <;> simp_all

private theorem liftSide_smul (a : Site) (r : ℝ) (q : Current) :
    liftSide a (r • q) = r • liftSide a q := by
  funext k i j
  rcases a with u | t | s | s <;>
    simp only [liftSide, capSide, slideOld, slideNew, Pi.smul_apply] <;>
    split <;> simp_all

private def assemblyLinear (q : Demand →ₗ[ℝ] Current) : MultiDemand →ₗ[ℝ] Fill where
  toFun z := assemble (fun t => q (z t))
  map_add' z w := by
    apply Prod.ext
    · funext a
      change liftSide a (aggregate (fun t => q ((z + w) t)) a) =
        liftSide a (aggregate (fun t => q (z t)) a) + liftSide a (aggregate (fun t => q (w t)) a)
      simp only [Pi.add_apply, aggregate, map_add, sum_add_distrib, liftSide_add]
    · change (0 : Block → Label → Current) = 0 + 0
      rw [add_zero]
  map_smul' r z := by
    apply Prod.ext
    · funext a
      change liftSide a (aggregate (fun t => q ((r • z) t)) a) =
        r • liftSide a (aggregate (fun t => q (z t)) a)
      simp only [Pi.smul_apply, aggregate, map_smul, ← smul_sum, liftSide_smul]
    · change (0 : Block → Label → Current) = r • 0
      rw [smul_zero]

theorem lift_unrestricted {c : Current} (hc : NonlinearEnvelope c) :
    Unrestricted (assembledCapacity c) := by
  intro z hz
  choose q hq hcov using fun t => hc (z t) (hz t)
  obtain ⟨hv, hf⟩ := assemble_fills hq
  exact ⟨assemble q, hv, hf, assemble_covered hcov⟩

theorem lift_linear {c : Current} (hc : LinearEnvelope c) :
    Linear (assembledCapacity c) := by
  obtain ⟨q, hq⟩ := hc
  refine ⟨assemblyLinear q, fun z hz => ?_⟩
  obtain ⟨hv, hf⟩ := assemble_fills (fun t => (hq (z t) (hz t)).1)
  exact ⟨hv, hf, assemble_covered (fun t => (hq (z t) (hz t)).2)⟩

private theorem cost_smul (r : ℝ) (c : Current) : cost (r • c) = r * cost c := by
  simp only [cost, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  ring

theorem assembledCapacity_cost (c : Current) : totalCost (assembledCapacity c) = 64 * cost c / 200 := by
  have hsite (a : Site) :
      sideCost ((assembledCapacity c).1 a) = (multiplicity a : ℝ) * cost c := by
    rw [← projectSide_cost, assembledCapacity, project_liftSide, cost_smul]
  have hint : (∑ b, sideCost ((assembledCapacity c).2 b)) = 0 := by
    simp [assembledCapacity, sideCost, cost]
  rw [totalCost, hint, zero_div, add_zero]
  simp only [hsite, ← sum_mul, multiplicity_sum]

private def synchronous (z : Demand) : MultiDemand := fun _ => z

private def localCapacity (c : Fill) (a : Site) : Current :=
  (multiplicity a : ℝ)⁻¹ • projectSide (c.1 a)

private def localRoute (p : Fill) (a : Site) : Current :=
  (multiplicity a : ℝ)⁻¹ • projectSide (p.1 a)

private theorem synchronous_demands (z : Demand) (a : Site) :
    demands (synchronous z) a = (multiplicity a : ℝ) • z.val := by
  simp [demands, synchronous, aggregate, multiplicity, sum_const, Nat.cast_smul_eq_nsmul]

private theorem restrict_fill {p c : Fill} {z : Demand} (hv : ValidFill p)
    (hf : Fills p (synchronous z)) (hc : covers c p) (a : Site) :
    Routes (localRoute p a) z.val ∧ covered (localCapacity c a) (localRoute p a) := by
  have h := project_filling hv hf a
  rw [synchronous_demands] at h
  have hn := multiplicity_pos a
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    simp only [localRoute, Pi.smul_apply, smul_eq_mul, h.1 i j, mul_neg]
  · intro i
    simp only [localRoute, Pi.smul_apply, smul_eq_mul, ← mul_sum, h.2 i, ← mul_assoc,
      inv_mul_cancel₀ hn.ne', one_mul]
  · intro i j
    simp only [localRoute, localCapacity, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hn.le)]
    exact mul_le_mul_of_nonneg_left (projectSide_covered (hc.1 a) i j) (inv_nonneg.mpr hn.le)

theorem restrict_unrestricted {c : Fill} (hc : Unrestricted c) (a : Site) :
    NonlinearEnvelope (localCapacity c a) := by
  intro z hz
  obtain ⟨p, hv, hf, hp⟩ := hc (synchronous z) (fun _ => hz)
  exact ⟨localRoute p a, restrict_fill hv hf hp a⟩

private def restrictLinear (L : MultiDemand →ₗ[ℝ] Fill) (a : Site) : Demand →ₗ[ℝ] Current where
  toFun z := localRoute (L (synchronous z)) a
  map_add' x y := by
    change localRoute (L (synchronous x + synchronous y)) a = _
    rw [map_add]
    funext i j
    simp [localRoute, projectSide, sum_add_distrib, mul_add]
  map_smul' r z := by
    change localRoute (L (r • synchronous z)) a = _
    rw [map_smul]
    funext i j
    change (multiplicity a : ℝ)⁻¹ * (∑ k, r * (L (synchronous z)).1 a k i j) =
      r * ((multiplicity a : ℝ)⁻¹ * ∑ k, (L (synchronous z)).1 a k i j)
    rw [← mul_sum]
    ring

theorem restrict_linear {c : Fill} (hc : Linear c) (a : Site) :
    LinearEnvelope (localCapacity c a) := by
  obtain ⟨L, hL⟩ := hc
  refine ⟨restrictLinear L a, fun z hz => ?_⟩
  obtain ⟨hv, hf, hp⟩ := hL (synchronous z) (fun _ => hz)
  exact restrict_fill hv hf hp a

private theorem lower_of_sites (c : Fill) (B : ℝ)
    (hs : ∀ a, B ≤ cost (localCapacity c a))
    (hn : ∀ b k i j, 0 ≤ c.2 b k i j) : 64 * B / 200 ≤ totalCost c := by
  have hsite (a : Site) : (multiplicity a : ℝ) * B ≤ sideCost (c.1 a) := by
    have ha := hs a
    rw [localCapacity, cost_smul, projectSide_cost] at ha
    have hs := mul_le_mul_of_nonneg_left ha (multiplicity_pos a).le
    simpa only [← mul_assoc, mul_inv_cancel₀ (multiplicity_pos a).ne', one_mul] using hs
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ (univ : Finset Site)) => hsite a
  rw [← sum_mul, multiplicity_sum] at hsum
  have hint : 0 ≤ ∑ b, sideCost (c.2 b) := by
    simp only [sideCost, cost]
    exact sum_nonneg fun b _ => sum_nonneg fun k _ => div_nonneg
      (sum_nonneg fun i _ => sum_nonneg fun j _ => hn b k i j) (by norm_num)
  unfold totalCost
  linarith

/-- The nonlinear and linear common envelopes on the weighted three-branching-
level five-label binary staircase have different sharp costs. -/
theorem exact_weighted_costs :
    (∃ c, Unrestricted c ∧ totalCost c = 16 / 15) ∧
    (∀ c, Unrestricted c → 16 / 15 ≤ totalCost c) ∧
    (∃ c, Linear c ∧ totalCost c = 32 / 25) ∧
    ∀ c, Linear c → 32 / 25 ≤ totalCost c := by
  obtain ⟨⟨cn, hcn, ecn⟩, _, ⟨cl, hcl, ecl⟩, _⟩ := exact_pair_costs
  refine ⟨⟨assembledCapacity cn, lift_unrestricted hcn, ?_⟩, ?_,
    ⟨assembledCapacity cl, lift_linear hcl, ?_⟩, ?_⟩
  · rw [assembledCapacity_cost, ecn]
    norm_num
  · intro c hc
    have hloc (a : Site) := nonlinear_lower (restrict_unrestricted hc a)
    obtain ⟨p, _, _, hp⟩ := hc 0 (by intro t i; simp)
    have hnn b k i j := (abs_nonneg (p.2 b k i j)).trans (hp.2 b k i j)
    have h := lower_of_sites c (10 / 3) hloc hnn
    norm_num at h
    exact h
  · rw [assembledCapacity_cost, ecl]
    norm_num
  · intro c hc
    have hloc (a : Site) := linear_lower (restrict_linear hc a)
    obtain ⟨L, hL⟩ := hc
    have hp := (hL 0 (by intro t i; simp)).2.2
    have hnn b k i j := (abs_nonneg ((L 0).2 b k i j)).trans (hp.2 b k i j)
    have h := lower_of_sites c 4 hloc hnn
    norm_num at h
    exact h

end
end FiveLaneRouting.BinaryStaircase
