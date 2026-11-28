import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeConcentration
import Mathlib.Order.Interval.Finset.Fin

compile_only_with_mathlib

/-! Omega original.

Localizing an offline chain rule to ancestral spines has a quantitative error
bound depending only on the number of copies at each insertion.
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
local notation "o" => (root (n := n) (k := k) 0)

private theorem clone_fixed (i : D) (hi : i ≠ 0) (σ : Equiv.Perm K) (v : V)
    (hv : stage v < i) : clone i hi σ v = v := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := v.val.1.reclone i hi σ) (c := v.val.1) rfl
    funext j
    simp [History.reclone, not_le_of_gt (show v.val.1.stage < i from hv)]
  · rfl

private theorem clone_preserves_adj (i : D) (hi : i ≠ 0) (σ : Equiv.Perm K) (v w : V) :
    (graph n k).Adj (clone i hi σ v) (clone i hi σ w) ↔ (graph n k).Adj v w :=
  clone_adj i hi σ v w

private def pointedPre (v w : V) : Prop := pre v w ∧ v ≠ o

private theorem fixes_root
    (τ : depthAutomorphisms (graph n k) depth (pointedPre (n := n) (k := k))) :
    τ.val o = o := by
  by_contra hn
  exact ((τ.property.2.2 o o).mp ⟨data.refl _, hn⟩).2 rfl

private def cloneAuto (i : D) (hi : i ≠ 0) (σ : Equiv.Perm K) :
    depthAutomorphisms (graph n k) depth (pointedPre (n := n) (k := k)) := by
  refine ⟨clone i hi σ, clone_preserves_adj i hi σ, fun _ => rfl, fun x y => ?_⟩
  have ho := clone_fixed i hi σ o (by
    change (0 : D) < i
    exact lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hi))
  simp only [pointedPre]
  change ((x.val.1.reclone i hi σ).IsPrefix (y.val.1.reclone i hi σ) ∧
    clone i hi σ x ≠ o) ↔ (x.val.1.IsPrefix y.val.1 ∧ x ≠ o)
  have he : clone i hi σ x ≠ o ↔ x ≠ o := by
    calc
      _ ↔ clone i hi σ x ≠ clone i hi σ o := by rw [ho]
      _ ↔ _ := (clone i hi σ).injective.ne_iff
  rw [History.reclone_prefix, he]

private def symmetric (p : V → Chains V) :=
  symmetrize (graph n k) depth pointedPre (fun v => p v - p o)

private theorem symmetric_zero (p : V → Chains V) : symmetric p o = 0 := by
  ext e
  unfold symmetric symmetrize
  simp [fixes_root, Pi.sub_apply]

private theorem symmetric_boundary (p : V → Chains V)
    (hb : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1) (v : V) :
    boundary (symmetric p v) = Pi.single v 1 - Pi.single o 1 := by
  apply symmetrize_boundary
  · intro x
    rw [boundary_sub, hb, hb, sub_self, sub_zero]
  · intro σ x
    have he : σ.val x = o ↔ x = o := by
      calc
        _ ↔ σ.val x = σ.val o := by rw [fixes_root σ]
        _ ↔ _ := σ.val.injective.eq_iff
    simp only [Pi.single_apply, he]

private theorem symmetric_supported (p : V → Chains V)
    (hp : ∀ v, Supported (graph n k) (p v)) (v : V) :
    Supported (graph n k) (symmetric p v) := by
  apply symmetrize_supported
  intro x e he
  simp [hp x e he, hp o e he]

private theorem symmetric_fit (p : V → Chains V) (R : ℝ)
    (h : ∀ u v, (graph n k).Adj u v → dualNorm B (orientedEdge u v + p u - p v) ≤ R)
    (u v : V) (huv : (graph n k).Adj u v) :
    dualNorm B (orientedEdge u v + symmetric p u - symmetric p v) ≤ R := by
  apply symmetrize_residual_le _ _ _ _ _ ?_ u v huv
  intro x y hxy
  convert h x y hxy using 2
  abel

private theorem edge_supported {u v : V} (h : (graph n k).Adj u v) :
    Supported (graph n k) (orientedEdge u v) := by
  intro e he
  have h₁ : e ≠ (u,v) := fun q => he (q ▸ h)
  have h₂ : e ≠ (v,u) := fun q => he (q ▸ h.symm)
  simp [orientedEdge, h₁, h₂]

private theorem edge_eval_clone (i : D) (hi : i ≠ 0) (σ : Equiv.Perm K) (u v : V)
    (hu : stage u < i) (hv : stage v < i) (x y : V) :
    orientedEdge u v (clone i hi σ x, clone i hi σ y) = orientedEdge u v (x,y) := by
  let τ := clone i hi σ
  have h₁ : τ.symm u = u := by
    apply τ.injective
    rw [Equiv.apply_symm_apply, clone_fixed i hi σ u hu]
  have h₂ : τ.symm v = v := by
    apply τ.injective
    rw [Equiv.apply_symm_apply, clone_fixed i hi σ v hv]
  have h := congrFun (pushChain_equiv τ (orientedEdge u v)) (x,y)
  simpa only [pushChain_edge, h₁, h₂] using h.symm

private theorem residual_invariant (p : V → Chains V) (i : D) (hi : i ≠ 0) (σ : Equiv.Perm K)
    (u v : V) (hu : stage u < i) (hv : stage v < i) (x y : V) :
    (orientedEdge u v + symmetric p u - symmetric p v) (clone i hi σ x, clone i hi σ y) =
      (orientedEdge u v + symmetric p u - symmetric p v) (x,y) := by
  have hu' := symmetrize_equivariant (graph n k) depth pointedPre
    (fun x => p x - p o) (cloneAuto i hi σ) u x y
  have hv' := symmetrize_equivariant (graph n k) depth pointedPre
    (fun x => p x - p o) (cloneAuto i hi σ) v x y
  change symmetric p (clone i hi σ u) (clone i hi σ x, clone i hi σ y) = symmetric p u (x,y) at hu'
  change symmetric p (clone i hi σ v) (clone i hi σ x, clone i hi σ y) = symmetric p v (x,y) at hv'
  rw [clone_fixed i hi σ u hu] at hu'
  rw [clone_fixed i hi σ v hv] at hv'
  simp only [Pi.sub_apply, Pi.add_apply, edge_eval_clone i hi σ u v hu hv, hu', hv']

private theorem root_prefix (x : V) : pre o x := History.initial_prefix _

private theorem previous_step (v : V) (hv : 0 < (stage v).val) :
    ∃ w : V, (stage w).val + 1 = (stage v).val ∧ pre w v ∧ (graph n k).Adj w v := by
  let b := v.val.1
  have hlt : previous b.stage < b.stage := Nat.sub_lt hv (by decide)
  let u := birth (b.prefix _ hlt.le)
  refine ⟨u, ?_, b.prefix_spec _ hlt.le, ?_⟩
  · change b.stage.val - 1 + 1 = b.stage.val
    omega
  · exact ⟨fun h => hlt.ne (congrArg (fun z => z.1.stage) h),
      Or.inr (Or.inl ⟨b.prefix_spec _ hlt.le, (b.legal _ le_rfl hv).2.2.2⟩)⟩

private theorem compare_spines (p : V → Chains V) (hp : ∀ v, Supported (graph n k) (p v))
    (R : ℝ) (hR : 0 ≤ R) (kpos : 0 < k)
    (hr : ∀ x y, (graph n k).Adj x y → dualNorm B (orientedEdge x y + p x - p y) ≤ R)
    (u v : V) (huv : pre u v) (hstage : stage u < stage v) :
    dualNorm B
      (pushChain (retract u.val.1) (symmetric p u) -
        pushChain (retract v.val.1) (symmetric p u)) ≤ 2 * R / (k : ℝ) := by
  classical
  let C : ℝ := 2 * R / (k : ℝ)
  let K₀ : ℝ := k + 1
  let diff (c : Chains V) := pushChain (retract u.val.1) c - pushChain (retract v.val.1) c
  let q := symmetric p
  let after : D := ⟨(stage u).val + 1, (Nat.succ_le_of_lt hstage).trans_lt (stage v).isLt⟩
  have hK : 0 < K₀ := by dsimp [K₀]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hk : (0 : ℝ) < k := by exact_mod_cast kpos
  have hgeo (t : ℕ) : C / K₀ ^ (t + 1) + 2 * R / K₀ ^ (t + 1) = C / K₀ ^ t := by
    rw [← add_div, pow_succ]
    have he : C + 2 * R = C * K₀ := by
      dsimp [K₀, C]
      field_simp
      ring
    rw [he, mul_div_mul_right _ _ hK.ne']
  have hrootGeo (t : ℕ) : 2 * R / K₀ ^ (t + 1) ≤ C / K₀ ^ t := by
    linarith [hgeo t, div_nonneg hC (pow_nonneg hK.le (t+1))]
  have step (x y : V) (hx : pre x u) (hy : pre y u) (hxy : (graph n k).Adj x y)
      (hdep : stage x ≤ stage y) :
      dualNorm B (diff (q y)) ≤ dualNorm B (diff (q x)) +
        2 * R / K₀ ^ (after.val - (stage y).val) := by
    let Z := orientedEdge x y + q x - q y
    have hpZ : Supported (graph n k) Z := by
      intro e he
      simp [Z, q, edge_supported hxy e he, symmetric_supported p hp x e he,
        symmetric_supported p hp y e he]
    let s := Finset.Ioc (stage y) after
    have hle (j : D) (hj : j ∈ s) : stage y < j ∧ j ≤ after := Finset.mem_Ioc.mp hj
    have h0 (j : D) (hj : j ∈ s) : j ≠ 0 := fun e =>
      (Fin.zero_le (stage y)).not_gt (e ▸ (hle j hj).1)
    have hw := retract_change_le u v huv hstage Z hpZ s
      (fun j hj => (hle j hj).2) h0
      (fun j hj hjs σ z w => residual_invariant p j hj σ x y
        (hdep.trans_lt (hle j hjs).1) (hle j hjs).1 z w)
    have hwn : dualNorm B (diff Z) ≤ 2 * R / K₀ ^ (after.val - (stage y).val) := by
      have hbudget := symmetric_fit p R hr x y hxy
      rw [show s.card = after.val - (stage y).val by exact Fin.card_Ioc _ _] at hw
      exact hw.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudget (by norm_num)) (pow_nonneg hK.le _))
    have he : diff (q y) = diff (q x) + -(diff Z) := by
      dsimp [diff, Z]
      rw [pushChain_sub, pushChain_sub, pushChain_add, pushChain_add, pushChain_edge,
        pushChain_edge, retract_fixed hx, retract_fixed hy,
        retract_fixed (data.trans hx huv), retract_fixed (data.trans hy huv)]
      abel
    rw [he]
    calc
      _ ≤ dualNorm B (diff (q x)) + dualNorm B (-(diff Z)) := dualNorm_add_le B _ _
      _ ≤ _ := by rw [dualNorm_neg_eq]; gcongr
  have hz : dualNorm B (diff (q o)) ≤ 0 := by
    have h : ∀ ρ : V → V, pushChain ρ 0 = 0 := by intro ρ; ext e; simp [pushChain]
    simp only [q, symmetric_zero, diff, h, sub_self]
    simpa [mass] using dualNorm_le_mass B 0
  have ind (x : V) (hx : pre x u) :
      dualNorm B (diff (q x)) ≤ C / K₀ ^ ((stage u).val - (stage x).val) := by
    generalize hdepth : (stage x).val = j
    induction j using Nat.strong_induction_on generalizing x with
    | h j ih =>
      rw [← hdepth]
      by_cases hj : j = 0
      · have hd0 := hdepth.trans hj
        by_cases he : x = o
        · subst x
          exact hz.trans (div_nonneg hC (pow_nonneg hK.le _))
        have hst : x.val.1.stage = 0 := Fin.ext hd0
        have hrep : x = root x.val.2 := Subtype.ext (Prod.ext (History.stage_zero hst) rfl)
        have ha : (0 : Fin 3) ≠ x.val.2 := fun e => he (by rw [hrep, ← e])
        have he' : (graph n k).Adj o x := by rw [hrep]; exact root_adj ha
        have hh := step o x (root_prefix _) hx he' (Fin.zero_le _)
        apply hh.trans
        have hd : after.val - (stage x).val = ((stage u).val - (stage x).val) + 1 := by
          change (stage u).val + 1 - (stage x).val = _
          omega
        rw [hd]
        exact (add_le_add_left hz _).trans (by simpa using hrootGeo ((stage u).val - (stage x).val))
      · obtain ⟨y, hsucc, hyv, hyx⟩ := previous_step x (by omega)
        have hyu := data.trans hyv hx
        have hi := ih (stage y).val (by omega) y hyu rfl
        have hs := step y x hyu hx hyx hyv.1
        have hd : after.val - (stage x).val = ((stage u).val - (stage x).val) + 1 := by
          have hle : (stage x).val ≤ (stage u).val := hx.1
          change (stage u).val + 1 - (stage x).val = _
          omega
        have hd' : (stage u).val - (stage y).val = ((stage u).val - (stage x).val) + 1 := by
          have hle : (stage x).val ≤ (stage u).val := hx.1
          omega
        rw [hd'] at hi
        rw [hd] at hs
        exact (hs.trans (add_le_add_left hi _)).trans_eq (hgeo _)
  simpa [C, q, diff] using ind u (data.refl u.val.1)

theorem push_single_boundary {l : ℕ} (f : V → Vertex n l) (v : V)
    (z : Chains V) (hb : boundary z = Pi.single v 1 - Pi.single o 1) :
    boundary (pushChain f z) = Pi.single (f v) 1 - Pi.single (f o) 1 := by
  classical
  ext y
  rw [pushChain_boundary]
  have he (w : V) :
      (∑ x : V, if f x = y then Pi.single (M := fun _ : V => ℝ) w 1 x else 0) =
        Pi.single (M := fun _ : Vertex n l => ℝ) (f w) 1 y := by
    trans ∑ x : V, if x = w then (if f w = y then (1 : ℝ) else 0) else 0
    · apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = w <;> simp [hx]
    · simp [Pi.single_apply, eq_comm]
  have dist (P : Prop) [Decidable P] (a b : ℝ) :
      (if P then a - b else 0) = (if P then a else 0) - (if P then b else 0) := by
    split <;> simp_all
  simp only [hb, Pi.sub_apply, dist, Finset.sum_sub_distrib, he]

private def edgePart (z : Chains V) : Chains V := by
  classical
  exact fun e => if (graph n k).Adj e.1 e.2 then z e else 0

private theorem edgePart_sub (c d : Chains V) : edgePart (c - d) = edgePart c - edgePart d := by
  funext e
  by_cases h : (graph n k).Adj e.1 e.2 <;> simp [edgePart, h]

private theorem edgePart_add (c d : Chains V) : edgePart (c + d) = edgePart c + edgePart d := by
  funext e
  by_cases h : (graph n k).Adj e.1 e.2 <;> simp [edgePart, h]

private theorem edgePart_eq {c : Chains V} (hc : Supported (graph n k) c) :
    edgePart c = c := by
  funext e
  by_cases h : (graph n k).Adj e.1 e.2
  · simp [edgePart, h]
  · simp [edgePart, h, hc e h]

private theorem edgePart_boundary (c : Chains V) (hc : ∀ e : V × V,
    e.1 ≠ e.2 → ¬(graph n k).Adj e.1 e.2 → c e = 0) :
    boundary (edgePart c) = boundary c := by
  ext v
  unfold boundary
  apply Finset.sum_congr rfl
  intro u _
  by_cases huv : (graph n k).Adj u v
  · simp [edgePart, huv, huv.symm]
  · by_cases he : u = v
    · subst u
      simp
    simp [edgePart, huv, hc (u,v) he huv, hc (v,u) (fun h => he h.symm) (fun h => huv h.symm)]

private theorem edgePart_norm (c : Chains V) : dualNorm B (edgePart c) ≤ dualNorm B c := by
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  have hpair (d : Chains V) : pairing f (edgePart d) = pairing (edgePart f) d := by
    unfold pairing
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : (graph n k).Adj e.1 e.2 <;> simp [edgePart, h]
  have had : Admissible B (edgePart f) := by
    refine ⟨fun e => ?_, fun t => ?_⟩
    · unfold edgePart
      split
      · exact hf.1 e
      · norm_num
    · rw [← hpair, edgePart_eq]
      · exact hf.2 t
      · intro e he
        simp [triangleChain, edge_supported t.2.1 e he,
          edge_supported t.2.2.1 e he, edge_supported t.2.2.2 e he]
  rw [hpair]
  exact abs_pairing_le_dualNorm had _

/-- An offline rooted chain family of error at most R has an ancestral
localization with error at most R + 2R/k, where the number of copies is k+1. -/
theorem sharp_localization (p : V → Chains V) (hp : ∀ v, Supported (graph n k) (p v))
    (hb : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1) (R : ℝ)
    (hR : 0 ≤ R) (hk : 0 < k)
    (hr : ∀ u v, (graph n k).Adj u v → dualNorm B (orientedEdge u v + p u - p v) ≤ R) :
    ∃ q : V → Chains V,
      (∀ v, boundary (q v) = Pi.single v 1 - Pi.single o 1) ∧
      (∀ v a b, ¬(pre a v ∧ pre b v ∧ (graph n k).Adj a b) → q v (a,b) = 0) ∧
      (∀ u v, (graph n k).Adj u v →
        dualNorm B (orientedEdge u v + q u - q v) ≤ R + 2 * R / (k : ℝ)) := by
  classical
  let q' (v : V) := pushChain (retract v.val.1) (symmetric p v)
  let q (v : V) := edgePart (q' v)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro v
    unfold q q'
    rw [edgePart_boundary, push_single_boundary _ _ _ (symmetric_boundary p hb v),
      retract_fixed (data.refl _), retract_fixed (root_prefix _)]
    intro e hne he
    exact retract_support v e.1 e.2 _ (symmetric_supported p hp v)
      (fun h => h.2.2.elim hne he)
  · intro v a b h
    by_cases hab : (graph n k).Adj a b
    · change (if (graph n k).Adj a b then q' v (a,b) else 0) = 0
      rw [ite_eq_left hab]
      exact retract_support v a b _ (symmetric_supported p hp v) (fun hh => h ⟨hh.1,hh.2.1,hab⟩)
    · simp [q, edgePart, hab]
  · have forward (u v : V) (huv : (graph n k).Adj u v) (hdep : stage u ≤ stage v) :
        dualNorm B (orientedEdge u v + q u - q v) ≤ R + 2 * R / (k : ℝ) := by
      have hr' := symmetric_fit p R hr u v huv
      let Z := orientedEdge u v + symmetric p u - symmetric p v
      have hpv := dualNorm_pushChain_le (retract v.val.1) (fun _ _ => retract_edge v.val.1) Z
      have hpre : pre u v := (rolling_earlier data huv hdep).1
      have hz :
          orientedEdge u v + q' u - q' v = pushChain (retract v.val.1) Z +
            (pushChain (retract u.val.1) (symmetric p u) -
              pushChain (retract v.val.1) (symmetric p u)) := by
        dsimp [q', Z]
        rw [pushChain_sub, pushChain_add, pushChain_edge, retract_fixed hpre, retract_fixed (data.refl _)]
        abel
      have he : orientedEdge u v + q u - q v = edgePart (orientedEdge u v + q' u - q' v) := by
        rw [edgePart_sub, edgePart_add, edgePart_eq (edge_supported huv)]
      rw [he]
      apply (edgePart_norm _).trans
      by_cases h : stage u = stage v
      · have hh := History.IsPrefix.eq_of_stage_eq hpre h
        rw [hz, hh, sub_self, add_zero]
        exact hpv.trans (hr'.trans (le_add_of_nonneg_right (by positivity)))
      · rw [hz]
        exact (dualNorm_add_le B _ _).trans (add_le_add (hpv.trans hr')
          (compare_spines p hp R hR hk hr u v hpre (lt_of_le_of_ne hdep h)))
    intro u v huv
    rcases le_total (stage u) (stage v) with h | h
    · exact forward u v huv h
    · rw [show orientedEdge u v + q u - q v = -(orientedEdge v u + q v - q u) by
        rw [orientedEdge_reverse v u]
        abel, dualNorm_neg_eq]
      exact forward v u huv.symm h

/-- A rooted offline rule with bounded triangle-dual error. -/
def OfflineFeasible (n k : ℕ) (R : ℝ) : Prop :=
  ∃ p : Vertex n k → Chains (Vertex n k),
    (∀ v, Supported (graph n k) (p v)) ∧
    (∀ v, boundary (p v) = Pi.single v 1 - Pi.single (root 0) 1) ∧
    ∀ u v, (graph n k).Adj u v →
      dualNorm (triangleChain (G := graph n k)) (orientedEdge u v + p u - p v) ≤ R

/-- A rooted rule on the single-copy tree, supported entirely on each vertex's ancestor spine. -/
def CausalFeasible (n : ℕ) (R : ℝ) : Prop :=
  ∃ p : Vertex n 0 → Chains (Vertex n 0),
    (∀ v, boundary (p v) = Pi.single v 1 - Pi.single (root 0) 1) ∧
    (∀ v a b, ¬(pre a v ∧ pre b v ∧ (graph n 0).Adj a b) → p v (a,b) = 0) ∧
    ∀ u v, (graph n 0).Adj u v →
      dualNorm (triangleChain (G := graph n 0)) (orientedEdge u v + p u - p v) ≤ R

theorem offline_to_causal {R : ℝ} (hR : 0 ≤ R) (hk : 0 < k)
    (h : OfflineFeasible n k R) : CausalFeasible n (R + 2 * R / (k : ℝ)) := by
  classical
  obtain ⟨p,hp,hb,hr⟩ := h
  obtain ⟨q,hqb,hqs,hqr⟩ := sharp_localization p hp hb R hR hk hr
  let f : V → Vertex n 0 := forget
  let s : Vertex n 0 → V := selectCopy
  refine ⟨fun v => pushChain f (q (s v)), ?_, ?_, ?_⟩
  · intro v
    rw [push_single_boundary f _ _ (hqb _)]
    change Pi.single (forget (selectCopy v)) 1 - Pi.single (forget (root 0 : V)) 1 = _
    rw [forget_selectCopy, forget, copyMap_root]
  · intro v a b hn
    simp only [pushChain, Finset.sum_apply, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro e _
    split
    · rename_i he
      apply hqs
      intro hh
      apply hn
      have ha : a = f e.1 := congrArg Prod.fst he
      have hb : b = f e.2 := congrArg Prod.snd he
      rw [ha,hb]
      rw [← forget_selectCopy (k := k) v]
      exact ⟨History.copyMap_prefix _ rfl hh.1, History.copyMap_prefix _ rfl hh.2.1,
        copyMap_edge _ rfl hh.2.2⟩
    · rfl
  · intro u v huv
    have hs : (graph n k).Adj (s u) (s v) := copyMap_edge _ rfl huv
    have hpush := dualNorm_pushChain_le f (fun _ _ e => Or.inr (copyMap_edge _ rfl e))
      (orientedEdge (s u) (s v) + q (s u) - q (s v))
    rw [pushChain_sub, pushChain_add, pushChain_edge] at hpush
    change dualNorm (triangleChain (G := graph n 0))
      (orientedEdge (forget (selectCopy u)) (forget (selectCopy v)) +
        pushChain f (q (s u)) - pushChain f (q (s v))) ≤ _ at hpush
    rw [forget_selectCopy, forget_selectCopy] at hpush
    exact hpush.trans (hqr _ _ hs)

end
end Omega.PureThreeTree
