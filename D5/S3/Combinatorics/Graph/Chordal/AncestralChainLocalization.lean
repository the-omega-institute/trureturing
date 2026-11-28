/- GID: D5/S3/Combinatorics/Graph/Chordal/AncestralChainLocalization
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-sharp-four-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Retraction of rolling-clique graphs to ancestral spines and localization of real chain potentials. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.RollingCliqueHistories
import D5.S3.Topology.GraphChains.GraphChainAveraging

compile_only_with_mathlib

/-! Omega original.

Retraction of rolling-clique graphs to ancestral spines and localization of real chain potentials. -/

namespace Omega.RollingCliques

open SimpleGraph Omega.GraphChains

open scoped BigOperators

noncomputable section

section RootNormalization

variable {n q k : ℕ} {P : Retention n q}

abbrev HV (P : Retention n q) (k : ℕ) := History P k × Fin q

private theorem History.stage_zero {b : History P k} (h : b.stage = 0) :
    b = History.initial P :=
  ((historyData P).earlier b).resolve_right (by
    rintro ⟨c,hpre,hne,_⟩
    have hlt := (historyData P).depth_lt hpre hne
    change c.stage.val < b.stage.val at hlt
    simp [h] at hlt)

def rootMass (v : HV P k) : ℝ := if v.1.stage = 0 then (q : ℝ)⁻¹ else 0

private def centerRoot (p : HV P k → Chains (HV P k)) (v : HV P k) : Chains (HV P k) :=
  p v - meanChain (fun a : Fin q => p (History.initial P,a))

private theorem centerRoot_boundary (hq : 0 < q) (o : HV P k)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1) (v : HV P k) :
    boundary (centerRoot p v) = Pi.single v 1 - rootMass := by
  classical
  funext x
  rw [centerRoot, boundary_sub, hp, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, boundary_mean]
  have hc : ∑ a : Fin q, boundary (p (History.initial P,a)) x =
      (if x.1.stage = 0 then 1 else 0) - (q : ℝ) * Pi.single (M := fun _ : HV P k => ℝ) o 1 x := by
    simp only [hp, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    by_cases hx : x.1.stage = 0
    · have he := History.stage_zero hx
      rcases x with ⟨b,a⟩
      change b = History.initial P at he
      subst b
      simp [Pi.single_apply, History.initial]
    · have he : x.1 ≠ History.initial P := fun h => hx (congrArg History.stage h)
      have hne (a : Fin q) : x ≠ (History.initial P, a) := fun h => he (congrArg Prod.fst h)
      simp [Pi.single_apply, hne, hx]
  rw [hc, Fintype.card_fin]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  by_cases hx : x.1.stage = 0 <;> simp [rootMass, hx, mul_sub, ← mul_assoc, hq'] <;> ring

private theorem centerRoot_mass (hq : 0 < q) (R : ℝ) (hR : R ≤ 4)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ u v, (rolling (historyData P)).Adj u v →
      dualNorm (triangleChain (G := rolling (historyData P))) (orientedEdge u v + p u - p v) ≤ R)
    (v : HV P k) : mass (centerRoot p v) ≤ 13 * (n + 1) := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  have edge (u v : HV P k) (h : (rolling (historyData P)).Adj u v) :
      mass (p v - p u) ≤ 13 :=
    (mass_edge_difference_le _ _ _ _ (hp u v h)).trans (by linarith)
  have hall (a : Fin q) : mass (p v - p (History.initial P,a)) ≤ 13 * (n + 1) := by
    obtain ⟨walk,hwalk⟩ := rolling_short_walk (historyData P) a v
    have h' : walk.length ≤ n + 1 := hwalk.trans (Nat.add_le_add_right (Nat.le_of_lt_succ v.1.stage.isLt) 1)
    exact (mass_walk_difference_le p 13 edge walk).trans
      (by
        have : (walk.length : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h'
        nlinarith)
  have hEq : centerRoot p v = meanChain (fun a : Fin q => p v - p (History.initial P,a)) := by
    funext e
    have hq' : (q : ℝ) ≠ 0 := by positivity
    simp [centerRoot, meanChain, Finset.sum_sub_distrib, mul_sub, ← mul_assoc, hq']
  rw [hEq]
  exact mass_mean_le _ _ hall

end RootNormalization


private theorem clone_load_le {n q k : ℕ} {P : Retention n q}
    (p : History P k × Fin q → Chains (History P k × Fin q)) (L : ℝ)
    (hp : ∀ v, mass (p v) ≤ L)
    (hs : ∀ (σ : depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1)) v a b,
      p (σ.val v) (σ.val a, σ.val b) = p v (a,b))
    (x : History P k × Fin q) (t : Fin (n + 1)) (ht : x.1.stage < t) (a : Fin (k + 1)) :
    ∑ v ∈ Finset.univ.filter (fun v : History P k × Fin q => t ≤ v.1.stage ∧ (v.1.step t).2 = a),
      load (p x) v ≤ 2 * L / (k + 1 : ℝ) := by
  classical
  let V := History P k × Fin q
  let S : Finset V := Finset.univ.filter fun v => t ≤ v.1.stage
  let f : V → Fin (k + 1) := fun v => (v.1.step t).2
  have hroot : t ≠ 0 := fun h => (Fin.zero_le x.1.stage).not_gt (h ▸ ht)
  have hEq (b : Fin (k + 1)) :
      ∑ v ∈ S with f v = b, load (p x) v = ∑ v ∈ S with f v = a, load (p x) v := by
    let π := Equiv.swap a b
    let σ : Equiv.Perm V := clonePerm t hroot π
    have hσ : σ ∈ depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1) :=
      ⟨clonePerm_adj t hroot π, fun _ => rfl, fun _ _ => History.reclone_prefix t hroot π⟩
    have hx : σ x = x := by
      apply Prod.ext
      · apply History.ext' (b := x.1.reclone t hroot π) (c := x.1) rfl
        funext i
        simp [History.reclone, not_le_of_gt ht]
      · rfl
    have hload := invariant_load σ (p x) (fun u v => by
      have h := hs ⟨σ,hσ⟩ x u v
      change p (σ x) (σ u, σ v) = p x (u,v) at h
      rwa [hx] at h)
    simp only [Finset.sum_filter, and_assoc, S, Finset.mem_univ, true_and]
    rw [← Equiv.sum_comp σ (fun v => if t ≤ v.1.stage then if f v = b then load (p x) v else 0 else 0)]
    apply Finset.sum_congr rfl
    intro v _
    have he : (σ v).1.stage = v.1.stage := rfl
    rw [he, hload]
    by_cases hv : t ≤ v.1.stage
    · have hfv : f (σ v) = π (f v) := by simp [f, σ, clonePerm, History.reclone, hv]
      have hπ : π a = b := Equiv.swap_apply_left a b
      simp only [hfv, ← hπ, π.injective.eq_iff]
    · simp [hv]
  have hmass := equal_fiber_mass_bound S f (load (p x)) a hEq
  have hS : ∑ v ∈ S, load (p x) v ≤ 2 * L := by
    calc
      _ ≤ ∑ v, load (p x) v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => load_nonneg _ v)
      _ ≤ _ := by rw [sum_load]; exact mul_le_mul_of_nonneg_left (hp x) (by norm_num)
  have hfilter : S.filter (fun v => f v = a) = Finset.univ.filter
      (fun v : V => t ≤ v.1.stage ∧ f v = a) := by
    rw [Finset.filter_filter]
  rw [← hfilter, hmass, Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

section SpineRetraction

variable {n q k : ℕ} {P : Retention n q}

private def History.Break (b c : History P k) (i : Fin (n + 1)) : Prop :=
  i ≤ b.stage ∧ (c.stage < i ∨ b.step i ≠ c.step i)

private theorem History.exists_break {b c : History P k} (h : ¬b.IsPrefix c) :
    ∃ i, b.Break c i := by
  classical
  by_contra! hn
  apply h
  refine ⟨?_, ?_⟩
  · exact le_of_not_gt fun ht => hn b.stage ⟨le_rfl, Or.inl ht⟩
  · exact fun i hi => not_ne_iff.mp fun he => hn i ⟨hi, Or.inr he⟩

private noncomputable def History.firstBreak {b c : History P k} (h : ¬b.IsPrefix c) : Fin (n + 1) :=
  letI := Classical.propDecidable
  ((Finset.univ : Finset (Fin (n + 1))).filter (b.Break c)).min'
    (by obtain ⟨i, hi⟩ := exists_break h; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

private theorem History.firstBreak_mem {b c : History P k} (h : ¬b.IsPrefix c) :
    b.Break c (firstBreak h) := by
  classical
  unfold firstBreak
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

private theorem History.firstBreak_min {b c : History P k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : b.Break c i) : firstBreak h ≤ i := by
  classical
  unfold firstBreak
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

private theorem History.firstBreak_pos {b c : History P k} (h : ¬b.IsPrefix c) :
    0 < (firstBreak h).val := by
  have hh := (firstBreak_mem h).2
  by_contra! hl
  have he : firstBreak h = 0 := Fin.ext (Nat.eq_zero_of_le_zero hl)
  simp [he, b.root_step, c.root_step] at hh

private theorem History.firstBreak_eq {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    firstBreak hb = firstBreak hd := by
  have hm := firstBreak_mem hb
  have ha : d.Break c (firstBreak hb) := by
    exact ⟨hm.1.trans h.1, by rw [← h.2 _ hm.1]; exact hm.2⟩
  have hle := firstBreak_min hd ha
  have hh := firstBreak_mem hd
  have hh' : firstBreak hd ≤ b.stage := hle.trans hm.1
  have hz : b.Break c (firstBreak hd) := by
    exact ⟨hh', by rw [h.2 _ hh']; exact hh.2⟩
  exact le_antisymm (firstBreak_min hb hz) hle

private def Fin.previous (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

private theorem History.beforeBreak {b c : History P k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : i < firstBreak h) : i ≤ c.stage ∧ b.step i = c.step i := by
  have hb := hi.le.trans (firstBreak_mem h).1
  constructor
  · exact le_of_not_gt fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inl hh⟩)
  · exact not_ne_iff.mp fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inr hh⟩)

private theorem History.previous_lt_break {b c : History P k} (h : ¬b.IsPrefix c) :
    Fin.previous (firstBreak h) < firstBreak h := by
  have hh := firstBreak_pos h
  change (firstBreak h).val - 1 < (firstBreak h).val
  omega

private def History.breakBlock {b c : History P k} (h : ¬b.IsPrefix c) : History P k :=
  b.prefix (firstBreak h) (firstBreak_mem h).1

private theorem History.breakBlock_eq {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    breakBlock hb = breakBlock hd := by
  have he := firstBreak_eq h hb hd
  apply History.ext' he
  funext i
  simp only [breakBlock, History.prefix, ← he]
  split
  · rename_i hi
    exact h.2 _ (hi.trans (firstBreak_mem hb).1)
  · rfl

private noncomputable def History.collapseVertex (a : History P k) (h : 0 < a.stage.val) :
    History P k × Fin q := by
  have hp : Fin.previous a.stage ≤ a.stage := Nat.sub_le _ _
  have hn : ((a.step a.stage).1 (Fin.previous a.stage)).Nonempty := by
    rw [← Finset.card_pos, a.cardinal _ _ le_rfl]
    exact P.positivePrevious a.stage h
  exact (a.prefix (Fin.previous a.stage) hp, hn.choose)

noncomputable def spineMap (c : History P k) (v : History P k × Fin q) :
    History P k × Fin q := by
  classical
  exact if h : v.1.IsPrefix c then v else
    History.collapseVertex (History.breakBlock h) (History.firstBreak_pos h)

theorem spineMap_fixed {c : History P k} {v : History P k × Fin q}
    (h : v.1.IsPrefix c) : spineMap c v = v := by
  simp [spineMap, h]

theorem spineMap_on_spine (c : History P k) (v : History P k × Fin q) :
    (spineMap c v).1.IsPrefix c := by
  classical
  by_cases h : v.1.IsPrefix c
  · rwa [spineMap_fixed h]
  rw [spineMap, dite_eq_right h]
  have hm := History.previous_lt_break h
  have hc := (History.beforeBreak h hm).1
  refine ⟨hc, fun i hi => ?_⟩
  have hb : i < History.firstBreak h := hi.trans_lt hm
  have hi' : i ≤ Fin.previous (History.firstBreak h) := hi
  simpa [History.collapseVertex, History.breakBlock, History.prefix, hi', hb.le] using
    (History.beforeBreak h hb).2

private theorem spineMap_eq_of_outside {b d c : History P k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) (x y : Fin q) :
    spineMap c (b,x) = spineMap c (d,y) := by
  simp only [spineMap, dif_neg hb, dif_neg hd]
  have e : (⟨History.breakBlock hb, History.firstBreak_pos hb⟩ :
      {a : History P k // 0 < a.stage.val}) =
      ⟨History.breakBlock hd, History.firstBreak_pos hd⟩ :=
    Subtype.ext (History.breakBlock_eq h hb hd)
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

theorem spineMap_edge (c : History P k) {u v : History P k × Fin q}
    (h : (rolling (historyData P)).Adj u v) :
    spineMap c u = spineMap c v ∨ (rolling (historyData P)).Adj (spineMap c u) (spineMap c v) := by
  classical
  let D : RollingData (History P k) (Fin q) := historyData P
  have earlier (x y : History P k × Fin q) (hxy : (rolling D).Adj x y)
      (hpre : x.1.IsPrefix y.1) :
      spineMap c x = spineMap c y ∨ (rolling D).Adj (spineMap c x) (spineMap c y) := by
    by_cases hx : x.1.IsPrefix c
    · rw [spineMap_fixed hx]
      by_cases hy : y.1.IsPrefix c
      · rw [spineMap_fixed hy]
        exact Or.inr hxy
      · have hp : x.1.stage < History.firstBreak hy := by
          by_contra! hn
          have hm := (History.firstBreak_mem hy).2
          rw [← hpre.2 _ hn, hx.2 _ hn] at hm
          exact hm.elim (fun hh => hh.not_ge (hn.trans hx.1)) (fun hh => hh rfl)
        rw [spineMap, dite_eq_right hy]
        let a := History.breakBlock hy
        let d := History.collapseVertex a (History.firstBreak_pos hy)
        change x = d ∨ (rolling D).Adj x d
        by_cases he : x = d
        · exact Or.inl he
        · apply Or.inr
          refine ⟨he, ?_⟩
          by_cases hb : x.1 = d.1
          · exact Or.inl hb
          · refine Or.inr (Or.inl ⟨?_, ?_⟩)
            · have hc : x.1.stage ≤ d.1.stage := by
                change x.1.stage.val ≤ (History.firstBreak hy).val - 1
                have hp' : x.1.stage.val < (History.firstBreak hy).val := hp
                omega
              refine ⟨hc, fun i hi => ?_⟩
              have hi' := hi.trans hp.le
              have hdi := hi.trans hc
              change x.1.step i =
                if i ≤ d.1.stage then (if i ≤ History.firstBreak hy then y.1.step i else _) else _
              rw [if_pos hdi, if_pos hi']
              exact hpre.2 _ hi
            · have hretain := (rolling_earlier D hxy hpre.1).2.resolve_left (fun hz => by
                have hp' := (History.firstBreak_mem hy).1
                exact hp.not_ge (hp'.trans (congrArg History.stage hz).ge))
              have hprefix (b c : History P k) (hbc : b.IsPrefix c) :
                  D.ancestor b c := hbc
              have hdy : d.1.IsPrefix y.1 :=
                D.trans (History.prefix_spec a (Fin.previous a.stage) (Nat.sub_le _ _))
                  (History.prefix_spec y.1 (History.firstBreak hy) (History.firstBreak_mem hy).1)
              exact D.nested (hprefix _ _ hdy) hretain
    · have hy : ¬y.1.IsPrefix c := fun hy => hx (D.trans hpre hy)
      exact Or.inl (spineMap_eq_of_outside hpre hx hy x.2 y.2)
  rcases h.2 with hh | hh | hh
  · exact earlier u v h (hh ▸ D.refl u.1)
  · exact earlier u v h hh.1
  · exact (earlier v u h.symm hh.1).elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)

private theorem spineMap_stable {b c : History P k} (h : b.IsPrefix c)
    (t : Fin (n + 1)) (ht : t.val = b.stage.val + 1) (htc : t ≤ c.stage)
    (v : History P k × Fin q) (hv : ¬(c.prefix t htc).IsPrefix v.1) :
    spineMap b v = spineMap c v := by
  classical
  let D : RollingData (History P k) (Fin q) := historyData P
  by_cases h₁ : v.1.IsPrefix b
  · rw [spineMap_fixed h₁, spineMap_fixed (D.trans h₁ h)]
  have hmin := (History.firstBreak_mem h₁).1
  let i := History.firstBreak h₁
  have hit : i ≤ t := by
    rcases le_total v.1.stage t with hv' | hv'
    · exact hmin.trans hv'
    · exact History.firstBreak_min h₁ ⟨hv', Or.inl (show b.stage < t from Nat.lt_of_succ_le ht.ge)⟩
  have hbefore (s : Fin (n + 1)) (hs : s < i) : s ≤ c.stage ∧ v.1.step s = c.step s := by
    obtain ⟨hh, he⟩ := History.beforeBreak h₁ hs
    exact ⟨hh.trans h.1, he.trans (h.2 s hh)⟩
  have hincompat : v.1.Break c i := by
    refine ⟨hmin, ?_⟩
    by_cases hlt : i < t
    · have hi : i ≤ b.stage := by
        change i.val < t.val at hlt
        exact show i.val ≤ b.stage.val by omega
      have hh := (History.firstBreak_mem h₁).2.resolve_left (not_lt_of_ge hi)
      exact Or.inr fun he => hh (he.trans (h.2 i hi).symm)
    · have he : i = t := le_antisymm hit (le_of_not_gt hlt)
      apply Or.inr
      intro har
      refine hv ⟨he ▸ hmin, fun s hs => ?_⟩
      change s ≤ t at hs
      change (if s ≤ t then c.step s else _) = v.1.step s
      rw [ite_eq_left hs]
      rcases lt_or_eq_of_le hs with hlt' | rfl
      · exact (hbefore s (he ▸ hlt')).2.symm
      · exact (he ▸ har).symm
  have h₂ : ¬v.1.IsPrefix c := fun g =>
    hincompat.2.elim (fun hh => hh.not_ge (hmin.trans g.1)) (fun hh => hh (g.2 i hmin))
  have eq : History.firstBreak h₁ = History.firstBreak h₂ := by
    refine le_antisymm (le_of_not_gt fun hj => ?_) (History.firstBreak_min h₂ hincompat)
    have g := hbefore _ hj
    exact (History.firstBreak_mem h₂).2.elim (fun hh => hh.not_ge g.1) (fun hh => hh g.2)
  simp only [spineMap, dite_eq_right h₁, dite_eq_right h₂]
  have equalBlock : History.breakBlock h₁ = History.breakBlock h₂ :=
    History.ext' eq (by funext s; simp [History.breakBlock, History.prefix, eq])
  have e : (⟨History.breakBlock h₁, History.firstBreak_pos h₁⟩ :
      {a : History P k // 0 < a.stage.val}) =
      ⟨History.breakBlock h₂, History.firstBreak_pos h₂⟩ :=
    Subtype.ext equalBlock
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

private theorem localize_residual {n q k : ℕ} {P : Retention n q}
    (p : History P k × Fin q → Chains (History P k × Fin q)) (R L : ℝ)
    (hp : ∀ v, mass (p v) ≤ L)
    (hs : ∀ (σ : depthAutomorphisms (rolling (historyData P)) (fun v => v.1.stage.val)
      (fun u v => u.1.IsPrefix v.1)) v a b,
      p (σ.val v) (σ.val a, σ.val b) = p v (a,b))
    (hr : ∀ u v, (rolling (historyData P)).Adj u v →
      dualNorm (triangleChain (G := rolling (historyData P)))
        (orientedEdge u v + p u - p v) ≤ R)
    (u v : History P k × Fin q) (huv : (rolling (historyData P)).Adj u v) :
    dualNorm (triangleChain (G := rolling (historyData P)))
      (orientedEdge u v + pushChain (spineMap u.1) (p u) - pushChain (spineMap v.1) (p v)) ≤
       R + 12 * L / (k + 1 : ℝ) := by
  classical
  let G : SimpleGraph (History P k × Fin q) := rolling (historyData P)
  have hL : 0 ≤ L := (Finset.sum_nonneg fun e _ => abs_nonneg (p u e)).trans (hp u)
  have forward (x y : History P k × Fin q) (hxy : G.Adj x y) (hd : x.1.stage ≤ y.1.stage) :
      dualNorm (triangleChain (G := G))
        (orientedEdge x y + pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p y)) ≤
        R + 12 * L / (k + 1 : ℝ) := by
    have hpre := (rolling_earlier _ hxy hd).1
    let tChain := triangleChain (G := G)
    have hpush := dualNorm_pushChain_le (spineMap y.1)
      (fun _ _ e => spineMap_edge y.1 e) (orientedEdge x y + p x - p y)
    rw [pushChain_sub, pushChain_add, pushChain_edge, spineMap_fixed hpre,
      spineMap_fixed ((historyData P).refl y.1)] at hpush
    by_cases hEq : x.1.stage = y.1.stage
    · have he := History.IsPrefix.eq_of_stage_eq hpre hEq
      rw [he]
      exact (hpush.trans (hr x y hxy)).trans
        (le_add_of_nonneg_right (by positivity))
    · have hlt := lt_of_le_of_ne hd hEq
      let i : Fin (n + 1) := ⟨x.1.stage.val + 1, (Nat.succ_le_of_lt hlt).trans_lt y.1.stage.isLt⟩
      have hi : i ≤ y.1.stage := Nat.succ_le_of_lt hlt
      let S := Finset.univ.filter (fun v : History P k × Fin q =>
        i ≤ v.1.stage ∧ (v.1.step i).2 = (y.1.step i).2)
      have hstay (z : History P k × Fin q) (hz : z ∉ S) : spineMap x.1 z = spineMap y.1 z := by
        apply spineMap_stable hpre i rfl hi z
        intro h
        apply hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1,
          (congrArg Prod.snd (h.2 i le_rfl)).symm.trans (by simp [History.prefix])⟩
      have hm := clone_load_le p L hp hs x i (show x.1.stage.val < i.val from Nat.lt_succ_self _) (y.1.step i).2
      have herr := (dualNorm_push_change tChain (spineMap x.1) (spineMap y.1) (p x) S hstay).trans
        (mul_le_mul_of_nonneg_left hm (by norm_num))
      have he : orientedEdge x y + pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p y) =
          (orientedEdge x y + pushChain (spineMap y.1) (p x) - pushChain (spineMap y.1) (p y)) +
          (pushChain (spineMap x.1) (p x) - pushChain (spineMap y.1) (p x)) := by abel
      rw [he]
      have h₁ := hpush.trans (hr x y hxy)
      have h₂ : dualNorm tChain (pushChain (spineMap x.1) (p x) -
          pushChain (spineMap y.1) (p x)) ≤ 12 * L / (k + 1 : ℝ) :=
        herr.trans (by ring_nf; rfl)
      exact (dualNorm_add_le tChain _ _).trans (add_le_add h₁ h₂)
  rcases le_total u.1.stage v.1.stage with hd | hd
  · exact forward u v huv hd
  · rw [show orientedEdge u v + pushChain (spineMap u.1) (p u) - pushChain (spineMap v.1) (p v) =
        -(orientedEdge v u + pushChain (spineMap v.1) (p v) - pushChain (spineMap u.1) (p u)) by
      rw [orientedEdge_reverse v u]
      abel, dualNorm_neg_eq]
    exact forward v u huv.symm hd

end SpineRetraction

section LocalizedPotential

variable {n q k : ℕ} {P : Retention n q}

abbrev histGraph (P : Retention n q) (k : ℕ) : SimpleGraph (HV P k) :=
  rolling (historyData P)

abbrev histDepth (v : HV P k) : ℕ := v.1.stage.val

abbrev histPre (u v : HV P k) : Prop := u.1.IsPrefix v.1

structure Localized (P : Retention n q) (k : ℕ) (R L : ℝ) where
  chain : HV P k → Chains (HV P k)
  boundary_eq (v : HV P k) : boundary (chain v) = Pi.single v 1 - rootMass
  mass_le (v : HV P k) : mass (chain v) ≤ L
  support (v a b : HV P k) :
    ¬(histPre a v ∧ histPre b v ∧ (a = b ∨ (histGraph P k).Adj a b)) → chain v (a,b) = 0
  residual (u v : HV P k) : (histGraph P k).Adj u v →
    dualNorm (triangleChain (G := histGraph P k)) (orientedEdge u v + chain u - chain v) ≤ R
  equivariant (σ : depthAutomorphisms (histGraph P k) histDepth histPre) (v a b : HV P k) :
    chain (σ.val v) (σ.val a, σ.val b) = chain v (a,b)

private theorem History.initial_prefix (b : History P k) : (History.initial P).IsPrefix b := by
  refine ⟨Fin.zero_le _, fun i hi => ?_⟩
  have he : i = 0 := le_antisymm hi (Fin.zero_le _)
  simp [he, History.initial, b.root_step]

private theorem spine_push_boundary (v : HV P k) (c : Chains (HV P k))
    (h : boundary c = Pi.single v 1 - rootMass) :
    boundary (pushChain (spineMap v.1) c) = boundary c := by
  classical
  funext x
  rw [pushChain_boundary, h]
  have he (a : HV P k) :
      (if spineMap v.1 a = x then (Pi.single (M := fun _ : HV P k => ℝ) v 1 a - rootMass a) else 0) =
      if a = x then (Pi.single (M := fun _ : HV P k => ℝ) v 1 a - rootMass a) else 0 := by
    by_cases hv : a = v
    · subst a
      rw [spineMap_fixed ((historyData P).refl v.1)]
    · by_cases hr : a.1.stage = 0
      · rw [spineMap_fixed (by rw [History.stage_zero hr]; exact History.initial_prefix _)]
      · simp [rootMass, hr, Pi.single_apply, hv]
  simp only [Pi.sub_apply, he]
  simp

private theorem spine_push_support (v a b : HV P k) (c : Chains (HV P k))
    (hs : Supported (histGraph P k) c)
    (hn : ¬(histPre a v ∧ histPre b v ∧ (a = b ∨ (histGraph P k).Adj a b))) :
    pushChain (spineMap v.1) c (a,b) = 0 := by
  classical
  unfold pushChain
  simp only [Finset.sum_apply, Pi.single_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : (a,b) = (spineMap v.1 e.1, spineMap v.1 e.2)
  · rw [if_pos he]
    apply hs e
    intro ed
    apply hn
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    change a = _ at ha
    change b = _ at hb
    rw [ha,hb]
    exact ⟨spineMap_on_spine _ _, spineMap_on_spine _ _, spineMap_edge _ ed⟩
  · simp [he]

theorem obtain_localized (hq : 0 < q) (R : ℝ) (hR : R ≤ 4) (o : HV P k)
    (p : HV P k → Chains (HV P k))
    (hp : ∀ v, Supported (histGraph P k) (p v))
    (hb : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1)
    (hr : ∀ u v, (histGraph P k).Adj u v →
      dualNorm (triangleChain (G := histGraph P k)) (orientedEdge u v + p u - p v) ≤ R) :
    Nonempty (Localized P k (R + 12 * (13 * (n + 1)) / (k + 1 : ℝ)) (13 * (n + 1))) := by
  classical
  let G := histGraph P k
  let L : ℝ := 13 * (n + 1)
  let p₀ := centerRoot p
  have ps (v : HV P k) : Supported G (p₀ v) := by
    intro e he
    simp [p₀, centerRoot, meanChain, hp _ _ he]
  have pb (v : HV P k) : boundary (p₀ v) = Pi.single v 1 - rootMass :=
    centerRoot_boundary hq o p hb v
  have pm (v : HV P k) : mass (p₀ v) ≤ L := centerRoot_mass hq R hR p hr v
  have pr (u v : HV P k) (e : G.Adj u v) :
      dualNorm (triangleChain (G := G)) (orientedEdge u v + p₀ u - p₀ v) ≤ R := by
    convert hr u v e using 1
    unfold p₀ centerRoot
    abel
  have mu (σ : depthAutomorphisms G histDepth histPre) (v : HV P k) :
      rootMass (σ.val v) = rootMass v := by
    unfold rootMass
    have hd := σ.property.2.1 v
    change (σ.val v).1.stage.val = v.1.stage.val at hd
    rw [Fin.ext hd]
  let pp := symmetrize G histDepth histPre p₀
  let P₀ (v : HV P k) := pushChain (spineMap v.1) (pp v)
  have wb (v : HV P k) : boundary (P₀ v) = Pi.single v 1 - rootMass := by
    have he := symmetrize_boundary G histDepth histPre p₀ rootMass pb mu v
    exact (spine_push_boundary v _ he).trans he
  have wm (v : HV P k) : mass (P₀ v) ≤ L :=
    (mass_pushChain _ _).trans (symmetrize_mass_le G histDepth histPre p₀ L pm v)
  have wr (u v : HV P k) (e : G.Adj u v) :
      dualNorm (triangleChain (G := G)) (orientedEdge u v + P₀ u - P₀ v) ≤
      R + 12 * L / (k + 1 : ℝ) :=
    localize_residual pp R L (symmetrize_mass_le G histDepth histPre p₀ L pm)
      (symmetrize_equivariant G histDepth histPre p₀) (symmetrize_residual_le G histDepth histPre p₀ R pr)
      u v e
  refine ⟨⟨symmetrize G histDepth histPre P₀,
    symmetrize_boundary G histDepth histPre P₀ rootMass wb mu,
    symmetrize_mass_le G histDepth histPre P₀ L wm, ?_,
    symmetrize_residual_le G histDepth histPre P₀ _ wr,
    symmetrize_equivariant G histDepth histPre P₀⟩⟩
  intro v a b hn
  unfold symmetrize
  have hw (σ : depthAutomorphisms G histDepth histPre) : P₀ (σ.val v) (σ.val a,σ.val b) = 0 := by
    apply spine_push_support _ _ _ _ (symmetrize_supported G histDepth histPre p₀ ps _)
    intro h
    exact hn ⟨(σ.property.2.2 _ _).mp h.1, (σ.property.2.2 _ _).mp h.2.1,
      h.2.2.imp (fun e => σ.val.injective e) ((σ.property.1 _ _).mp)⟩
  simp [hw]

end LocalizedPotential

end

end Omega.RollingCliques
