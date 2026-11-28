/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalBanachSharpFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rolling clique separators force Banach gain reconstruction errors approaching four. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import D5.S3.Combinatorics.Graph.AncestralChainLocalization
import D5.S3.Combinatorics.Graph.PeriodicBandCochains

namespace SimpleGraph.ChordalReconstruction

open Omega.GraphChains Omega.RollingCliques Omega.PeriodicBandCochains
open scoped BigOperators

noncomputable section

variable {B X : Type*} [Fintype B] [Fintype X] in
private theorem rolling_chordal (D : RollingData B X) : (rolling D).IsChordal := by
  classical
  intro x c hc hl
  obtain ⟨v, hv, hmax⟩ :=
    Finset.exists_max_image c.support.toFinset (fun u => D.depth u.1) ⟨x, by simp⟩
  have hmem : v ∈ c.support := by simpa using hv
  let d := c.rotate v hmem
  have hd : d.IsCycle := hc.rotate hmem
  have hn : 4 ≤ d.length := by simpa [d] using hl
  have support (u : B × X) (hu : u ∈ d.support) : u ∈ c.support := by
    rw [← Walk.cons_tail_support] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hmem
    · exact List.mem_of_mem_tail ((c.support_rotate v hmem).mem_iff.mp hu)
  have hs := support d.snd (d.getVert_mem_support 1)
  have hp := support d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hs, hp, rolling_clique D v
    ⟨hmax _ (by simpa using hs), (d.adj_snd hd.not_nil).symm⟩
    ⟨hmax _ (by simpa using hp), d.adj_penultimate hd.not_nil⟩
    hd.snd_ne_penultimate, ?_⟩
  intro edge
  have mem := Walk.adj_toSubgraph_iff_mem_edges.mpr ((c.rotate_edges v hmem).mem_iff.mpr edge)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at mem
  rw [hd.neighborSet_toSubgraph_internal (by omega) (by omega)] at mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.sub_self] at mem
  rcases mem with hm | hm <;>
    have eq := hd.getVert_injOn' (by simp : d.length - 1 ∈ {n | n ≤ d.length - 1})
      (by simp <;> omega) hm <;> omega

private theorem band_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ ((m : ℝ) + 2) * (4 - ε / 2) <
      (m : ℝ) * (4 - 2 / (m : ℝ)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (20 / ε))
  have h₁ : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have h₂ : (20 : ℝ) < m * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hm)
  have hm' : (m : ℝ) ≠ 0 := by linarith
  have he : (m : ℝ) * (4 - 2 / (m : ℝ)) = 4 * (m : ℝ) - 2 := by
    field_simp
  refine ⟨m, by exact_mod_cast h₁.le, ?_⟩
  rw [he]
  nlinarith

private theorem band_contradiction (ε : ℝ) {m : ℕ}
    (hm : 1 ≤ m) (hparam : ((m : ℝ) + 2) * (4 - ε / 2) <
      (m : ℝ) * (4 - 2 / (m : ℝ)))
    (H : Fin m → ℕ → ℝ) (hH : ∀ t, ∑ r, H r t = 0)
    (bound : ∀ (r : Fin m) (u v : ℕ), u < v → v ≤ u + m → v ≤ m * m + m + 1 →
      2 + band r u v + H r u - H r v ≤ (4 - ε) + ε / 2) : False := by
  have h := band_average (n := m) (show 0 < m by omega) H hH (4 - ε) (ε / 2) bound
  rw [show (4 - ε) + ε / 2 = 4 - ε / 2 by ring] at h
  exact hparam.not_ge h

section Ages

variable {w n M k : ℕ} {hw : 1 ≤ w} {hM : 1 ≤ M}

private abbrev RollingHistory (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :=
  History (concreteRetention w n M hw hM) k

private abbrev RollingVertex (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :=
  RollingHistory hw hM n k × Fin (M ^ (w + 2))

private abbrev RollingG (hw : 1 ≤ w) (hM : 1 ≤ M) (n k : ℕ) :
    SimpleGraph (RollingVertex hw hM n k) :=
  rolling (historyData (concreteRetention w n M hw hM))

private noncomputable def liveStages (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ≤ c.stage ∧ v.2 ∈ (c.step i).1 v.1.stage

private noncomputable def age (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    ℕ :=
  (liveStages c v).sup Fin.val

private theorem age_ge_of_live {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (i : Fin (n + 1)) (hi : i ≤ c.stage) (h : v.2 ∈ (c.step i).1 v.1.stage) :
    i.val ≤ age c v :=
  Finset.le_sup (f := Fin.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, h⟩)

private theorem age_le_stage (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    age c v ≤ c.stage.val := by
  apply Finset.sup_le
  intro i hi
  exact (Finset.mem_filter.mp hi).2.1

private theorem age_le_span (c : RollingHistory hw hM n k) (v : RollingVertex hw hM n k) :
    age c v ≤ v.1.stage.val + w := by
  apply Finset.sup_le
  intro i hi
  have ⟨hs, hm⟩ := (Finset.mem_filter.mp hi).2
  by_contra! hn
  have he := c.cardinal v.1.stage i hs
  change ((c.step i).1 v.1.stage).card = quota w M v.1.stage.val i.val at he
  rw [quota, ite_eq_right (not_le_of_gt hn)] at he
  exact (Finset.card_pos.mpr ⟨_, hm⟩).ne' he

private theorem birth_live {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) : v.2 ∈ (c.step v.1.stage).1 v.1.stage := by
  have he := c.cardinal v.1.stage v.1.stage hv.1
  change ((c.step v.1.stage).1 v.1.stage).card = quota w M v.1.stage.val v.1.stage.val at he
  have hb : v.1.stage.val ≤ v.1.stage.val + w := by omega
  have hc : ((c.step v.1.stage).1 v.1.stage).card = Fintype.card (Fin (M ^ (w + 2))) := by
    simpa [quota, hb] using he
  have hfull : (c.step v.1.stage).1 v.1.stage = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa [hc])
  rw [hfull]
  exact Finset.mem_univ _

private theorem birth_le_age {c : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) : v.1.stage.val ≤ age c v :=
  age_ge_of_live v.1.stage hv.1 (birth_live hv)

private theorem age_ge_of_adj {c : RollingHistory hw hM n k} {u v : RollingVertex hw hM n k}
    (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v)
    (hstage : u.1.stage ≤ v.1.stage) : v.1.stage.val ≤ age c u := by
  obtain ⟨hu, he | hr⟩ := rolling_earlier _ h hstage
  · exact (congrArg (fun b => (History.stage b).val) he) ▸ birth_le_age
      ((historyData (concreteRetention w n M hw hM)).trans hu hv)
  · apply age_ge_of_live v.1.stage hv.1
    rw [← hv.2 v.1.stage le_rfl]
    exact hr

private theorem age_edge {c : RollingHistory hw hM n k} {u v : RollingVertex hw hM n k}
    (hu : u.1.IsPrefix c) (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v) :
    tagPair w 0 0 (.inl (age c u)) (.inl (age c v)) := by
  rcases le_total u.1.stage v.1.stage with h₀ | h₀
  · have h₁ := age_ge_of_adj hv h h₀
    have h₂ := birth_le_age hv
    have h₃ := age_le_span c u
    have h₄ := age_le_span c v
    change u.1.stage.val ≤ v.1.stage.val at h₀
    exact ⟨by omega, by omega⟩
  · have h₁ := age_ge_of_adj hu h.symm h₀
    have h₂ := birth_le_age hu
    have h₃ := age_le_span c u
    have h₄ := age_le_span c v
    change v.1.stage.val ≤ u.1.stage.val at h₀
    exact ⟨by omega, by omega⟩

private def tagAge (c : RollingHistory hw hM n k) (x y v : RollingVertex hw hM n k) :
    Tags := by
  classical
  exact if v = x then .inr false else if v = y then .inr true else .inl (age c v)

private theorem tagged_age_edge {c : RollingHistory hw hM n k} {x y u v : RollingVertex hw hM n k}
    (hx : x.1.IsPrefix c) (hy : y.1 = c) (hxy : x ≠ y)
    (hu : u.1.IsPrefix c) (hv : v.1.IsPrefix c) (h : (RollingG hw hM n k).Adj u v) :
    tagPair w x.1.stage.val c.stage.val (tagAge c x y u) (tagAge c x y v) := by
  classical
  have ageAdj (z t : RollingVertex hw hM n k) (hz : z.1.IsPrefix c) (ht : t.1.IsPrefix c)
      (hzt : (RollingG hw hM n k).Adj z t) :
      z.1.stage.val ≤ age c t := by
    rcases le_total z.1.stage t.1.stage with h' | h'
    · exact (show z.1.stage.val ≤ t.1.stage.val from h').trans (birth_le_age ht)
    · exact age_ge_of_adj hz hzt.symm h'
  have ageX (z : RollingVertex hw hM n k) (hz : z.1.IsPrefix c)
      (hadj : (RollingG hw hM n k).Adj x z) :
      x.1.stage.val ≤ age c z ∧ age c z ≤ c.stage.val :=
    ⟨ageAdj _ _ hx hz hadj, age_le_stage _ _⟩
  have hyP : y.1.IsPrefix c := hy.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have ageY (z : RollingVertex hw hM n k) (hz : z.1.IsPrefix c)
      (hadj : (RollingG hw hM n k).Adj y z) : age c z = c.stage.val :=
    le_antisymm (age_le_stage _ _) (by simpa only [hy] using ageAdj _ _ hyP hz hadj)
  by_cases hux : u = x
  · subst u
    by_cases hvy : v = y
    · subst v
      simp [tagAge, hxy, Ne.symm hxy, tagPair]
    · have hvx : v ≠ x := fun he => h.ne he.symm
      simpa [tagAge, hvx, hvy, tagPair] using ageX v hv h
  by_cases huy : u = y
  · subst u
    by_cases hvx : v = x
    · subst v
      simp [tagAge, hxy, Ne.symm hxy, tagPair]
    · have hvy : v ≠ y := fun he => h.ne he.symm
      simpa [tagAge, hux, hvx, hvy, tagPair] using ageY v hv h
  by_cases hvx : v = x
  · subst v
    simpa [tagAge, hux, huy, tagPair] using ageX u hu h.symm
  by_cases hvy : v = y
  · subst v
    simpa [tagAge, hux, huy, hvx, tagPair] using ageY u hu h.symm
  rw [tagAge, ite_eq_right hux, ite_eq_right huy, tagAge, ite_eq_right hvx, ite_eq_right hvy]
  exact age_edge hu hv h

private theorem alive_swap {c : RollingHistory hw hM n k} {b : RollingHistory hw hM n k}
    (hbc : b.IsPrefix c) {s t : Fin (M ^ (w + 2))}
    (hs : s ∈ (c.step c.stage).1 b.stage) (ht : t ∈ (c.step c.stage).1 b.stage) :
    ∃ σ : depthAutomorphisms (RollingG hw hM n k) histDepth histPre,
      (∀ a : RollingHistory hw hM n k, a.IsPrefix c → (σ.val (a,s)).1 = a) ∧
      σ.val (b,s) = (b,t) ∧
      (∀ a : RollingVertex hw hM n k, a.1.IsPrefix c →
        (a.1.stage ≠ b.stage ∨ (a.2 ≠ s ∧ a.2 ≠ t)) → σ.val a = a) ∧
      (∀ a : RollingVertex hw hM n k, a.1.IsPrefix c → age c (σ.val a) = age c a) := by
  classical
  let π : Fin (n+1) → Equiv.Perm (Fin (M^(w+2))) :=
    Function.update (fun _ => 1) b.stage (Equiv.swap s t)
  let σ : Equiv.Perm (RollingVertex hw hM n k) := labelPerm π
  have fixHistory (a : RollingHistory hw hM n k) (ha : a.IsPrefix c) : a.relabel π = a := by
    refine History.ext' (b := a.relabel π) (c := a) rfl ?_
    funext i
    by_cases hi : i ≤ a.stage
    · change relabelStep π (a.step i) = a.step i
      apply Prod.ext
      · funext j
        ext x
        simp only [relabelStep, Finset.mem_map_equiv]
        by_cases hj : j = b.stage
        · subst j
          have hsi : s ∈ (a.step i).1 b.stage := by
            rw [ha.2 i hi]
            exact c.nested _ _ _ (hi.trans ha.1) le_rfl hs
          have hti : t ∈ (a.step i).1 b.stage := by
            rw [ha.2 i hi]
            exact c.nested _ _ _ (hi.trans ha.1) le_rfl ht
          simp only [π, Function.update_self, Equiv.symm_swap]
          by_cases hxs : x = s
          · subst x
            simp [hsi, hti]
          · by_cases hxt : x = t
            · subst x
              simp [hsi, hti]
            · simp [Equiv.swap_apply_of_ne_of_ne hxs hxt]
        · simp [π, Function.update_of_ne hj, Equiv.Perm.one_def]
      · rfl
    · rw [(a.relabel π).beyond i (lt_of_not_ge hi), a.beyond i (lt_of_not_ge hi)]
  let τ : depthAutomorphisms (RollingG hw hM n k) histDepth histPre :=
    ⟨σ, labelPerm_adj π, (fun _ => rfl), fun _ _ => History.relabel_prefix π⟩
  refine ⟨τ, fun a ha => fixHistory a ha, ?_, ?_, ?_⟩
  · apply Prod.ext (fixHistory b hbc)
    simp [τ, σ, labelPerm, π]
  · intro a ha h
    apply Prod.ext (fixHistory a.1 ha)
    rcases h with hj | ⟨h₁,h₂⟩
    · simp [τ, σ, labelPerm, π, Function.update_of_ne hj]
    · by_cases hj : a.1.stage = b.stage
      · simp [τ, σ, labelPerm, π, hj, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
      · simp [τ, σ, labelPerm, π, Function.update_of_ne hj]
  · intro a ha
    have e := fixHistory a.1 ha
    unfold age
    congr 1
    ext i
    simp only [liveStages, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show (σ a).1 = a.1 from e]
    constructor <;> rintro ⟨hi,hx⟩ <;> refine ⟨hi, ?_⟩ <;>
      by_cases hj : a.1.stage = b.stage
    · change (π a.1.stage a.2) ∈ _ at hx
      rw [hj] at hx ⊢
      have hs' := c.nested b.stage i c.stage hi le_rfl hs
      have ht' := c.nested b.stage i c.stage hi le_rfl ht
      by_cases h₁ : a.2 = s
      · simpa [h₁] using hs'
      · by_cases h₂ : a.2 = t
        · simpa [h₂] using ht'
        · simpa [π, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hx
    · simpa [τ, σ, labelPerm, π, Function.update_of_ne hj] using hx
    · change (π a.1.stage a.2) ∈ _
      rw [hj] at hx ⊢
      have hs' := c.nested b.stage i c.stage hi le_rfl hs
      have ht' := c.nested b.stage i c.stage hi le_rfl ht
      by_cases h₁ : a.2 = s
      · simpa [h₁, π] using ht'
      · by_cases h₂ : a.2 = t
        · simpa [h₂, π] using hs'
        · simpa [π, Equiv.swap_apply_of_ne_of_ne h₁ h₂] using hx
    · simpa [τ, σ, labelPerm, π, Function.update_of_ne hj] using hx

private theorem sum_const_subset_bound {V : Type*} [DecidableEq V] (u : V → ℝ)
    (S T : Finset V) (M : ℕ) (hM : 0 < M)
    (hsub : T ⊆ S) (hcard : M * T.card ≤ S.card) (hpos : ∀ v, 0 ≤ u v)
    (hc : ∀ a ∈ S, ∀ b ∈ S, u a = u b) :
    ∑ v ∈ T, u v ≤ (∑ v ∈ S, u v) / M := by
  by_cases hs : S.Nonempty
  · obtain ⟨v,hv⟩ := hs
    have h₁ : ∑ i ∈ S, u i = (S.card : ℝ) * u v := by
      calc
        _ = ∑ i ∈ S, u v := Finset.sum_congr rfl fun i hi => hc i hi v hv
        _ = _ := by simp
    have h₂ : ∑ i ∈ T, u i = (T.card : ℝ) * u v := by
      calc
        _ = ∑ i ∈ T, u v := Finset.sum_congr rfl fun i hi => hc i (hsub hi) v hv
        _ = _ := by simp
    rw [h₁, h₂, le_div_iff₀ (Nat.cast_pos.mpr hM)]
    have hℝ : (M : ℝ) * T.card ≤ S.card := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hℝ (hpos v)]
  · have hse := Finset.not_nonempty_iff_eq_empty.mp hs
    have hte : T = ∅ := Finset.subset_empty.mp (hse ▸ hsub)
    simp [hte, hse]

private def retainedVertices (c b : RollingHistory hw hM n k) :
    Finset (RollingVertex hw hM n k) :=
  ((c.step c.stage).1 b.stage).map ⟨Prod.mk b, fun _ _ h => congrArg Prod.snd h⟩

private theorem mem_retainedVertices {c b : RollingHistory hw hM n k} {v : RollingVertex hw hM n k} :
    v ∈ retainedVertices c b ↔ v.1 = b ∧ v.2 ∈ (c.step c.stage).1 b.stage := by
  simp only [retainedVertices, Finset.mem_map]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨h,ha⟩
    exact ⟨v.2,ha,Prod.ext h.symm rfl⟩

private theorem surviving_load_const {R L : ℝ} {c b : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hb : b.IsPrefix c)
    {u v : RollingVertex hw hM n k}
    (hu : u ∈ (retainedVertices c b).erase x) (hv : v ∈ (retainedVertices c b).erase x) :
    load (P.chain x) u = load (P.chain x) v := by
  obtain ⟨hun,hum⟩ := Finset.mem_erase.mp hu
  obtain ⟨hvn,hvm⟩ := Finset.mem_erase.mp hv
  obtain ⟨hu',hu''⟩ := mem_retainedVertices.mp hum
  obtain ⟨hv',hv''⟩ := mem_retainedVertices.mp hvm
  obtain ⟨σ,_,hm,hfix,_⟩ := alive_swap hb hu'' hv''
  have hxc : x.1.IsPrefix c := hx.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have hfx : σ.val x = x := by
    apply hfix x hxc
    by_cases hi : x.1.stage = b.stage
    · have he : b = x.1 := History.IsPrefix.eq_of_stage_eq (hx ▸ hb) hi.symm
      right
      exact ⟨fun h => hun (Prod.ext (hu'.trans he) h.symm),
        fun h => hvn (Prod.ext (hv'.trans he) h.symm)⟩
    · exact Or.inl hi
  have huv : σ.val u = v := by
    rw [show u = (b,u.2) from Prod.ext hu' rfl, hm]
    exact Prod.ext hv'.symm rfl
  have h := invariant_load σ.val (P.chain x) (fun a b => by
    have e := P.equivariant σ x a b
    rwa [hfx] at e) u
  rw [huv] at h
  exact h.symm

private theorem retentions_shrink {b c d : RollingHistory hw hM n k}
    (hbc : b.IsPrefix c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) :
    M * (retainedVertices d b).card ≤ (retainedVertices c b).card := by
  rw [retainedVertices, retainedVertices, Finset.card_map, Finset.card_map,
    d.cardinal b.stage d.stage le_rfl, c.cardinal b.stage c.stage le_rfl]
  change M * quota w M b.stage.val d.stage.val ≤ quota w M b.stage.val c.stage.val
  rw [ht]
  by_cases h : c.stage.val + 1 ≤ b.stage.val + w
  · exact (quota_step w M _ _ hbc.1 h).symm.le
  · simp [quota, h]

private theorem retained_subset {b c d : RollingHistory hw hM n k}
    (hcd : c.IsPrefix d) : retainedVertices d b ⊆ retainedVertices c b := by
  intro v hv
  obtain ⟨he,h⟩ := mem_retainedVertices.mp hv
  refine mem_retainedVertices.mpr ⟨he, ?_⟩
  rw [hcd.2 c.stage le_rfl]
  exact d.nested b.stage c.stage d.stage hcd.1 le_rfl h

private theorem refined_load_by_block {R L : ℝ} {b c d : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hbc : b.IsPrefix c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) (hx' : x ∈ retainedVertices d c) :
    ∑ y ∈ (retainedVertices d b).erase x, load (P.chain x) y ≤
      (∑ y ∈ (retainedVertices c b).erase x, load (P.chain x) y) / M := by
  classical
  apply sum_const_subset_bound _ _ _ M (by omega)
  · exact Finset.erase_subset_erase x (retained_subset hcd)
  · have h := retentions_shrink hbc hcd ht
    by_cases hs : x ∈ retainedVertices c b
    · have he : c = b := hx.symm.trans (mem_retainedVertices.mp hs).1
      have ht' : x ∈ retainedVertices d b := he ▸ hx'
      rw [Finset.card_erase_of_mem ht', Finset.card_erase_of_mem hs]
      have hh := Finset.card_pos.mpr ⟨x, ht'⟩
      have hm : 0 < M := by omega
      calc
        M * ((retainedVertices d b).card - 1) = M * (retainedVertices d b).card - M :=
          by rw [Nat.mul_sub, Nat.mul_one]
        _ ≤ (retainedVertices c b).card - 1 := by omega
    · have ht' : x ∉ retainedVertices d b := fun hm => hs (retained_subset hcd hm)
      rwa [Finset.erase_eq_of_notMem ht', Finset.erase_eq_of_notMem hs]
  · exact load_nonneg _
  · exact fun a ha b hb => surviving_load_const P x hx hbc ha hb

private theorem age_stable {c d : RollingHistory hw hM n k} {v : RollingVertex hw hM n k}
    (hcd : c.IsPrefix d) (t : Fin (n + 1)) (ht : t.val = c.stage.val + 1)
    (htd : t ≤ d.stage) (hn : v.2 ∉ (d.step t).1 v.1.stage) :
    age d v = age c v := by
  have hSet : liveStages d v = liveStages c v := by
    ext i
    simp only [liveStages, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hv⟩
      have hic : i ≤ c.stage := by
        by_contra! hlt
        have hti : t ≤ i := by
          change c.stage.val < i.val at hlt
          exact show t.val ≤ i.val by omega
        exact hn (d.nested _ _ _ hti hi hv)
      exact ⟨hic, hcd.2 i hic ▸ hv⟩
    · rintro ⟨hi,hv⟩
      exact ⟨hi.trans hcd.1, hcd.2 i hi ▸ hv⟩
  simp [age, hSet]

private theorem child_load_bound {R L : ℝ} {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hy : y.1 = c)
    (hb : b.IsPrefix c) (hdepth : b.stage < c.stage)
    (hspan : c.stage.val ≤ b.stage.val + w) (hx : x ∈ retainedVertices c b) :
    load (P.chain y) x ≤ 2 * L / M := by
  classical
  have hy' : y ∉ retainedVertices c b := fun hm =>
    hdepth.ne (congrArg History.stage ((mem_retainedVertices.mp hm).1.symm.trans hy))
  have hset : (retainedVertices c b).erase y = retainedVertices c b := Finset.erase_eq_of_notMem hy'
  have hs : ∀ a ∈ retainedVertices c b, load (P.chain y) a = load (P.chain y) x := fun a ha =>
    surviving_load_const P y hy hb (hset.symm ▸ ha) (hset.symm ▸ hx)
  have hcard : M ≤ (retainedVertices c b).card := by
    rw [retainedVertices, Finset.card_map, c.cardinal _ _ le_rfl]
    change M ≤ quota w M b.stage.val c.stage.val
    simp only [quota, hspan, ite_true]
    simpa using pow_le_pow_right' hM
      (show 1 ≤ w + 2 - (c.stage.val - b.stage.val) by omega)
  have hsum : ∑ a ∈ retainedVertices c b, load (P.chain y) a ≤ 2 * L := by
    calc
      _ ≤ ∑ a, load (P.chain y) a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => load_nonneg _ a)
      _ ≤ _ := by rw [sum_load]; exact mul_le_mul_of_nonneg_left (P.mass_le y) (by norm_num)
  have hEval : ∑ a ∈ retainedVertices c b, load (P.chain y) a =
      ((retainedVertices c b).card : ℝ) * load (P.chain y) x := by
    calc
      _ = ∑ a ∈ retainedVertices c b, load (P.chain y) x :=
        Finset.sum_congr rfl hs
      _ = _ := by simp
  rw [hEval] at hsum
  apply (le_div_iff₀ (show (0 : ℝ) < M by exact_mod_cast (show 0 < M by omega))).2
  have hcard' : (M : ℝ) ≤ (retainedVertices c b).card := by exact_mod_cast hcard
  exact (by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hcard' (load_nonneg _ _)).trans hsum)

private def retentionError (c d : RollingHistory hw hM n k) (x : RollingVertex hw hM n k) :
    Finset (RollingVertex hw hM n k) := by
  classical
  exact (Finset.univ.filter fun b : RollingHistory hw hM n k => b.IsPrefix c).biUnion
    (fun b => (retainedVertices d b).erase x)

private theorem retentionError_load_bound {R L : ℝ} {c d : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x : RollingVertex hw hM n k) (hx : x.1 = c) (hcd : c.IsPrefix d)
    (ht : d.stage.val = c.stage.val + 1) (hx' : x ∈ retainedVertices d c) :
    ∑ a ∈ retentionError c d x, load (P.chain x) a ≤ 2 * L / M := by
  classical
  let S := Finset.univ.filter fun b : RollingHistory hw hM n k => b.IsPrefix c
  have disj (e : RollingHistory hw hM n k) :
      (↑S : Set _).PairwiseDisjoint (fun b => (retainedVertices e b).erase x) := by
    intro a _ b _ hne
    apply Finset.disjoint_left.mpr
    intro z ha hb
    have ha' := (mem_retainedVertices.mp (Finset.mem_erase.mp ha).2).1
    have hb' := (mem_retainedVertices.mp (Finset.mem_erase.mp hb).2).1
    exact hne (ha'.symm.trans hb')
  change ∑ a ∈ S.biUnion _, load (P.chain x) a ≤ _
  rw [Finset.sum_biUnion (disj d)]
  calc
    _ ≤ ∑ b ∈ S, (∑ a ∈ (retainedVertices c b).erase x, load (P.chain x) a) / M :=
      Finset.sum_le_sum fun b hb =>
        refined_load_by_block P x hx (Finset.mem_filter.mp hb).2 hcd ht hx'
    _ = (∑ a ∈ S.biUnion (fun b => (retainedVertices c b).erase x), load (P.chain x) a) / M := by
      rw [Finset.sum_biUnion (disj c)]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => load_nonneg _ a)).trans ?_
      rw [sum_load]
      exact mul_le_mul_of_nonneg_left (P.mass_le x) (by norm_num)

private def ageCochain (r : Fin w) (b : RollingHistory hw hM n k) :
    Chains (RollingVertex hw hM n k) :=
  fun e => band r (age b e.1) (age b e.2)

private def testCochain (r : Fin w) (i : ℕ) (b : RollingHistory hw hM n k)
    (x y : RollingVertex hw hM n k) : Chains (RollingVertex hw hM n k) :=
  fun e => tagValue r i (tagAge b x y e.1) (tagAge b x y e.2)

private theorem testCochain_skew (r : Fin w) (i : ℕ) (b : RollingHistory hw hM n k)
    (x y u v : RollingVertex hw hM n k) : testCochain r i b x y (v,u) =
      -testCochain r i b x y (u,v) :=
  tagValue_skew r i _ _

private theorem testCochain_eval_residual {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val+w)
    (hedge : (RollingG hw hM n k).Adj x y) :
    1 + pairing (testCochain r c.stage.val c x y) (P.chain x) -
      pairing (testCochain r c.stage.val c x y) (P.chain y) ≤ R := by
  classical
  let G := RollingG hw hM n k
  let F := testCochain r c.stage.val c x y
  let f := pullCochain (spineMap c) F
  have hf : ∀ u v, f (v,u) = -f (u,v) := fun _ _ => testCochain_skew _ _ _ _ _ _ _
  have h₁ : Admissible (triangleChain (G := G)) f := by
    refine ⟨fun e => tagValue_abs _ _ _ _, fun ⟨⟨u,v,z⟩,huv,hvz,huz⟩ => ?_⟩
    change |pairing f (orientedEdge u v + orientedEdge v z - orientedEdge u z)| ≤ 1
    rw [pairing_triangle f hf]
    have hP (a d : RollingVertex hw hM n k) (e : G.Adj a d) :
        tagPair w b.stage.val c.stage.val (tagAge c x y (spineMap c a)) (tagAge c x y (spineMap c d)) := by
      rcases spineMap_edge c e with he | he
      · rw [he]
        cases tagAge c x y (spineMap c d)
        · exact ⟨by omega, by omega⟩
        · rename_i a
          cases a <;> trivial
      · have h := tagged_age_edge (hx.symm ▸ hbc) hy hedge.ne
          (spineMap_on_spine c a) (spineMap_on_spine c d) he
        simpa [hx] using h
    exact tagValue_defect r hs _ _ _ (hP u v huv) (hP v z hvz) (hP u z huz)
  have hconst (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix c) :
      spineMap c a = a := spineMap_fixed ha
  have hread (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix c) :
      pairing f (P.chain a) = pairing F (P.chain a) := by
    unfold pairing
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : histPre e.1 a ∧ histPre e.2 a
    · simp [f, pullCochain, hconst _ ((historyData _).trans he.1 ha),
        hconst _ ((historyData _).trans he.2 ha)]
    · simp [P.support a e.1 e.2 (fun h => he ⟨h.1,h.2.1⟩)]
  have hx' : x.1.IsPrefix c := hx.symm ▸ hbc
  have hy' : y.1.IsPrefix c := hy.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
  have hEdge : f (x,y) = 1 := by simp [f, F, pullCochain, hconst _ hx', hconst _ hy',
    testCochain, tagAge, hedge.ne, Ne.symm hedge.ne, tagValue]
  have hfit := (abs_pairing_le_dualNorm h₁ (orientedEdge x y + P.chain x - P.chain y)).trans
    (P.residual x y hedge)
  rw [pairing_chain_sub, pairing_chain_add, pairing_orientedEdge _ _ _ hf,
    hread _ hx', hread _ hy', hEdge] at hfit
  exact (le_abs_self _).trans hfit

private theorem newest_neighbour_age {c : RollingHistory hw hM n k}
    {x a : RollingVertex hw hM n k} (hx : x.1 = c) (ha : a.1.IsPrefix c)
    (h : a = x ∨ (RollingG hw hM n k).Adj a x) : age c a = c.stage.val := by
  apply le_antisymm (age_le_stage _ _)
  rcases h with rfl | h
  · simpa [hx] using birth_le_age ha
  · have hx' : x.1.IsPrefix c := hx.symm ▸ ⟨le_rfl, fun _ _ => rfl⟩
    simpa [hx] using age_ge_of_adj hx' h (hx.symm ▸ ha.1)

private theorem parent_coarse {R L : ℝ} (r : Fin w) (i : ℕ) {b : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b)
    (hi : b.stage.val < i) (hy : b.stage < y.1.stage) :
    pairing (testCochain r i b x y) (P.chain x) =
      pairing (ageCochain r b) (P.chain x) +
        (band r b.stage.val i + 1) * (1 - rootMass x) := by
  classical
  let A := band r b.stage.val i + 1
  let g : Chains (RollingVertex hw hM n k) := fun e =>
    A * ((if e.2 = x then 1 else 0) - (if e.1 = x then 1 else 0))
  have hdiag (a : ℕ) : band r a a = 0 := by simp [band]
  have he : pairing (testCochain r i b x y) (P.chain x) =
      pairing (ageCochain r b + g) (P.chain x) := by
    unfold pairing
    apply Finset.sum_congr rfl
    rintro ⟨a,d⟩ _
    by_cases h0 : P.chain x (a,d) = 0
    · simp [h0]
    have hs := not_not.mp (fun hn => h0 (P.support x a d hn))
    have ha : a.1.IsPrefix b := hx ▸ hs.1
    have hd : d.1.IsPrefix b := hx ▸ hs.2.1
    have hay : a ≠ y := fun h => (ha.1.trans_lt hy).ne (congrArg (fun v => v.1.stage) h)
    have hdy : d ≠ y := fun h => (hd.1.trans_lt hy).ne (congrArg (fun v => v.1.stage) h)
    congr 1
    by_cases hax : a = x <;> by_cases hdx : d = x
    · simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hdx, hdiag]
    · subst a
      have h₁ := newest_neighbour_age hx hd (hs.2.2.imp Eq.symm SimpleGraph.Adj.symm)
      have h₂ := newest_neighbour_age hx ha (Or.inl rfl)
      simp [testCochain, ageCochain, tagAge, tagValue, g, hdx, hdy, h₁, h₂, A, hi.ne, hdiag]
    · subst d
      have h₁ := newest_neighbour_age hx ha hs.2.2
      have h₂ := newest_neighbour_age hx hd (Or.inl rfl)
      simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hay, h₁, h₂, A, hi.ne, hdiag]
    · simp [testCochain, ageCochain, tagAge, tagValue, g, hax, hdx, hay, hdy]
  rw [he]
  have hlin : pairing (ageCochain r b + g) (P.chain x) =
      pairing (ageCochain r b) (P.chain x) + pairing g (P.chain x) := by
    simp [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hlin]
  have hg : pairing g (P.chain x) = A * boundary (P.chain x) x :=
    pairing_incident _ _ _
  rw [hg, P.boundary_eq]
  simp [A, Pi.single_apply]

private theorem parent_refinement {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hkeep : x ∈ retainedVertices c b) :
    |pairing (testCochain r c.stage.val c x y) (P.chain x) -
      pairing (testCochain r c.stage.val b x y) (P.chain x)| ≤ 12 * L / M := by
  classical
  let t : Fin (n + 1) := ⟨b.stage.val + 1, (Nat.succ_le_of_lt hd).trans_lt c.stage.isLt⟩
  have htc : t ≤ c.stage := Nat.succ_le_of_lt hd
  let d := c.prefix t htc
  have hbd : b.IsPrefix d := ⟨(show b.stage ≤ t from Nat.le_succ _), fun j hj => by
      change b.step j = if j ≤ t then c.step j else _
      rw [ite_eq_left (hj.trans (show b.stage ≤ t from Nat.le_succ _))]
      exact hbc.2 j hj⟩
  have hdc := c.prefix_spec t htc
  have hxkeep : x ∈ retainedVertices d b := retained_subset hdc hkeep
  let S := retentionError b d x
  have hconst (a : RollingVertex hw hM n k) (ha : a.1.IsPrefix b) (hn : a ∉ S) :
      tagAge c x y a = tagAge b x y a := by
    by_cases hax : a = x
    · simp [tagAge,hax]
    · by_cases hay : a = y
      · simp [tagAge,hax,hay]
      · have hno : a.2 ∉ (c.step t).1 a.1.stage := by
          intro hm
          apply hn
          apply Finset.mem_biUnion.mpr
          refine ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,
            Finset.mem_erase.mpr ⟨hax,mem_retainedVertices.mpr ⟨rfl,?_⟩⟩⟩
          simpa [d, History.prefix] using hm
        simp [tagAge,hax,hay,age_stable hbc t rfl htc hno]
  have hbound := abs_pairing_change_le (testCochain r c.stage.val c x y)
    (testCochain r c.stage.val b x y) (P.chain x) S 6 (by norm_num)
    (fun e => (abs_sub _ _).trans ((add_le_add (tagValue_abs _ _ _ _) (tagValue_abs _ _ _ _)).trans (by norm_num)))
    (fun a d ha hd hne => by
      have hs := not_not.mp (fun hn => hne (P.support x a d hn))
      simp [testCochain, hconst a (hx ▸ hs.1) ha, hconst d (hx ▸ hs.2.1) hd])
  exact hbound.trans ((mul_le_mul_of_nonneg_left (retentionError_load_bound P x hx hbd rfl hxkeep)
    (by norm_num)).trans_eq (by ring))

private theorem child_refinement {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hy : y.1 = c) (hbc : b.IsPrefix c)
    (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val + w) (hkeep : x ∈ retainedVertices c b) :
    |pairing (testCochain r c.stage.val c x y) (P.chain y) -
      pairing (ageCochain r c) (P.chain y)| ≤ 12 * L / M := by
  classical
  have hdiag : band r c.stage.val c.stage.val = 0 := by simp [band]
  have hbound := abs_pairing_change_le (testCochain r c.stage.val c x y)
    (ageCochain r c) (P.chain y) {x} 6 (by norm_num)
    (fun e => (abs_sub _ _).trans ((add_le_add (tagValue_abs _ _ _ _) (band_abs_le _ _ _)).trans (by norm_num)))
    (fun a d ha hd hne => by
      have ha' : a ≠ x := by simpa using ha
      have hd' : d ≠ x := by simpa using hd
      have H := not_not.mp (fun hn => hne (P.support y a d hn))
      by_cases hay : a = y <;> by_cases hdy : d = y
      · subst a; subst d
        have h := newest_neighbour_age hy (hy ▸ H.1) (Or.inl rfl)
        simp [testCochain, ageCochain, tagAge, tagValue, ha', h, hdiag]
      · subst a
        have h₁ := newest_neighbour_age hy (hy ▸ H.1) (Or.inl rfl)
        have h₂ := newest_neighbour_age hy (hy ▸ H.2.1) (H.2.2.imp Eq.symm SimpleGraph.Adj.symm)
        simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hdy,h₁,h₂,hdiag]
      · subst d
        have h₁ := newest_neighbour_age hy (hy ▸ H.1) H.2.2
        have h₂ := newest_neighbour_age hy (hy ▸ H.2.1) (Or.inl rfl)
        simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hay,h₁,h₂,hdiag]
      · simp [testCochain, ageCochain, tagAge, tagValue, ha',hd',hay,hdy])
  simp only [Finset.sum_singleton] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left (child_load_bound P x y hy hbc hd hs hkeep)
    (by norm_num)).trans_eq (by ring))


private theorem age_pairing_independent {R L : ℝ} (r : Fin w) (b : RollingHistory hw hM n k)
    (P : Localized (concreteRetention w n M hw hM) k R L) (s t : Fin (M^(w+2))) :
    pairing (ageCochain r b) (P.chain (b,s)) =
      pairing (ageCochain r b) (P.chain (b,t)) := by
  classical
  have hb : b.IsPrefix b := ⟨le_rfl, fun _ _ => rfl⟩
  obtain ⟨σ,_,hσ,_,ha⟩ := alive_swap hb (birth_live (v := (b,s)) hb) (birth_live (v := (b,t)) hb)
  unfold pairing
  rw [← Equiv.sum_comp (σ.val.prodCongr σ.val)
    (fun e : RollingVertex hw hM n k × RollingVertex hw hM n k =>
      ageCochain r b e * P.chain (b,t) e)]
  apply Finset.sum_congr rfl
  rintro ⟨a,d⟩ _
  change _ * _ = ageCochain r b (σ.val a,σ.val d) * P.chain (b,t) (σ.val a,σ.val d)
  rw [← hσ, P.equivariant]
  by_cases h : a.1.IsPrefix b ∧ d.1.IsPrefix b
  · simp [ageCochain, ha a h.1, ha d h.2]
  · simp [P.support (b,s) a d (fun hs => h ⟨hs.1,hs.2.1⟩)]

private theorem band_transfer {R L : ℝ} (r : Fin w) {b c : RollingHistory hw hM n k}
    (P : Localized (concreteRetention w n M hw hM) k R L)
    (x y : RollingVertex hw hM n k) (hx : x.1 = b) (hy : y.1 = c)
    (hbc : b.IsPrefix c) (hd : b.stage < c.stage) (hs : c.stage.val ≤ b.stage.val + w)
    (hkeep : x ∈ retainedVertices c b) :
    2 + band r b.stage.val c.stage.val + pairing (ageCochain r b) (P.chain x) -
      pairing (ageCochain r c) (P.chain y) ≤ R + 24 * L / M + 3 / (M ^ (w+2) : ℝ) := by
  classical
  have hne : x ≠ y := fun e => hd.ne (congrArg History.stage (hx.symm.trans ((congrArg Prod.fst e).trans hy)))
  have hEdge : (RollingG hw hM n k).Adj x y := by
    refine ⟨hne, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · change x.1.IsPrefix y.1
      rw [hx,hy]
      exact hbc
    · change x.2 ∈ (y.1.step y.1.stage).1 x.1.stage
      rw [hx,hy]
      exact (mem_retainedVertices.mp hkeep).2
  have htest := testCochain_eval_residual r P x y hx hy hbc hd hs hEdge
  have h₁ := (abs_le.mp (parent_refinement r P x y hx hy hbc hd hkeep)).1
  have h₂ := (abs_le.mp (child_refinement r P x y hy hbc hd hs hkeep)).2
  rw [parent_coarse r _ P x y hx (show b.stage.val < c.stage.val from hd) (hy.symm ▸ hd)] at h₁
  have hroot : 0 ≤ rootMass x ∧ rootMass x ≤ ((M : ℝ) ^ (w+2))⁻¹ := by
    unfold rootMass
    split
    · rw [Nat.cast_pow]
      exact ⟨by positivity, le_rfl⟩
    · exact ⟨le_rfl, by positivity⟩
  have hfactor : (band r b.stage.val c.stage.val + 1) * rootMass x ≤
      3 / (M ^ (w+2) : ℝ) := by
    have hr := (abs_le.mp (band_abs_le r b.stage.val c.stage.val)).2
    calc
      _ ≤ 3 * rootMass x := mul_le_mul_of_nonneg_right (by linarith) hroot.1
      _ ≤ _ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hroot.2 (by norm_num)
  rw [mul_sub, mul_one] at h₁
  have herr : (24 : ℝ) * L / M = 12 * L / M + 12 * L / M := by ring
  rw [herr]
  linarith

private theorem localized_band {R L : ℝ}
    (P : Localized (concreteRetention w n M hw hM) k R L) :
    ∃ H : Fin w → ℕ → ℝ, (∀ t, ∑ r, H r t = 0) ∧
      ∀ r u v, u < v → v ≤ u + w → v ≤ n →
        2 + band r u v + H r u - H r v ≤ R + 24 * L / M + 3 / (M ^ (w+2) : ℝ) := by
  classical
  let top := fullSpine w n M k hw hM
  let a (t : ℕ) (ht : t ≤ n) : RollingHistory hw hM n k :=
    top.prefix ⟨t, Nat.lt_succ_of_le ht⟩ ht
  have aq (t : ℕ) (ht : t ≤ n) : (a t ht).stage.val = t := rfl
  let zeroLabel : Fin (M^(w+2)) := ⟨0, pow_pos (by omega) _⟩
  let H (r : Fin w) (t : ℕ) : ℝ := if ht : t ≤ n then
    pairing (ageCochain r (a t ht)) (P.chain (a t ht,zeroLabel)) else 0
  refine ⟨H, ?_, ?_⟩
  · intro t
    by_cases ht : t ≤ n
    · unfold H
      simp only [dif_pos ht, pairing, ageCochain]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, sum_band (show 0 < w by omega), zero_mul, Finset.sum_const_zero]
    · simp [H,ht]
  · intro r u v huv hwv hnv
    have hnu : u ≤ n := huv.le.trans hnv
    let b := a u hnu
    let c := a v hnv
    have hbc : b.IsPrefix c := by
      refine ⟨huv.le, fun i hi => ?_⟩
      have hi' : i ≤ c.stage := hi.trans huv.le
      change (if i ≤ b.stage then top.step i else _) = (if i ≤ c.stage then top.step i else _)
      rw [ite_eq_left hi, ite_eq_left hi']
    have hd : b.stage < c.stage := huv
    have hs : c.stage.val ≤ b.stage.val+w := hwv
    have hcard : 0 < ((c.step c.stage).1 b.stage).card := by
      rw [c.cardinal _ _ le_rfl]
      change 0 < quota w M u v
      simp [quota, hwv, pow_pos (show 0 < M by omega)]
    obtain ⟨s,hs'⟩ := Finset.card_pos.mp hcard
    let x : RollingVertex hw hM n k := (b,s)
    let y : RollingVertex hw hM n k := (c,zeroLabel)
    have hb := band_transfer r P x y rfl rfl hbc hd hs (mem_retainedVertices.mpr ⟨rfl,hs'⟩)
    change 2 + band r u v + pairing (ageCochain r b) (P.chain (b,s)) -
      pairing (ageCochain r c) (P.chain (c,zeroLabel)) ≤ _ at hb
    rw [age_pairing_independent r b P s zeroLabel] at hb
    simpa [H, hnu, hnv, b, c, a] using hb


end Ages

end

end SimpleGraph.ChordalReconstruction

namespace SimpleGraph

open ChordalReconstruction Omega.GraphChains Omega.RollingCliques Omega.PeriodicBandCochains

/-- For every positive tolerance, a finite connected chordal graph has a Banach-valued gain
with triangle defect at most one and reconstruction error at least four minus that tolerance. -/
theorem exists_chordal_banach_gain_lower_four (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), G.IsChordal ∧ G.Connected ∧
      ∃ (E : Type) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
        letI := N
        letI := S
        ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : V → V → E),
          (∀ u v, g v u = -g u v) ∧
          (∀ u v z, G.Adj u v → G.Adj v z → G.Adj u z → ‖g u v + g v z - g u z‖ ≤ 1) ∧
          ∀ φ : V → E, ∃ u v, G.Adj u v ∧ 4 - ε ≤ ‖g u v - (φ v - φ u)‖ := by
  classical
  obtain ⟨m,hm,hparam⟩ := band_parameters ε hε
  let n := m * m + m + 1
  let L : ℝ := 13 * (n + 1)
  have hL : 0 < L := by positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (4 * (24 * L + 3) / ε))
  obtain ⟨k,hk⟩ := exists_nat_gt (4 * (12 * L) / ε)
  have hM₁ : (1 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hM' : 1 ≤ M := by exact_mod_cast hM₁.le
  have hM₂ : 4 * (24 * L + 3) < (M : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hM)
  have hk' : 4 * (12 * L) < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hMerr : (24 * L + 3) / (M : ℝ) < ε / 4 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < M by linarith)).2
    nlinarith
  have hkerr : 12 * L / ((k : ℝ) + 1) < ε / 4 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < (k : ℝ) + 1 by positivity)).2
    nlinarith
  have hpow : (M : ℝ) ≤ (M : ℝ) ^ (m+2) := by
    simpa using pow_le_pow_right₀ hM₁.le (show 1 ≤ m+2 by omega)
  have hqerr : (3 : ℝ) / (M : ℝ) ^ (m+2) ≤ 3 / (M : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hpow
  have hErr : 12 * L / ((k : ℝ) + 1) + 24 * L / (M : ℝ) +
      3 / (M : ℝ) ^ (m+2) ≤ ε / 2 := by
    rw [add_div] at hMerr
    linarith
  let P := concreteRetention m n M hm hM'
  let G : SimpleGraph (HV P k) := histGraph P k
  let x₀ : Fin (M^(m+2)) := ⟨0, pow_pos (by omega) _⟩
  let o : HV P k := (History.initial P,x₀)
  have hconn := rolling_connected (historyData (k := k) P) x₀
  refine ⟨HV P k, inferInstance, G, rolling_chordal _, hconn, ?_⟩
  apply gain_of_rooted_chain_obstruction G hconn o (4 - ε)
  intro p hsupport hboundary
  by_contra! hfail
  obtain ⟨p'⟩ := obtain_localized (P := P) x₀.isLt (4 - ε) (by linarith) o p hsupport hboundary
    (fun u v hu => (hfail u v hu).le)
  obtain ⟨H,hH,hband⟩ := localized_band p'
  apply band_contradiction ε hm hparam H hH
  intro r u v huv hwv hnv
  have h := hband r u v huv hwv hnv
  change 2 + band r u v + H r u - H r v ≤
    4 - ε + 12 * L / ((k : ℝ) + 1) + 24 * L / M + 3 / (M : ℝ) ^ (m+2) at h
  linarith

end SimpleGraph
