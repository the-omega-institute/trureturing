/- GID: D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simplicial means and greedy interval and split graph attachments bound gain errors. -/

import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! # Simplicial averaging and reconstruction on interval and split graphs -/

open scoped BigOperators

namespace SimpleGraph

universe u v

private noncomputable def averagingRadius (k n : ℕ) : ℝ :=
  (k - 1 : ℝ) * (1 - (((k - 1 : ℝ) / k) ^ (n - 1)))

private theorem averagingRadius_nonneg (k n : ℕ) (hk : 2 ≤ k) :
    0 ≤ averagingRadius k n := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 ≤ ((k - 1 : ℝ) / k) := div_nonneg (by linarith) (by linarith)
  have hq' : ((k - 1 : ℝ) / k) ≤ 1 := (div_le_iff₀ (by linarith)).2 (by linarith)
  exact mul_nonneg (by linarith) (sub_nonneg.mpr (pow_le_one₀ hq hq'))

private theorem averagingRadius_step (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    averagingRadius k (n + 1) = ((k - 1 : ℝ) / k) * (averagingRadius k n + 1) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  unfold averagingRadius
  rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
  field_simp
  ring

private theorem averagingRadius_mono_step (k n : ℕ) (hk : 2 ≤ k) :
    averagingRadius k n ≤ averagingRadius k (n + 1) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 ≤ ((k - 1 : ℝ) / k) := div_nonneg (by linarith) (by linarith)
  have hq' : ((k - 1 : ℝ) / k) ≤ 1 := (div_le_iff₀ (by linarith)).2 (by linarith)
  unfold averagingRadius
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (pow_le_pow_of_le_one hq hq' (by omega)) _) (by linarith)

private theorem mean_candidate_bound {V : Type u} {E : Type v}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq V]
    (S : Finset V) (p : V → E) {u : V} (hu : u ∈ S) {B : ℝ}
    (h : ∀ w ∈ S.erase u, ‖p u - p w‖ ≤ B) :
    ‖p u - (S.card : ℝ)⁻¹ • ∑ w ∈ S, p w‖ ≤
      ((S.card : ℝ) - 1) / S.card * B := by
  have hm : (0 : ℝ) < S.card := by exact_mod_cast (Finset.card_pos.mpr ⟨u, hu⟩)
  have he : p u - (S.card : ℝ)⁻¹ • ∑ w ∈ S, p w =
      (S.card : ℝ)⁻¹ • ∑ w ∈ S, (p u - p w) := by
    simp [Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, hm.ne']
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  have hsum : ∑ w ∈ S, ‖p u - p w‖ ≤ ((S.erase u).card : ℝ) * B := by
    rw [← S.sum_erase_add (fun w => ‖p u - p w‖) hu]
    simp only [sub_self, norm_zero, add_zero]
    exact (Finset.sum_le_sum h).trans_eq (by simp)
  have hc : ((S.erase u).card : ℝ) + 1 = S.card := by exact_mod_cast Finset.card_erase_add_one hu
  calc
    _ ≤ (S.card : ℝ)⁻¹ * ∑ w ∈ S, ‖p u - p w‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hm.le)
    _ ≤ (S.card : ℝ)⁻¹ * (((S.erase u).card : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm.le)
    _ = _ := by rw [show ((S.erase u).card : ℝ) = S.card - 1 by linarith]; ring

/-- Averaging the candidates at a deleted simplicial vertex yields the finite-size radius. -/
theorem IsChordal.exists_simplicial_banach_gain_potential
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 2 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (k - 1 : ℝ) *
        (1 - (((k - 1 : ℝ) / k) ^ (Nat.card V - 1))) * ε := by
  classical
  let := Fintype.ofFinite V
  have hmain (S : Finset V) : ∃ φ : V → E, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ averagingRadius k S.card * ε := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · let : Nonempty (↑S : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
        let a : V := z.val
        have ha : a ∈ S := z.property
        have hlt : (S.erase a).card < S.card := Finset.card_erase_lt_of_mem ha
        obtain ⟨ψ, hψ⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let N := S.filter fun w => G.Adj w a
        have memN {w : V} : w ∈ N ↔ w ∈ S ∧ G.Adj w a := Finset.mem_filter
        have haN : a ∉ N := fun h => (memN.mp h).2.ne rfl
        have adjN {x y : V} (hx : x ∈ N) (hy : y ∈ N) (hne : x ≠ y) : G.Adj x y :=
          hz (show (⟨x, (memN.mp hx).1⟩ : (S : Set V)) ∈ _ from (memN.mp hx).2.symm)
            (show (⟨y, (memN.mp hy).1⟩ : (S : Set V)) ∈ _ from (memN.mp hy).2.symm)
            (by simpa [Subtype.ext_iff] using hne)
        have hcl : G.IsClique (↑(insert a N) : Set V) := by
          intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
          rcases hx with rfl | hx
          · exact (memN.mp (hy.resolve_left hxy.symm)).2.symm
          · rcases hy with rfl | hy
            · exact (memN.mp hx).2
            · exact adjN hx hy hxy
        have hNk := hclique (insert a N) hcl
        rw [Finset.card_insert_of_notMem haN] at hNk
        have hNk' : N.card ≤ k := by omega
        have hcard : (S.erase a).card + 1 = S.card := Finset.card_erase_add_one ha
        let p (w : V) := ψ w + g w a
        let μ := (N.card : ℝ)⁻¹ • ∑ w ∈ N, p w
        let φ (w : V) := if w = a then μ else ψ w
        have old {x y : V} (hx : x ∈ S.erase a) (hy : y ∈ S.erase a) (hxy : G.Adj x y) :
            ‖g x y - (φ y - φ x)‖ ≤ averagingRadius k S.card * ε := by
          simp only [φ, (Finset.mem_erase.mp hx).1, (Finset.mem_erase.mp hy).1, ite_false]
          apply (hψ x hx y hy hxy).trans
          rw [← hcard]
          exact mul_le_mul_of_nonneg_right (averagingRadius_mono_step k _ hk) hε
        have new {x : V} (hx : x ∈ N) : ‖g x a - (φ a - φ x)‖ ≤ averagingRadius k S.card * ε := by
          have hxa := (memN.mp hx).2
          have hx' : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa.ne, (memN.mp hx).1⟩
          have hn : 1 ≤ (S.erase a).card := Finset.card_pos.mpr ⟨x, hx'⟩
          let B := (averagingRadius k (S.erase a).card + 1) * ε
          have hB : 0 ≤ B := mul_nonneg (by linarith [averagingRadius_nonneg k (S.erase a).card hk]) hε
          have pair (w : V) (hw : w ∈ N.erase x) : ‖p x - p w‖ ≤ B := by
            obtain ⟨hwx, hwN⟩ := Finset.mem_erase.mp hw
            have hwa := (memN.mp hwN).2
            have hw' : w ∈ S.erase a := Finset.mem_erase.mpr ⟨hwa.ne, (memN.mp hwN).1⟩
            have hxw := adjN hx hwN hwx.symm
            have he : p x - p w = (g x w - (ψ w - ψ x)) - (g x w + g w a - g x a) := by
              dsimp [p]; abel
            rw [he]
            exact (norm_sub_le _ _).trans (by dsimp [B]; linarith [hψ x hx' w hw' hxw, htri x w a hxw hwa hxa])
          have hmean := mean_candidate_bound N p hx pair
          have hm : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
          have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
          have hmk : (N.card : ℝ) ≤ k := by exact_mod_cast hNk'
          have hfrac : ((N.card : ℝ) - 1) / N.card ≤ (k - 1 : ℝ) / k := by
            apply (div_le_div_iff₀ hm (by linarith : (0 : ℝ) < k)).mpr
            nlinarith
          have he : g x a - (φ a - φ x) = p x - μ := by
            simp only [φ, ite_true, hxa.ne, ite_false, p]; abel
          rw [he, ← hcard, averagingRadius_step k _ hk hn]
          calc
            _ ≤ ((N.card : ℝ) - 1) / N.card * B := hmean
            _ ≤ ((k - 1 : ℝ) / k) * B := mul_le_mul_of_nonneg_right hfrac hB
            _ = _ := by dsimp [B]; ring
        refine ⟨φ, fun x hx y hy hxy => ?_⟩
        by_cases hxa : x = a
        · subst x
          rw [hrev y a, show -(g y a) - (φ y - φ a) = -(g y a - (φ a - φ y)) by abel, norm_neg]
          exact new (memN.mpr ⟨hy, hxy.symm⟩)
        · by_cases hya : y = a
          · subst y
            exact new (memN.mpr ⟨hx, hxy⟩)
          · exact old (Finset.mem_erase.mpr ⟨hxa, hx⟩) (Finset.mem_erase.mpr ⟨hya, hy⟩) hxy
      · exact ⟨fun _ => 0, fun x hx => (hs ⟨x, hx⟩).elim⟩
  obtain ⟨φ, hφ⟩ := hmain Finset.univ
  refine ⟨φ, fun x y hxy => ?_⟩
  simpa [averagingRadius, Nat.card_eq_fintype_card] using hφ x (Finset.mem_univ _) y (Finset.mem_univ _) hxy


section GraphClasses

variable {V : Type u} {G : SimpleGraph V}

-- A simplicial vertex in the induced vertex set of a cycle forces a chord.
private theorem chordal_of_local_simplicial
    (h : ∀ (S : Finset V), S.Nonempty → ∃ z ∈ S,
      ∀ x ∈ S, ∀ y ∈ S, G.Adj z x → G.Adj z y → x ≠ y → G.Adj x y) :
    G.IsChordal := by
  classical
  intro v c hc hlen
  obtain ⟨z, hz, hzcl⟩ := h c.support.toFinset ⟨v, by simp⟩
  have hz' : z ∈ c.support := by simpa using hz
  let d := c.rotate z hz'
  have hd : d.IsCycle := hc.rotate hz'
  have hn : 4 ≤ d.length := by simpa [d] using hlen
  have he := c.rotate_edges z hz'
  have hsupp (w : V) (hw : w ∈ d.support) : w ∈ c.support := by
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.mp hw with rfl | hh
    · exact hz'
    · exact List.mem_of_mem_tail ((c.support_rotate z hz').mem_iff.mp hh)
  have hx := hsupp d.snd (d.getVert_mem_support 1)
  have hy := hsupp d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hx, hy,
    hzcl _ (by simpa using hx) _ (by simpa using hy) (d.adj_snd hd.not_nil)
      (d.adj_penultimate hd.not_nil).symm hd.snd_ne_penultimate, ?_⟩
  intro hm
  have hmem : d.penultimate ∈ d.toSubgraph.neighborSet d.snd :=
    Walk.adj_toSubgraph_iff_mem_edges.mpr (he.mem_iff.mpr hm)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at hmem
  rw [hd.neighborSet_toSubgraph_internal (i := 1) (by omega) (by omega)] at hmem
  simp only [Nat.sub_self, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hfirst : d.length - 1 ∈ {i : ℕ | i ≤ d.length - 1} := by simp
  have hzero : 0 ∈ {i : ℕ | i ≤ d.length - 1} := by simp
  have htwo : 2 ∈ {i : ℕ | i ≤ d.length - 1} := by simp; omega
  rcases hmem with h | h
  · have eq := hd.getVert_injOn' hfirst hzero h
    omega
  · have eq := hd.getVert_injOn' hfirst htwo h
    omega

private theorem interval_chordal (ℓ r : V → ℝ)
    (hG : ∀ x y, G.Adj x y ↔ x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y)) :
    G.IsChordal := by
  classical
  apply chordal_of_local_simplicial
  intro S hs
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S r hs
  refine ⟨z, hz, fun x hx y hy hzx hzy hxy => (hG x y).2 ⟨hxy, ?_⟩⟩
  have hxl : ℓ x ≤ r z := (le_max_right _ _).trans ((hG z x).1 hzx).2 |>.trans (min_le_left _ _)
  have hyl : ℓ y ≤ r z := (le_max_right _ _).trans ((hG z y).1 hzy).2 |>.trans (min_le_left _ _)
  exact (max_le hxl hyl).trans (le_min (hmin x hx) (hmin y hy))

private theorem split_chordal (C : Set V) (hC : G.IsClique C) (hD : G.IsIndepSet Cᶜ) :
    G.IsChordal := by
  classical
  apply chordal_of_local_simplicial
  intro S hs
  by_cases h : ∃ z ∈ S, z ∉ C
  · obtain ⟨z, hz, hzC⟩ := h
    refine ⟨z, hz, fun x hx y hy hzx hzy hxy => ?_⟩
    have memC {w : V} (hw : G.Adj z w) : w ∈ C := by
      by_contra hn
      exact (hD hzC hn hw.ne) hw
    exact hC (memC hzx) (memC hzy) hxy
  · obtain ⟨z, hz⟩ := hs
    refine ⟨z, hz, fun x hx y hy hzx hzy hxy => hC ?_ ?_ hxy⟩
    · by_contra hn; exact h ⟨x, hx, hn⟩
    · by_contra hn; exact h ⟨y, hy, hn⟩

section GroupGains

variable {H : Type v} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

omit [IsIsometricSMul H H] in
private theorem reverse_fit (g : V → V → H) (φ : V → H)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹) {x y : V} (hxy : G.Adj x y) :
    Dist.dist (φ y * g y x) (φ x) = Dist.dist (φ x * g x y) (φ y) := by
  rw [hrev x y hxy, ← dist_mul_right _ _ (g x y), mul_assoc, inv_mul_cancel, mul_one]
  exact _root_.dist_comm _ _

private theorem interval_rooted_fit (ℓ r : V → ℝ) (hI : ∀ v, ℓ v ≤ r v)
    (hG : ∀ x y, G.Adj x y ↔ x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y))
    (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε)
    (S : Finset V) : ∀ p ∈ S, (∀ x ∈ S, ℓ p ≤ r x) →
      ∃ φ : V → H, (∀ x ∈ S, G.Adj p x → φ p * g p x = φ x) ∧
        ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → Dist.dist (φ x * g x y) (φ y) ≤ 2 * ε := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro p hp hleft
    let N := S.filter (G.Adj p)
    have memN {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj p x := Finset.mem_filter
    have overlap {x y : V} (h : G.Adj x y) : ℓ x ≤ r y ∧ ℓ y ≤ r x := by
      have h' := ((hG x y).mp h).2
      exact ⟨(le_max_left _ _).trans (h'.trans (min_le_right _ _)),
        (le_max_right _ _).trans (h'.trans (min_le_left _ _))⟩
    have adjacent {x y : V} (hn : x ≠ y) (hxy : ℓ x ≤ r y) (hyx : ℓ y ≤ r x) : G.Adj x y :=
      (hG x y).2 ⟨hn, le_min (max_le (hI x) hyx) (max_le hxy (hI y))⟩
    have outside {x : V} (hx : x ∈ S) (hxp : x ≠ p) (hn : ¬ G.Adj p x) : r p < ℓ x := by
      by_contra! h
      exact hn (adjacent hxp.symm (hleft x hx) h)
    have nonneg : 0 ≤ 2 * ε := by linarith
    by_cases hN : N.Nonempty
    · obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image N r hN
      have hpq := (memN.mp hq).2
      let T := S.filter fun x => x = q ∨ (x ≠ p ∧ ¬ G.Adj p x)
      have memT {x : V} : x ∈ T ↔ x ∈ S ∧ (x = q ∨ (x ≠ p ∧ ¬ G.Adj p x)) := Finset.mem_filter
      have hqT : q ∈ T := memT.mpr ⟨(memN.mp hq).1, Or.inl rfl⟩
      have hpT : p ∉ T := by simp [memT, hpq.ne]
      have hTS : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨fun x hx => (memT.mp hx).1, fun he => hpT (he.symm ▸ hp)⟩
      have hlq : ∀ x ∈ T, ℓ q ≤ r x := by
        intro x hx
        rcases (memT.mp hx).2 with rfl | ⟨hxp, hnx⟩
        · exact hI _
        · exact (overlap hpq).2.trans ((outside (memT.mp hx).1 hxp hnx).le.trans (hI x))
      obtain ⟨ψ, hstar, hfit⟩ := ih T hTS q hqT hlq
      let A := g p q * (ψ q)⁻¹
      let φ (x : V) := if x = p then 1 else if G.Adj p x then g p x else A * ψ x
      have root : φ p = 1 := ite_eq_left rfl
      have stem {x : V} (hx : G.Adj p x) : φ x = g p x := by simp [φ, hx, hx.ne.symm]
      have tail {x : V} (hx : x ∈ T) : φ x = A * ψ x := by
        rcases (memT.mp hx).2 with rfl | ⟨hxp, hnx⟩
        · rw [stem hpq]; simp [A, mul_assoc]
        · simp [φ, hxp, hnx]
      refine ⟨φ, fun x _ hx => by rw [root, one_mul, stem hx], ?_⟩
      have forward {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y)
          (hxp : x ≠ p) (hpy : y ≠ p) (hnx : G.Adj p x) :
          Dist.dist (φ x * g x y) (φ y) ≤ 2 * ε := by
        by_cases hny : G.Adj p y
        · rw [stem hnx, stem hny]
          exact (htri p x y hnx hxy hny).trans (by linarith)
        · have hr := outside hy hpy hny
          have hxyR := (overlap hxy).2
          have hqR : ℓ y ≤ r q := hxyR.trans (hmax x (memN.mpr ⟨hx, hnx⟩))
          have hqy : G.Adj q y := adjacent (fun he => hny (he ▸ hpq))
            ((overlap hpq).2.trans (hr.le.trans (hI y))) hqR
          have hyT : y ∈ T := memT.mpr ⟨hy, Or.inr ⟨hpy, hny⟩⟩
          have hφy : φ y = g p q * g q y := by
            rw [tail hyT, ← hstar y hyT hqy]
            simp [A, mul_assoc]
          rw [stem hnx, hφy]
          by_cases hxq : x = q
          · subst x; simp [nonneg]
          · have hxq' : G.Adj x q := adjacent hxq
              ((overlap hnx).2.trans (hr.le.trans hqR)) ((overlap hpq).2.trans (hr.le.trans hxyR))
            have h₁ : Dist.dist (g p x * g x y) (g p x * (g x q * g q y)) ≤ ε := by
              rw [dist_mul_left, _root_.dist_comm]
              exact htri x q y hxq' hqy hxy
            have h₂ : Dist.dist (g p x * (g x q * g q y)) (g p q * g q y) ≤ ε := by
              rw [← mul_assoc, dist_mul_right]
              exact htri p x q hnx hxq' hpq
            exact (_root_.dist_triangle _ _ _).trans (by linarith)
      intro x hx y hy hxy
      by_cases hxp : x = p
      · subst x; simp [root, stem hxy, nonneg]
      by_cases hyp : y = p
      · subst y
        rw [reverse_fit g φ hrev hxy.symm, root, one_mul, stem hxy.symm]
        simpa using nonneg
      by_cases hpx : G.Adj p x
      · exact forward hx hy hxy hxp hyp hpx
      by_cases hpy : G.Adj p y
      · rw [reverse_fit g φ hrev hxy.symm]
        exact forward hy hx hxy.symm hyp hxp hpy
      have hxT : x ∈ T := memT.mpr ⟨hx, Or.inr ⟨hxp, hpx⟩⟩
      have hyT : y ∈ T := memT.mpr ⟨hy, Or.inr ⟨hyp, hpy⟩⟩
      rw [tail hxT, tail hyT, mul_assoc, dist_mul_left]
      exact hfit x hxT y hyT hxy
    · have no_edge {x : V} (hx : x ∈ S) : ¬ G.Adj p x := fun h => hN ⟨x, memN.mpr ⟨hx, h⟩⟩
      by_cases he : (S.erase p).Nonempty
      · obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (S.erase p) ℓ he
        obtain ⟨ψ, _, hfit⟩ := ih (S.erase p) (Finset.erase_ssubset hp) q hq
          (fun x hx => (hmin x hx).trans (hI x))
        refine ⟨ψ, fun x hx h => (no_edge hx h).elim, fun x hx y hy hxy => ?_⟩
        have hx' : x ≠ p := fun h => no_edge hy (h ▸ hxy)
        have hy' : y ≠ p := fun h => no_edge hx (h ▸ hxy.symm)
        exact hfit x (Finset.mem_erase.mpr ⟨hx', hx⟩) y (Finset.mem_erase.mpr ⟨hy', hy⟩) hxy
      · refine ⟨fun _ => 1, fun x hx h => (no_edge hx h).elim, fun x hx y hy hxy => ?_⟩
        have hxp : x = p := by by_contra hn; exact he ⟨x, Finset.mem_erase.mpr ⟨hn, hx⟩⟩
        exact (no_edge hy (hxp ▸ hxy)).elim

/-- Finite interval graphs are chordal and admit a universal two-defect gain potential. -/
theorem intervalGraph_isChordal_and_two_approximate_gain_potential [Finite V]
    (ℓ r : V → ℝ) (hI : ∀ v, ℓ v ≤ r v)
    (hG : ∀ x y, G.Adj x y ↔ x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y))
    (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε) :
    G.IsChordal ∧ ∃ φ : V → H, ∀ x y, G.Adj x y →
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 2 * ε := by
  classical
  refine ⟨interval_chordal ℓ r hG, ?_⟩
  let := Fintype.ofFinite V
  by_cases hs : (Finset.univ : Finset V).Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image Finset.univ ℓ hs
    obtain ⟨φ, _, hφ⟩ := interval_rooted_fit ℓ r hI hG g ε hε hrev htri Finset.univ p hp
      (fun x hx => (hmin x hx).trans (hI x))
    refine ⟨φ, fun x y hxy => ?_⟩
    rw [← dist_mul_left (φ x), ← mul_assoc, mul_inv_cancel, one_mul]
    exact hφ x (Finset.mem_univ _) y (Finset.mem_univ _) hxy
  · exact ⟨fun _ => 1, fun x => (hs ⟨x, Finset.mem_univ _⟩).elim⟩

/-- Split graphs are chordal and admit a universal two-defect gain potential. -/
theorem exists_two_approximate_gain_potential_of_split [Finite V]
    (C : Set V) (hC : G.IsClique C) (hD : G.IsIndepSet Cᶜ)
    (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε) :
    G.IsChordal ∧ ∃ φ : V → H, ∀ x y, G.Adj x y →
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 2 * ε := by
  classical
  refine ⟨split_chordal C hC hD, ?_⟩
  let := Fintype.ofFinite V
  let S := Finset.univ.filter (fun x => x ∈ C)
  have hS (x : V) : x ∈ S ↔ x ∈ C := by simp [S]
  by_cases hne : S.Nonempty
  · obtain ⟨o, hoS⟩ := hne
    have ho := (hS o).mp hoS
    let ψ (x : V) := if x = o then 1 else g o x
    let has (x : V) := ∃ c ∈ C, G.Adj c x
    let a (x : V) (hx : has x) := hx.choose
    have ha (x : V) (hx : has x) : a x hx ∈ C ∧ G.Adj (a x hx) x := hx.choose_spec
    let φ (x : V) := if x ∈ C then ψ x else if hx : has x then ψ (a x hx) * g (a x hx) x else 1
    have clique_value {x : V} (hx : x ∈ C) : φ x = ψ x := by simp [φ, hx]
    have clique_fit {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hxy : G.Adj x y) :
        Dist.dist (ψ x * g x y) (ψ y) ≤ ε := by
      by_cases hxo : x = o
      · subst x; simp [ψ, hxy.ne.symm, hε]
      by_cases hyo : y = o
      · subst y; simp [ψ, hxo, hrev o x hxy.symm, hε]
      · simp only [ψ, hxo, hyo, ite_false]
        exact htri o x y (hC ho hx (Ne.symm hxo)) hxy (hC ho hy (Ne.symm hyo))
    have cross {x y : V} (hx : x ∈ C) (hy : y ∉ C) (hxy : G.Adj x y) :
        Dist.dist (φ x * g x y) (φ y) ≤ 2 * ε := by
      have hh : has y := ⟨x, hx, hxy⟩
      have hya := (ha y hh).2
      have hCa := (ha y hh).1
      rw [clique_value hx, show φ y = ψ (a y hh) * g (a y hh) y by simp [φ, hy, hh]]
      by_cases hxa : x = a y hh
      · subst x; simp [hε]
      have hxa' := hC hx hCa hxa
      have h₁ : Dist.dist (ψ x * g x y) (ψ x * (g x (a y hh) * g (a y hh) y)) ≤ ε := by
        rw [dist_mul_left, _root_.dist_comm]
        exact htri x (a y hh) y hxa' hya hxy
      have h₂ : Dist.dist (ψ x * (g x (a y hh) * g (a y hh) y))
          (ψ (a y hh) * g (a y hh) y) ≤ ε := by
        rw [← mul_assoc, dist_mul_right]
        exact clique_fit hx hCa hxa'
      exact (_root_.dist_triangle _ _ _).trans (by linarith)
    refine ⟨φ, fun x y hxy => ?_⟩
    rw [← dist_mul_left (φ x), ← mul_assoc, mul_inv_cancel, one_mul]
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · rw [clique_value hx, clique_value hy]
        exact (clique_fit hx hy hxy).trans (by linarith)
      · exact cross hx hy hxy
    · by_cases hy : y ∈ C
      · rw [reverse_fit g φ hrev hxy.symm]; exact cross hy hx hxy.symm
      · exact ((hD hx hy hxy.ne) hxy).elim
  · exact ⟨fun _ => 1, fun x y hxy => ((hD (fun hx => hne ⟨x, (hS x).mpr hx⟩)
      (fun hy => hne ⟨y, (hS y).mpr hy⟩) hxy.ne) hxy).elim⟩

end GroupGains
end GraphClasses

/-- The frozen finite path powers have the closed interval representation with endpoints `i`, `i+k`. -/
theorem BanachPathPower.pathPower_isIntervalGraph (n k : ℕ) :
    ∃ ℓ r : Fin n → ℝ, (∀ v, ℓ v = (v.val : ℝ) ∧ r v = (v.val : ℝ) + k) ∧
      (∀ v, ℓ v ≤ r v) ∧ ∀ x y, (pathPower n k).Adj x y ↔ x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y) := by
  refine ⟨fun i => i.val, fun i => (i.val : ℝ) + k, fun _ => ⟨rfl, rfl⟩, ?_, fun x y => ?_⟩
  · intro i
    exact le_add_of_nonneg_right (Nat.cast_nonneg k)
  change (x ≠ y ∧ x.val ≤ y.val + k ∧ y.val ≤ x.val + k) ↔
    x ≠ y ∧ max (x.val : ℝ) (y.val : ℝ) ≤ min ((x.val : ℝ) + k) ((y.val : ℝ) + k)
  constructor
  · rintro ⟨hne, hxy, hyx⟩
    exact ⟨hne, le_min (max_le (le_add_of_nonneg_right (Nat.cast_nonneg k))
      (by exact_mod_cast hyx)) (max_le (by exact_mod_cast hxy)
      (le_add_of_nonneg_right (Nat.cast_nonneg k)))⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, by exact_mod_cast (le_max_left _ _).trans (h.trans (min_le_right _ _)),
      by exact_mod_cast (le_max_right _ _).trans (h.trans (min_le_left _ _))⟩

example : Nonempty (Fin 2) := ⟨0⟩

example : ∃ g : Fin 2 → Fin 2 → ℝ,
    (∀ i j, g j i = -g i j) ∧
    (∀ i j l, (⊤ : SimpleGraph (Fin 2)).Adj i j → (⊤ : SimpleGraph (Fin 2)).Adj j l →
      (⊤ : SimpleGraph (Fin 2)).Adj i l → ‖g i j + g j l - g i l‖ ≤ 0) :=
  ⟨fun _ _ => 0, by simp, by simp⟩

example : ∃ ℓ r : Fin 2 → ℝ, (∀ v, ℓ v ≤ r v) ∧
    (∀ x y, (⊤ : SimpleGraph (Fin 2)).Adj x y ↔
      x ≠ y ∧ max (ℓ x) (ℓ y) ≤ min (r x) (r y)) :=
  ⟨fun _ => 0, fun _ => 0, by simp, by simp⟩

example : ∃ C : Set (Fin 2), (⊤ : SimpleGraph (Fin 2)).IsClique C ∧
    (⊤ : SimpleGraph (Fin 2)).IsIndepSet Cᶜ :=
  ⟨Set.univ, by simp, by simp⟩

#print axioms IsChordal.exists_simplicial_banach_gain_potential
#print axioms intervalGraph_isChordal_and_two_approximate_gain_potential
#print axioms exists_two_approximate_gain_potential_of_split
#print axioms BanachPathPower.pathPower_isIntervalGraph

end SimpleGraph
