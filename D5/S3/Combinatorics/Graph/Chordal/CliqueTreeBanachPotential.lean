/- GID: D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Center extension and separator midpoint bounds on clique trees. -/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! # Gain reconstruction on clique trees -/

open scoped BigOperators
namespace SimpleGraph
universe u v w

/-- A tree of clique bags covering the vertices and edges, with running intersection
expressed along simple paths. -/
structure IsCliqueTree {I : Type w} {V : Type u} (T : SimpleGraph I) (G : SimpleGraph V)
    (K : I → Set V) : Prop where
  isTree : T.IsTree
  clique : ∀ a, G.IsClique (K a)
  cover : ∀ x, ∃ a, x ∈ K a
  edge : ∀ u v, G.Adj u v → ∃ a, u ∈ K a ∧ v ∈ K a
  running : ∀ {a b} (p : T.Walk a b), p.IsPath →
    ∀ x ∈ K a, x ∈ K b → ∀ c ∈ p.support, x ∈ K c

/-- Residual coefficients after successive waves of separator averaging. -/
noncomputable def cliqueTreeRadius (m : ℕ) (R₀ : ℝ) : ℕ → ℝ
  | 0 => R₀
  | n + 1 =>
    let R := cliqueTreeRadius m R₀ n
    max (max R 1) ((1 - 1 / (m : ℝ)) * (1 + R))

/-- The bound on the change at a separator vertex when taking its midpoint. -/
noncomputable def sepShift {I : Type w} {V : Type u} (K : I → Set V) (a b : I) : ℝ :=
  (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
    (1 - ((K a ∩ K b).ncard : ℝ) / ((max (K a).ncard (K b).ncard : ℕ) : ℝ))

namespace CliqueTreeBanach
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
private noncomputable def mean (S : Finset V) (f : V → E) : E :=
  (S.card : ℝ)⁻¹ • ∑ t ∈ S, f t
private theorem mean_sub (S : Finset V) (f h : V → E) :
    mean S f - mean S h = mean S (fun t => f t - h t) := by
  simp [mean, Finset.sum_sub_distrib, smul_sub]
private theorem const_sub_mean {S : Finset V} (hS : S.Nonempty) (e : E) (f : V → E) :
    e - mean S f = mean S (fun t => e - f t) := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  simp [mean, Finset.sum_sub_distrib, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn]
private theorem mean_bound {S A : Finset V} (hAS : A ⊆ S)
    (f : V → E) (B : ℝ) (hz : ∀ t ∈ S, t ∉ A → f t = 0)
    (hb : ∀ t ∈ A, ‖f t‖ ≤ B) :
    ‖mean S f‖ ≤ ((A.card : ℝ) / S.card) * B := by
  classical
  have hp : 0 ≤ (S.card : ℝ)⁻¹ := by positivity
  have hs : ∑ t ∈ A, f t = ∑ t ∈ S, f t := Finset.sum_subset hAS hz
  rw [mean, ← hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * (∑ t ∈ A, ‖f t‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp
    _ ≤ (S.card : ℝ)⁻¹ * (∑ _t ∈ A, B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) hp
    _ = _ := by simp [div_eq_mul_inv]; ring
private theorem full_mean_bound {S : Finset V} (hS : S.Nonempty) {f : V → E} {B : ℝ}
    (hb : ∀ t ∈ S, ‖f t‖ ≤ B) : ‖mean S f‖ ≤ 1 * B := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  simpa only [div_self hn] using mean_bound (fun _ h => h : S ⊆ S) f B
    (fun _ ht hnt => (hnt ht).elim) hb
private theorem diag_zero (g : V → V → E) (hrev : ∀ i j, g j i = -g i j)
    (x : V) : g x x = 0 := by
  have hz : (2 : ℝ) • g x x = 0 := by rw [two_smul, eq_neg_iff_add_eq_zero.mp (hrev x x)]
  calc
    g x x = (1 / 2 : ℝ) • ((2 : ℝ) • g x x) := by rw [smul_smul]; norm_num
    _ = 0 := by rw [hz, smul_zero]
private abbrev TriangleFlat (G : SimpleGraph V) (g : V → V → E) (ε : ℝ) :=
  ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l → ‖g i j + g j l - g i l‖ ≤ ε
private theorem defect_bound (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : TriangleFlat G g ε)
    {u v t : V} (huv : u ≠ v → G.Adj u v) (htu : t ≠ u → G.Adj t u)
    (htv : t ≠ v → G.Adj t v) : ‖g u v - (g t v - g t u)‖ ≤ ε := by
  by_cases h : u = v
  · subst v
    simpa [diag_zero g hrev] using hε
  by_cases hu : t = u
  · subst t
    simpa [diag_zero g hrev] using hε
  by_cases hv : t = v
  · subst t
    simpa [diag_zero g hrev, hrev u v] using hε
  convert htri t u v (htu hu) (huv h) (htv hv) using 1
  abel
private theorem star_residual {S : Finset V} (hS : S.Nonempty) (g : V → V → E) (u v : V) :
    g u v - (mean S (fun t => g t v) - mean S (fun t => g t u)) =
      mean S (fun t => g u v - (g t v - g t u)) := by
  rw [mean_sub, const_sub_mean hS]
private theorem star_bound {S : Finset V} (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : TriangleFlat G g ε)
    (hcl : G.IsClique (S : Set V)) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : G.Adj u v) :
    ‖g u v - (mean S (fun t => g t v) - mean S (fun t => g t u))‖ ≤
      (1 - 2 / (S.card : ℝ)) * ε := by
  classical
  let A := (S.erase u).erase v
  have hs : S.Nonempty := ⟨u, hu⟩
  have hc : A.card + 2 = S.card := by
    have h₁ := Finset.card_erase_add_one hu
    have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv.ne.symm, hv⟩)
    dsimp [A]
    omega
  have hp : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  rw [star_residual hs]
  calc
    _ ≤ ((A.card : ℝ) / S.card) * ε := by
      apply mean_bound ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      · intro t ht hta
        by_cases htu : t = u
        · subst t
          simp [diag_zero g hrev]
        have htv : t = v := by by_contra h; exact hta (by simp [htu, h, ht])
        subst t
        simp [diag_zero g hrev, hrev u v]
      · intro t ht
        have hts : t ∈ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _) ht
        exact defect_bound g ε hε hrev htri (fun _ => huv) (fun hn => hcl hts hu hn)
          (fun hn => hcl hts hv hn)
    _ = _ := by
      have hr : (A.card : ℝ) + 2 = S.card := by exact_mod_cast hc
      rw [show (A.card : ℝ) = S.card - 2 by linarith]
      field_simp
private noncomputable def bag [Finite V] (S : Set V) : Finset V :=
  S.toFinite.toFinset
@[simp] private theorem mem_bag [Finite V] {x : V} {S : Set V} : x ∈ bag S ↔ x ∈ S := by
  simp [bag]
@[simp] private theorem card_bag [Finite V] (S : Set V) : (bag S).card = S.ncard := by
  exact (Set.ncard_eq_toFinset_card S S.toFinite).symm
private theorem erase_fraction [DecidableEq V] {S : Finset V} {u : V} (hu : u ∈ S) :
    ((S.erase u).card : ℝ) / S.card = 1 - 1 / (S.card : ℝ) := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (show S.Nonempty from ⟨u, hu⟩).card_ne_zero
  have hc : ((S.erase u).card : ℝ) + 1 = S.card := by exact_mod_cast Finset.card_erase_add_one hu
  field_simp
  linarith
omit [NormedSpace ℝ E] in
private theorem fit_reverse (g : V → V → E) (hrev : ∀ i j, g j i = -g i j)
    (p : V → E) (u v : V) :
    ‖g v u - (p u - p v)‖ = ‖g u v - (p v - p u)‖ := by
  rw [hrev u v, show -g u v - (p u - p v) = -(g u v - (p v - p u)) by abel, norm_neg]
private theorem extend_bound {S : Finset V} {A : Set V} (hS : S.Nonempty)
    (hSA : (S : Set V) ⊆ A) (hcl : G.IsClique A)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : TriangleFlat G g ε)
    (p : V → E) (R : ℝ) (hR : 0 ≤ R)
    (hfit : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ‖g u v - (p v - p u)‖ ≤ R * ε)
    (m : ℕ) (hm : S.card ≤ m) :
    ∃ q : V → E, (∀ v ∈ S, q v = p v) ∧
      ∀ u ∈ A, ∀ v ∈ A, G.Adj u v →
        ‖g u v - (q v - q u)‖ ≤ (max (max R 1) ((1 - 1 / (m : ℝ)) * (1 + R))) * ε := by
  classical
  let q (v : V) := if v ∈ S then p v else mean S (fun t => p t + g t v)
  have mixed {u v : V} (hu : u ∈ S) (hv : v ∈ A) (hvs : v ∉ S) (huv : G.Adj u v) :
      ‖g u v - (q v - q u)‖ ≤ ((1 - 1 / (m : ℝ)) * (1 + R)) * ε := by
    have he : g u v - (q v - q u) =
        mean S (fun t => (g u v + p u) - (p t + g t v)) := by
      rw [show q u = p u by simp [q, hu],
        show q v = mean S (fun t => p t + g t v) by simp [q, hvs],
        ← const_sub_mean hS]
      abel
    have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hmR : (S.card : ℝ) ≤ m := by exact_mod_cast hm
    have hfraction : ((S.erase u).card : ℝ) / S.card ≤ 1 - 1 / (m : ℝ) := by
      rw [erase_fraction hu]
      linarith [one_div_le_one_div_of_le hpos hmR]
    rw [he]
    calc
      _ ≤ (((S.erase u).card : ℝ) / S.card) * ((1 + R) * ε) := by
        apply mean_bound (Finset.erase_subset _ _)
        · intro t ht hn
          have : t = u := by simpa [ht] using hn
          subst t
          abel
        · intro t ht
          obtain ⟨htu, hts⟩ := Finset.mem_erase.mp ht
          have hut := hcl (hSA hu) (hSA hts) htu.symm
          have hb := defect_bound g ε hε hrev htri (fun _ => huv) (fun _ => hut.symm)
            (fun h => hcl (hSA hts) hv h)
          rw [show g u v + p u - (p t + g t v) =
            (g u v - (g t v - g t u)) + (g u t - (p t - p u)) by rw [hrev u t]; abel]
          exact (norm_add_le _ _).trans (by linarith [hfit u hu t hts hut])
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hfraction (mul_nonneg (by linarith) hε)
  refine ⟨q, fun v hv => by simp [q, hv], fun u hu v hv huv => ?_⟩
  by_cases hus : u ∈ S
  · by_cases hvs : v ∈ S
    · exact (by simpa [q, hus, hvs] using hfit u hus v hvs huv :
        ‖g u v - (q v - q u)‖ ≤ R * ε).trans
          (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hε)
    · exact (mixed hus hv hvs huv).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  by_cases hvs : v ∈ S
  · rw [← fit_reverse g hrev q u v]
    exact (mixed hvs hu hus huv.symm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  have he : g u v - (q v - q u) = mean S (fun t => g u v - (g t v - g t u)) := by
    simp only [q, hus, hvs, ite_false]
    rw [mean_sub, const_sub_mean hS]
    congr 1
    funext t
    abel
  rw [he]
  refine (full_mean_bound hS (fun _ ht => defect_bound g ε hε hrev htri (fun _ => huv)
    (fun hn => hcl (hSA ht) hu hn) (fun hn => hcl (hSA ht) hv hn))).trans
    (mul_le_mul_of_nonneg_right ((le_max_right R 1).trans (le_max_left _ _)) hε)
omit [SeminormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem glue_equal {p : I → V → E} (hK : IsCliqueTree T G K)
    (hag : ∀ a b, T.Adj a b → ∀ x ∈ K a ∩ K b, p a x = p b x) :
    ∃ φ : V → E, ∀ a x, x ∈ K a → φ x = p a x := by
  classical
  have along {a b} (q : T.Walk a b) (x : V) (hx : ∀ c ∈ q.support, x ∈ K c) :
      p a x = p b x := by
    induction q with
    | nil => rfl
    | cons hab q ih =>
      exact (hag _ _ hab x ⟨hx _ (by simp), hx _ (by simp)⟩).trans
        (ih (fun c hc => hx c (by simp [hc])))
  refine ⟨fun x => p (hK.cover x).choose x, fun a x hx => ?_⟩
  obtain ⟨q, hq⟩ := (hK.isTree.existsUnique_path (hK.cover x).choose a).exists
  exact along q x (hK.running q hq x (hK.cover x).choose_spec hx)
private noncomputable def route (hT : T.IsTree) (r a : I) : T.Walk r a :=
  (hT.existsUnique_path r a).exists.choose
private theorem route_path (hT : T.IsTree) (r a : I) : (route hT r a).IsPath :=
  (hT.existsUnique_path r a).exists.choose_spec
private theorem path_eq_route (hT : T.IsTree) {r a : I} {p : T.Walk r a} (hp : p.IsPath) :
    p = route hT r a :=
  Subtype.mk.inj ((hT.isAcyclic.subsingleton_path r a).elim ⟨p, hp⟩ ⟨_, route_path hT r a⟩)
private theorem path_length (hT : T.IsTree) {r a : I} {p : T.Walk r a} (hp : p.IsPath) :
    p.length = T.dist r a := by
  obtain ⟨q, hq, hlen⟩ := hT.connected.exists_path_of_dist r a
  rw [path_eq_route hT hp, ← path_eq_route hT hq, hlen]
private theorem route_adj (hT : T.IsTree) (r : I) {a b : I} (h : T.Adj a b) :
    route hT r b = (route hT r a).concat h ∨
      route hT r a = (route hT r b).concat h.symm := by
  by_cases ha : a ∈ (route hT r b).support
  · exact Or.inl (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h ha)
  · exact Or.inr (hT.isAcyclic.path_concat (route_path ..) (route_path ..) h.symm
      (hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        (route_path ..) (route_path ..) h ha))

open Classical in
private theorem branch_distance (hT : T.IsTree) {r b : I} (h : T.Adj r b) (a : I) :
    if b ∈ (route hT r a).support then T.dist r a = T.dist b a + 1
    else T.dist b a = T.dist r a + 1 := by
  classical
  let p := route hT r a
  have hp := route_path hT r a
  split_ifs with ha
  · have hs : p.takeUntil b ha = (Walk.nil : T.Walk b b).cons h := by
      exact (path_eq_route hT (hp.takeUntil ha)).trans (path_eq_route hT (Path.singleton h).2).symm
    have hlen := congrArg Walk.length (p.take_spec ha)
    rw [Walk.length_append, hs, path_length hT (hp.dropUntil ha), path_length hT hp] at hlen
    simp only [Walk.length] at hlen
    omega
  · have hc : (p.cons h.symm).IsPath := (Walk.cons_isPath_iff ..).mpr ⟨hp, ha⟩
    rw [← path_length hT hc, Walk.length, path_length hT hp]
private theorem branch_separation (hT : T.IsTree) {r b x y : I} (h : T.Adj r b)
    (hx : b ∈ (route hT r x).support) (hy : b ∉ (route hT r y).support) :
    T.dist x y = T.dist r x + T.dist r y := by
  classical
  let p := route hT r x
  let q := route hT r y
  have hp := route_path hT r x
  have hq := route_path hT r y
  have hdis : p.reverse.support.Disjoint q.support.tail := by
    intro a ha haq
    have ha' : a ∈ p.support := by simpa [p.support_reverse] using ha
    have haq' : a ∈ q.support := List.mem_of_mem_tail haq
    have har : a ≠ r := by
      intro he
      subst a
      have hn := hq.support_nodup
      rw [← List.cons_head_tail q.support_ne_nil] at hn
      exact (List.nodup_cons.mp hn).1 (by simpa using haq)
    have hsame : p.takeUntil a ha' = q.takeUntil a haq' := by
      rw [path_eq_route hT (hp.takeUntil ha'), path_eq_route hT (hq.takeUntil haq')]
    have hs := hT.isAcyclic.eq_snd_of_adj_start hp h hx
    have hb : b ∈ (p.takeUntil a ha').support := by
      rw [hs, ← p.snd_takeUntil har ha']
      exact List.mem_of_mem_tail (Walk.snd_mem_tail_support (Walk.not_nil_of_ne har.symm))
    rw [hsame] at hb
    exact hy (q.support_takeUntil_subset_support haq' hb)
  have happ := (p.reverse.isPath_append q).mpr ⟨hp.reverse, hq.tail, hdis⟩
  rw [← path_length hT happ, Walk.length_append, Walk.length_reverse,
    path_length hT hp, path_length hT hq]
private theorem center_piece [Finite I] (hT : T.IsTree) (D : ℕ)
    (hD : ∀ a b, T.dist a b ≤ D) :
    ∃ r b, (r = b ∨ T.Adj r b) ∧ ∀ a, min (T.dist r a) (T.dist b a) ≤ D / 2 := by
  classical
  let := Fintype.ofFinite I
  let := hT.connected.nonempty
  let e (r : I) := Finset.univ.sup (T.dist r)
  have he (r a : I) : T.dist r a ≤ e r := Finset.le_sup (f := T.dist r) (Finset.mem_univ a)
  obtain ⟨r, -, hr⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  by_cases small : e r ≤ D / 2
  · exact ⟨r, r, Or.inl rfl, fun a => (min_le_left ..).trans ((he r a).trans small)⟩
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ (T.dist r) Finset.univ_nonempty
  have hxe : T.dist r x = e r :=
    (he r x).antisymm (Finset.sup_le fun a ha => hx a ha)
  have hrx : r ≠ x := by rintro rfl; simp at hxe; omega
  let p := route hT r x
  let b := p.snd
  have hp := Walk.not_nil_of_ne hrx (p := p)
  have hab : T.Adj r b := p.adj_snd hp
  have hbx : b ∈ (route hT r x).support := List.mem_of_mem_tail (p.snd_mem_tail_support hp)
  have hd (a : I) := branch_distance hT hab a
  have hout (a : I) (ha : b ∉ (route hT r a).support) : T.dist r a + e r ≤ D := by
    simpa [branch_separation hT hab hbx ha, hxe, add_comm] using hD x a
  have hf : e r ≤ D / 2 + 1 := by
    by_contra! hh
    have hlt : e b ≤ e r - 1 := Finset.sup_le fun a _ => by
      specialize hd a
      split_ifs at hd with ha
      · have := he r a; omega
      · have := hout a ha; omega
    have := hr b (Finset.mem_univ b)
    omega
  refine ⟨r, b, Or.inr hab, fun a => ?_⟩
  specialize hd a
  split_ifs at hd with ha
  · exact (min_le_right _ _).trans (by have := he r a; omega)
  · exact (min_le_left _ _).trans (by have := hout a ha; omega)
private theorem extend_layers [Finite V] (hK : IsCliqueTree T G K)
    (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (m : ℕ) (hm : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ m)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j)
    (htri : TriangleFlat G g ε)
    (d : I → ℕ) (parent : I → I)
    (hpar : ∀ a, 0 < d a → T.Adj (parent a) a ∧ d a = d (parent a) + 1)
    (hedge : ∀ a b, T.Adj a b →
      (d a = 0 ∧ d b = 0) ∨ parent b = a ∧ d b = d a + 1 ∨
        parent a = b ∧ d a = d b + 1)
    (p₀ : V → E) (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hinit : ∀ a, d a = 0 → ∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
      ‖g u v - (p₀ v - p₀ u)‖ ≤ R₀ * ε)
    (n : ℕ) (hn : ∀ a, d a ≤ n) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ cliqueTreeRadius m R₀ n * ε := by
  classical
  let R := cliqueTreeRadius m R₀
  have step (j : ℕ) : R j ≤ R (j + 1) := (le_max_left _ _).trans (le_max_left _ _)
  have hR (j : ℕ) : 0 ≤ R j := hR₀.trans (monotone_nat_of_le_succ step (Nat.zero_le j))
  have layers (j : ℕ) : ∃ p : I → V → E,
      (∀ a, d a ≤ j → ∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
        ‖g u v - (p a v - p a u)‖ ≤ R j * ε) ∧
      (∀ a b, T.Adj a b → d a ≤ j → d b ≤ j →
        ∀ x ∈ K a ∩ K b, p a x = p b x) := by
    induction j with
    | zero =>
      exact ⟨fun _ => p₀, fun a ha => hinit a (Nat.eq_zero_of_le_zero ha), by simp⟩
    | succ j ih =>
      obtain ⟨p, hp, hag⟩ := ih
      have next (a : I) (ha : d a = j + 1) : ∃ q : V → E,
          (∀ x ∈ K (parent a) ∩ K a, q x = p (parent a) x) ∧
          (∀ u ∈ K a, ∀ v ∈ K a, G.Adj u v →
            ‖g u v - (q v - q u)‖ ≤ R (j + 1) * ε) := by
        obtain ⟨hadj, hdepth⟩ := hpar a (by omega)
        let S := bag (K (parent a) ∩ K a)
        obtain ⟨x, hx⟩ := hs (parent a) a hadj
        have hS : S.Nonempty := ⟨x, mem_bag.mpr hx⟩
        have sub₁ : (S : Set V) ⊆ K (parent a) := fun _ hx => (mem_bag.mp hx).1
        have sub₂ : (S : Set V) ⊆ K a := fun _ hx => (mem_bag.mp hx).2
        obtain ⟨q, hq, he⟩ := extend_bound hS sub₂ (hK.clique a) g ε hε hrev htri
          (p (parent a)) (R j) (hR j)
          (fun u hu v hv huv => hp _ (by omega) u (sub₁ hu) v (sub₁ hv) huv)
          m (by simpa [S] using hm _ _ hadj)
        exact ⟨q, fun x hx => hq x (mem_bag.mpr hx), he⟩
      let q (a : I) := if ha : d a = j + 1 then (next a ha).choose else p a
      have old (a : I) (ha : d a ≤ j) : q a = p a := dite_eq_right (by omega)
      have fresh (a : I) (ha : d a = j + 1) : q a = (next a ha).choose := dite_eq_left ha
      have agree (a b : I) (hab : T.Adj a b) (hb : d b ≤ j + 1)
          (hpar : parent b = a) (hdep : d b = d a + 1) (x : V) (hx : x ∈ K a ∩ K b) :
          q a x = q b x := by
        rw [old a (by omega)]
        by_cases h : d b ≤ j
        · rw [old b h]
          exact hag a b hab (by omega) h x hx
        · have hd : d b = j + 1 := by omega
          rw [fresh b hd]
          simpa only [hpar] using ((next b hd).choose_spec.1 x (hpar.symm ▸ hx)).symm
      refine ⟨q, fun a ha u hu v hv huv => ?_, fun a b hab ha hb x hx => ?_⟩
      · by_cases h : d a ≤ j
        · rw [old a h]
          exact (hp a h u hu v hv huv).trans (mul_le_mul_of_nonneg_right (step j) hε)
        · have hd : d a = j + 1 := by omega
          rw [fresh a hd]
          exact (next a hd).choose_spec.2 u hu v hv huv
      · rcases hedge a b hab with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
        · rw [old a (by omega), old b (by omega)]
          exact hag a b hab (by omega) (by omega) x hx
        · exact agree a b hab hb h₀ h₁ x hx
        · exact (agree b a hab.symm ha h₀ h₁ x ⟨hx.2, hx.1⟩).symm
  obtain ⟨p, hp, hag⟩ := layers n
  obtain ⟨φ, hφ⟩ := glue_equal hK (fun a b hab => hag a b hab (hn a) (hn b))
  refine ⟨φ, fun u v huv => ?_⟩
  obtain ⟨a, hu, hv⟩ := hK.edge u v huv
  rw [hφ a u hu, hφ a v hv]
  exact hp a (hn a) u hu v hv huv
private theorem rooted_layers (hT : T.IsTree) {r b : I} (hrb : r = b ∨ T.Adj r b) :
    ∃ d : I → ℕ, ∃ parent : I → I,
      (∀ a, d a = min (T.dist r a) (T.dist b a)) ∧
      (∀ a, d a = 0 → a = r ∨ a = b) ∧
      (∀ a, 0 < d a → T.Adj (parent a) a ∧ d a = d (parent a) + 1) ∧
      (∀ a a', T.Adj a a' →
        (d a = 0 ∧ d a' = 0) ∨ parent a' = a ∧ d a' = d a + 1 ∨
          parent a = a' ∧ d a = d a' + 1) := by
  classical
  let d (a : I) := min (T.dist r a) (T.dist b a)
  let parent (a : I) := (route hT r a).penultimate
  have depth (a : I) : d a = T.dist r a -
      (if r ≠ b ∧ b ∈ (route hT r a).support then 1 else 0) := by
    rcases hrb with he | ha
    · subst b
      simp [d]
    have hh := branch_distance hT ha a
    split_ifs at hh with hs <;> simp [d, hs, ha.ne, hh]
  have orient {a a' : I} (h : T.Adj a a') (he : route hT r a' = (route hT r a).concat h) :
      parent a' = a ∧ ((d a = 0 ∧ d a' = 0) ∨ d a' = d a + 1) := by
    have hlen : T.dist r a' = T.dist r a + 1 := by
      rw [← path_length hT (route_path hT r a'), he, Walk.length_concat,
        path_length hT (route_path hT r a)]
    refine ⟨by simp [parent, he, Walk.penultimate_concat], ?_⟩
    by_cases hnew : r ≠ b ∧ b = a' ∧ b ∉ (route hT r a).support
    · obtain ⟨hne, rfl, _⟩ := hnew
      have hb : T.Adj r b := hrb.resolve_left hne
      have := T.dist_eq_one_iff_adj.mpr hb
      have hz : T.dist r a = 0 := by omega
      have ha : a = r := (hT.connected.dist_eq_zero_iff.mp hz).symm
      subst a
      exact Or.inl ⟨by simp [d], by simp [d]⟩
    · right
      have hx : (r ≠ b ∧ b ∈ (route hT r a').support) ↔
          (r ≠ b ∧ b ∈ (route hT r a).support) := by
        simp only [he, Walk.support_concat, List.mem_append, List.mem_singleton]
        tauto
      rw [depth, depth, hlen]
      by_cases hs : r ≠ b ∧ b ∈ (route hT r a).support
      · rw [ite_eq_left hs, ite_eq_left (hx.mpr hs)]
        have hd : T.dist r a ≠ 0 := by
          intro hz
          have ha : a = r := (hT.connected.dist_eq_zero_iff.mp hz).symm
          subst a
          have hnil : route hT r r = .nil := (path_eq_route hT Walk.IsPath.nil).symm
          exact hs.1 (by simpa [hnil, eq_comm] using hs.2)
        omega
      · simp [hs, show ¬ (r ≠ b ∧ b ∈ (route hT r a').support) from fun hh => hs (hx.mp hh)]
  refine ⟨d, parent, fun _ => rfl, fun a ha => ?_, fun a ha => ?_, fun a a' h => ?_⟩
  · change min (T.dist r a) (T.dist b a) = 0 at ha
    rcases min_cases (T.dist r a) (T.dist b a) with he | he
    · exact Or.inl (hT.connected.dist_eq_zero_iff.mp (he.1.symm.trans ha)).symm
    · exact Or.inr (hT.connected.dist_eq_zero_iff.mp (he.1.symm.trans ha)).symm
  · have hne : r ≠ a := by
      rintro rfl
      simp [d] at ha
    let p := route hT r a
    have hh := p.adj_penultimate (Walk.not_nil_of_ne hne)
    have hp : p.dropLast.IsPath := (route_path hT r a).dropLast
    have he : route hT r a = (route hT r p.penultimate).concat hh := by
      rw [← path_eq_route hT hp, Walk.concat_dropLast]
    exact ⟨hh, (orient hh he).2.resolve_left (fun h => (Nat.ne_of_gt ha) h.2)⟩
  · rcases route_adj hT r h with ha | ha
    · obtain ⟨hp, hz | hd⟩ := orient h ha
      · exact Or.inl hz
      · exact Or.inr (Or.inl ⟨hp, hd⟩)
    · obtain ⟨hp, hz | hd⟩ := orient h.symm ha
      · exact Or.inl hz.symm
      · exact Or.inr (Or.inr ⟨hp, hd⟩)

end CliqueTreeBanach

open CliqueTreeBanach in
/-- Extension from one central clique or two adjacent central cliques gives the radius recurrence. -/
theorem cliqueTree_center_extension_banach_potential {V : Type u} [Finite V] {I : Type w}
    [Finite I] {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (hK : IsCliqueTree T G K) (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (m : ℕ) (_hm : 1 ≤ m) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ m)
    (D : ℕ) (hD : ∀ a b, T.dist a b ≤ D)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ cliqueTreeRadius m 1 (D / 2) * ε := by
  classical
  obtain ⟨r, b, hab, hr⟩ := center_piece hK.isTree D hD
  obtain ⟨d, p, hd, hz, hp, he⟩ := rooted_layers hK.isTree hab
  let S := bag (K r ∩ K b)
  refine extend_layers hK hs m hsep g ε hε hrev htri d p hp he
    (fun v => mean S (fun t => g t v)) 1 (by norm_num) ?_ (D / 2) (fun a => (hd a).symm ▸ hr a)
  intro a ha u hu v hv huv
  have hsub : (S : Set V) ⊆ K a := by
    rcases hz a ha with rfl | rfl
    · exact fun _ ht => (mem_bag.mp ht).1
    · exact fun _ ht => (mem_bag.mp ht).2
  obtain ⟨x, hx⟩ : (K r ∩ K b).Nonempty := hab.elim
    (fun he => ⟨u, by rcases hz a ha with rfl | rfl <;> simpa [he] using hu⟩) (hs r b)
  have hS : S.Nonempty := ⟨x, mem_bag.mpr hx⟩
  rw [star_residual hS]
  exact full_mean_bound hS (fun _ ht => defect_bound g ε hε hrev htri (fun _ => huv)
    (fun hn => hK.clique a (hsub ht) hu hn) (fun hn => hK.clique a (hsub ht) hv hn))

namespace CliqueTreeBanach
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
private noncomputable def maxZero (s : Finset ℝ) : ℝ := by
  classical
  exact (insert 0 s).max' (Finset.insert_nonempty ..)
private theorem le_maxZero {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) : x ≤ maxZero s := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hx)
private theorem maxZero_lt {s : Finset ℝ} {k : ℝ} (hk : 0 < k)
    (h : ∀ x ∈ s, x < k) : maxZero s < k := by
  classical
  have hm := Finset.max'_mem (insert 0 s) (Finset.insert_nonempty ..)
  rcases Finset.mem_insert.mp hm with he | he
  · simpa [maxZero, he] using hk
  · exact h _ he

/-- Sum of the two largest incident separator coefficients, with zero padding. -/
noncomputable def twoShifts [Finite I] (T : SimpleGraph I) (K : I → Set V) (a : I) : ℝ := by
  classical
  letI := Fintype.ofFinite (Option I × Option I)
  let weight : Option I → ℝ := fun b => b.elim 0 (fun b => if T.Adj a b then sepShift K a b else 0)
  exact maxZero (Finset.univ.image fun b : Option I × Option I =>
    if b.1 = b.2 then 0 else weight b.1 + weight b.2)
private theorem sepShift_bounds [Finite V] (h : (K (a : I) ∩ K (b : I)).Nonempty) :
    0 ≤ sepShift K a b ∧ sepShift K a b < 1 := by
  have hp : (1 : ℝ) ≤ (K a ∩ K b).ncard := by exact_mod_cast h.ncard_pos
  have hle : ((K a ∩ K b).ncard : ℝ) ≤ ((max (K a).ncard (K b).ncard : ℕ) : ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard Set.inter_subset_left).trans
      (le_max_left (K a).ncard (K b).ncard)
  have hm : (0 : ℝ) < ((max (K a).ncard (K b).ncard : ℕ) : ℝ) := by linarith
  have h₁ := sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℝ) < (K a ∩ K b).ncard)).2 hp)
  exact ⟨mul_nonneg h₁ (sub_nonneg.mpr ((div_le_one hm).2 hle)),
    (mul_le_of_le_one_right h₁ (sub_le_self _ (by positivity))).trans_lt (sub_lt_self _ (by positivity))⟩
private theorem weighted_bound {A : Finset V} (w : V → ℝ) (f : V → E) (ε : ℝ)
    (hw : ∀ t ∈ A, 0 ≤ w t) (hf : ∀ t ∈ A, ‖f t‖ ≤ ε) :
    ‖∑ t ∈ A, w t • f t‖ ≤ (∑ t ∈ A, w t) * ε := by
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw t ht)]
  exact mul_le_mul_of_nonneg_left (hf t ht) (hw t ht)
private theorem common_stars {A S : Finset V} (hS : S ⊆ A) (ha : A.Nonempty)
    (f : V → E) (ε q : ℝ) (hqa : q ≤ (A.card : ℝ)⁻¹)
    (hf : ∀ t ∈ A, ‖f t‖ ≤ ε) :
    ‖mean A f - q • ∑ t ∈ S, f t‖ ≤ (1 - S.card * q) * ε := by
  classical
  let w (t : V) := (A.card : ℝ)⁻¹ - if t ∈ S then q else 0
  have hi : A.filter (fun t => t ∈ S) = S := by ext t; exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hS h, h⟩⟩
  have he : mean A f - q • ∑ t ∈ S, f t = ∑ t ∈ A, w t • f t := by
    simp only [w, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, mean]
    congr 1
    simp only [ite_smul, zero_smul, ← Finset.sum_filter, hi, ← Finset.smul_sum]
  have hsum : ∑ t ∈ A, w t = 1 - S.card * q := by
    have hn : (A.card : ℝ) ≠ 0 := by exact_mod_cast ha.card_ne_zero
    simp only [w, Finset.sum_sub_distrib, ← Finset.sum_filter, hi, Finset.sum_const, nsmul_eq_mul]
    rw [mul_inv_cancel₀ hn]
  rw [he, ← hsum]
  apply weighted_bound w f ε _ hf
  intro t _
  by_cases ht : t ∈ S <;> simp [w, ht, sub_nonneg, hqa, inv_nonneg]
private def transport {T : SimpleGraph I} (d : I → I → E) {a b : I} : T.Walk a b → E
  | .nil => 0
  | .cons' x y _ _ p => d x y + transport d p
omit [NormedSpace ℝ E] in
private theorem transport_concat (d : I → I → E) {a b c : I}
    (p : T.Walk a b) (h : T.Adj b c) :
    transport d (p.concat h) = transport d p + d b c := by
  induction p with
  | nil => simp [Walk.concat, transport]
  | cons h' p ih =>
    change _ + transport d (p.concat h) = (_ + transport d p) + d _ _
    rw [ih, add_assoc]
private theorem shared_adj [Finite I] (hK : IsCliqueTree T G K)
    (h₂ : ∀ v : V, {i : I | v ∈ K i}.ncard ≤ 2)
    {a b : I} {x : V} (ha : x ∈ K a) (hb : x ∈ K b) (hab : a ≠ b) : T.Adj a b := by
  classical
  let p := route hK.isTree a b
  have hp := route_path hK.isTree a b
  have hsub : p.support.toFinset ⊆ bag {i : I | x ∈ K i} := by
    intro c hc
    exact mem_bag.mpr (hK.running p hp x ha hb c (List.mem_toFinset.mp hc))
  have hle : p.support.toFinset.card ≤ 2 := (Finset.card_le_card hsub).trans (by simpa using h₂ x)
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support, path_length hK.isTree hp] at hle
  exact T.dist_eq_one_iff_adj.mp (by have := hK.isTree.connected.pos_dist_of_ne hab; omega)
private theorem shared_unique [Finite I] (h₂ : ∀ v : V, {i : I | v ∈ K i}.ncard ≤ 2)
    {a b c : I} {x : V} (ha : x ∈ K a) (hb : x ∈ K b) (hc : x ∈ K c)
    (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  classical
  by_contra hbc
  have h : ({a, b, c} : Set I) ⊆ {i : I | x ∈ K i} := by
    simp [Set.insert_subset_iff, ha, hb, hc]
  have hle := (Set.ncard_le_ncard h).trans (h₂ x)
  simp [Set.ncard_insert_of_notMem, hab, hac, hbc] at hle

end CliqueTreeBanach

/-- The largest local midpoint bound, with value zero when no bag contains an edge. -/
noncomputable def cliqueTreeMidpointCoeff {V : Type u} {I : Type w} [Finite I]
    (T : SimpleGraph I) (K : I → Set V) : ℝ :=
  CliqueTreeBanach.maxZero ((CliqueTreeBanach.bag {a : I | 2 ≤ (K a).ncard}).image
    (fun a => 1 - 2 / ((K a).ncard : ℝ) + CliqueTreeBanach.twoShifts T K a))

open CliqueTreeBanach in
/-- Translated clique star means and separator midpoints give a coefficient strictly below three. -/
theorem cliqueTree_twoClique_midpoint_banach_potential {V : Type u} [Finite V] {I : Type w}
    [Finite I] {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (hK : IsCliqueTree T G K) (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (h₂ : ∀ x : V, {i : I | x ∈ K i}.ncard ≤ 2)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    cliqueTreeMidpointCoeff T K < 3 ∧ ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ cliqueTreeMidpointCoeff T K * ε := by
  classical
  let := Fintype.ofFinite (Option I × Option I)
  let A (a : I) := bag (K a)
  let S (a b : I) := bag (K a ∩ K b)
  let C (a : I) := 1 - 2 / ((K a).ncard : ℝ)
  let w (a : I) (b : Option I) := b.elim 0 (fun b => if T.Adj a b then sepShift K a b else 0)
  have wlt (a : I) (b : Option I) : w a b < 1 := by
    cases b with
    | none => norm_num [w]
    | some b =>
      by_cases h : T.Adj a b
      · simpa [w, h] using (sepShift_bounds (hs a b h)).2
      · norm_num [w, h]
  have wpair (a : I) (b c : Option I) :
      (if b = c then 0 else w a b + w a c) ≤ twoShifts T K a := by
    unfold twoShifts
    exact le_maxZero (Finset.mem_image.mpr ⟨(b, c), Finset.mem_univ _, rfl⟩)
  have padding (a : I) : 0 ≤ twoShifts T K a := by simpa using wpair a none none
  refine ⟨maxZero_lt (by norm_num) (fun k hk => ?_), ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    have ht : twoShifts T K a < 2 := by
      unfold twoShifts
      refine maxZero_lt (by norm_num) (fun n hn => ?_)
      obtain ⟨⟨b, c⟩, -, rfl⟩ := Finset.mem_image.mp hn
      split_ifs
      · norm_num
      · convert add_lt_add (wlt a b) (wlt a c) using 1 <;> norm_num
    exact (add_lt_add_of_le_of_lt (sub_le_self (1 : ℝ) (by positivity)) ht).trans_le (by norm_num)
  let p (a : I) (x : V) := mean (A a) (fun t => g t x)
  let gain (a b : I) := mean (S a b) (fun x => p a x - p b x)
  have rev (a b : I) : gain b a = -gain a b := by
    simp only [gain, S, Set.inter_comm (K b) (K a), ← mean_sub]
    abel
  let root := hK.isTree.connected.nonempty.some
  let c (a : I) := transport gain (route hK.isTree root a)
  have offset (a b : I) (hab : T.Adj a b) : c b - c a = gain a b := by
    rcases route_adj hK.isTree root hab with h | h
    · simp only [c, h, transport_concat]; abel
    · simp only [c, h, transport_concat, rev a b]; abel
  let ψ (a : I) (x : V) := p a x + c a
  have fit (a : I) (u v : V) (hu : u ∈ K a) (hv : v ∈ K a) (h : G.Adj u v) :
      ‖g u v - (ψ a v - ψ a u)‖ ≤ C a * ε := by
    have hcl : G.IsClique (A a : Set V) := fun _ hx _ hy =>
      hK.clique a (mem_bag.mp hx) (mem_bag.mp hy)
    simpa [ψ, p, C, A, add_sub_add_right_eq_sub] using
      star_bound g ε hε hrev htri hcl (mem_bag.mpr hu) (mem_bag.mpr hv) h
  have shift (a b : I) (hab : T.Adj a b) (u : V) (hu : u ∈ K a ∩ K b) :
      ‖(1 / 2 : ℝ) • (ψ a u + ψ b u) - ψ a u‖ ≤ sepShift K a b * ε := by
    let B := S a b
    have huB : u ∈ B := mem_bag.mpr hu
    have hB : B.Nonempty := ⟨u, huB⟩
    have ha : (A a).Nonempty := ⟨u, mem_bag.mpr hu.1⟩
    have hb : (A b).Nonempty := ⟨u, mem_bag.mpr hu.2⟩
    let q : ℝ := ((max (K a).ncard (K b).ncard : ℕ) : ℝ)⁻¹
    have inc (v : V) (hv : v ∈ B) :
        ‖(p b u - p a u) - (p b v - p a v)‖ ≤ 2 * (1 - B.card * q) * ε := by
      have hv' : v ∈ K a ∩ K b := mem_bag.mp hv
      let F (t : V) := g u v - (g t v - g t u)
      have cancel (j : I) (huj : u ∈ K j) (hvj : v ∈ K j) (hsub : (B : Set V) ⊆ K j)
          (hj : (K j).ncard ≤ max (K a).ncard (K b).ncard) :
          ‖mean (A j) F - q • ∑ t ∈ B, F t‖ ≤ (1 - B.card * q) * ε := by
        have hpos : (0 : ℝ) < (A j).card := by
          exact_mod_cast (show (A j).Nonempty from ⟨u, mem_bag.mpr huj⟩).card_pos
        exact common_stars (fun x hx => mem_bag.mpr (hsub hx)) ⟨u, mem_bag.mpr huj⟩
          F ε q (inv_anti₀ hpos (by exact_mod_cast (by simpa [A] using hj)))
          (fun t ht => defect_bound g ε hε hrev htri (hK.clique j huj hvj)
            (fun hn => hK.clique j (mem_bag.mp ht) huj hn)
            (fun hn => hK.clique j (mem_bag.mp ht) hvj hn))
      have h₁ := cancel a hu.1 hv'.1 (fun _ hx => (mem_bag.mp hx).1) (le_max_left ..)
      have h₂ := cancel b hu.2 hv'.2 (fun _ hx => (mem_bag.mp hx).2) (le_max_right ..)
      rw [show (p b u - p a u) - (p b v - p a v) =
        (mean (A b) F - q • ∑ t ∈ B, F t) - (mean (A a) F - q • ∑ t ∈ B, F t) by
          rw [← star_residual ha g u v, ← star_residual hb g u v]; dsimp [p]; abel]
      exact (norm_sub_le _ _).trans (by linarith)
    have hdiff : ψ b u - ψ a u = mean B
        (fun v => (p b u - p a u) - (p b v - p a v)) := by
      rw [← const_sub_mean hB]
      change (p b u + c b) - (p a u + c a) = _
      rw [show (p b u + c b) - (p a u + c a) =
        p b u - p a u + (c b - c a) by abel, offset a b hab]
      simp only [gain, B, ← mean_sub]
      abel
    have hnorm := mean_bound (Finset.erase_subset u B) _ (2 * (1 - B.card * q) * ε)
      (fun v hv hn => by rw [show v = u by simpa [hv] using hn, sub_self])
      (fun v hv => inc v (Finset.mem_of_mem_erase hv))
    rw [show (1 / 2 : ℝ) • (ψ a u + ψ b u) - ψ a u =
      (1 / 2 : ℝ) • (ψ b u - ψ a u) by module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hdiff]
    refine (mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans_eq ?_
    rw [erase_fraction huB]
    simp only [sepShift, q, B, S, card_bag, div_eq_mul_inv]
    ring
  have coeff (a : I) (u v : V) (hu : u ∈ K a) (hv : v ∈ K a) (hne : u ≠ v) :
      C a + twoShifts T K a ≤ cliqueTreeMidpointCoeff T K := by
    have hn : 2 ≤ (K a).ncard := by
      have sub : ({u, v} : Set V) ⊆ K a := by simp [Set.insert_subset_iff, hu, hv]
      simpa [hne] using Set.ncard_le_ncard sub
    exact le_maxZero (Finset.mem_image.mpr ⟨a, mem_bag.mpr hn, rfl⟩)
  let attached (a : I) (x : V) := ∃ b, a ≠ b ∧ x ∈ K b
  let idx (a : I) (x : V) : Option I :=
    if h : attached a x then some h.choose else none
  let mid (a : I) (x : V) : E := (idx a x).elim (ψ a x) (fun b => (1 / 2 : ℝ) • (ψ a x + ψ b x))
  have shared (a b : I) (x : V) (ha : x ∈ K a) (hb : x ∈ K b) (hab : a ≠ b) :
      idx a x = some b := by
    have h : attached a x := ⟨b, hab, hb⟩
    simp [idx, h, shared_unique h₂ ha h.choose_spec.2 hb h.choose_spec.1 hab]
  have close (a : I) (x : V) (ha : x ∈ K a) :
      ‖mid a x - ψ a x‖ ≤ w a (idx a x) * ε := by
    by_cases h : attached a x
    · have hj := shared_adj hK h₂ ha h.choose_spec.2 h.choose_spec.1
      simpa [w, hj, mid, idx, h] using shift a h.choose hj x ⟨ha, h.choose_spec.2⟩
    · simp [mid, idx, w, h]
  let Φ (x : V) := mid (hK.cover x).choose x
  have agree (a : I) (x : V) (ha : x ∈ K a) : Φ x = mid a x := by
    let b := (hK.cover x).choose
    have hb : x ∈ K b := (hK.cover x).choose_spec
    change mid b x = mid a x
    by_cases hab : a = b
    · rw [hab]
    · simp [mid, shared a b x ha hb hab, shared b a x hb ha (Ne.symm hab), add_comm]
  refine ⟨Φ, fun u v huv => ?_⟩
  obtain ⟨a, hu, hv⟩ := hK.edge u v huv
  rw [agree a u hu, agree a v hv]
  have local_le (j : I) (hj : u ∈ K j) (hj' : v ∈ K j) : C j ≤ cliqueTreeMidpointCoeff T K :=
    (le_add_of_nonneg_right (padding j)).trans (coeff j u v hj hj' huv.ne)
  have ca := coeff a u v hu hv huv.ne
  by_cases he : idx a u = idx a v
  · cases h : idx a u with
    | none =>
      have hv' : idx a v = none := he.symm.trans h
      simpa [mid, h, hv'] using (fit a u v hu hv huv).trans
        (mul_le_mul_of_nonneg_right (local_le a hu hv) hε)
    | some b =>
      have hv' : idx a v = some b := he.symm.trans h
      have inBag (x : V) (hx : idx a x = some b) : x ∈ K b := by
        by_cases hh : attached a x
        · have eq : hh.choose = b := by simpa [idx, hh] using hx
          exact eq ▸ hh.choose_spec.2
        · simp [idx, hh] at hx
      have ub := inBag u h
      have vb := inBag v hv'
      simp only [mid, h, hv', Option.elim_some]
      rw [show g u v - ((1 / 2 : ℝ) • (ψ a v + ψ b v) - (1 / 2 : ℝ) • (ψ a u + ψ b u)) =
        (1 / 2 : ℝ) • ((g u v - (ψ a v - ψ a u)) + (g u v - (ψ b v - ψ b u))) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have fitM (j : I) (uj : u ∈ K j) (vj : v ∈ K j) :=
        (fit j u v uj vj huv).trans (mul_le_mul_of_nonneg_right (local_le j uj vj) hε)
      exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)).trans
        (by linarith [fitM a hu hv, fitM b ub vb])
  · rw [show g u v - (mid a v - mid a u) = (g u v - (ψ a v - ψ a u)) +
      ((mid a u - ψ a u) - (mid a v - ψ a v)) by abel]
    have hmove := (norm_sub_le _ _).trans (add_le_add (close a u hu) (close a v hv))
    have hpair : w a (idx a u) + w a (idx a v) ≤ twoShifts T K a := by
      simpa [he] using wpair a (idx a u) (idx a v)
    exact (norm_add_le _ _).trans
      ((add_le_add (fit a u v hu hv huv) hmove).trans (by
        rw [← add_mul, ← add_mul]
        exact mul_le_mul_of_nonneg_right ((add_le_add_right hpair _).trans ca) hε))

#print axioms cliqueTree_center_extension_banach_potential
#print axioms cliqueTree_twoClique_midpoint_banach_potential

end SimpleGraph
