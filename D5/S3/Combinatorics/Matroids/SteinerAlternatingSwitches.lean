/- GID: D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerAlternatingSwitches
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The large components of two translations give exactly the successful Steiner switches. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations

/-! # Successful switches in a point-deleted Steiner system -/

namespace D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches

open Set SimpleGraph
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open PointDeletedSteinerSwitch (pointDeletedFamily point_deleted_switch)
open SteinerMatchingTranslations

/-- Two perfect matchings with distinct partners at each vertex. -/
private structure Matchings (V : Type*) where
  first : V → V
  second : V → V
  first_involutive : Function.Involutive first
  second_involutive : Function.Involutive second
  first_ne_self : ∀ x, first x ≠ x
  second_ne_self : ∀ x, second x ≠ x
  partners_ne : ∀ x, first x ≠ second x

namespace Matchings

variable {V : Type*} (M : Matchings V)

/-- The union of the two undirected perfect matchings. -/
private def graph : SimpleGraph V where
  Adj x y := M.first x = y ∨ M.second x = y
  symm := ⟨by
    intro x y h
    rcases h with e | e
    · exact Or.inl (e ▸ M.first_involutive x)
    · exact Or.inr (e ▸ M.second_involutive x)⟩
  loopless := ⟨fun x h => h.elim (M.first_ne_self x) (M.second_ne_self x)⟩

private theorem stepFirst (x : V) : M.graph.Reachable x (M.first x) :=
  (show M.graph.Adj x (M.first x) from Or.inl rfl).reachable

private theorem stepSecond (x : V) : M.graph.Reachable x (M.second x) :=
  (show M.graph.Adj x (M.second x) from Or.inr rfl).reachable

private theorem supp_eq_reachable (x : V) :
    (M.graph.connectedComponentMk x).supp = {y | M.graph.Reachable x y} := by
  ext y
  exact ConnectedComponent.eq.trans ⟨Reachable.symm, Reachable.symm⟩

/-- At a commuting vertex the entire connected component consists of the four corners. -/
private theorem component_eq_square {x : V} (h : M.first (M.second x) = M.second (M.first x)) :
    (M.graph.connectedComponentMk x).supp =
      {x, M.first x, M.second x, M.first (M.second x)} := by
  let corners : Set V := {x, M.first x, M.second x, M.first (M.second x)}
  have closed {u v : V} (hu : u ∈ corners) (edge : M.graph.Adj u v) : v ∈ corners := by
    change M.first u = v ∨ M.second u = v at edge
    have hf := M.first_involutive
    have hg := M.second_involutive
    have finish : M.second (M.first (M.second x)) = M.first x := by
      rw [h, hg]
    simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl <;> rcases edge with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl (hf _)
    · exact Or.inr (Or.inr (Or.inr h.symm))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (hg _)
    · exact Or.inr (Or.inr (Or.inl (hf _)))
    · exact Or.inr (Or.inl finish)
  rw [M.supp_eq_reachable x]
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · change M.graph.Reachable x y at hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy
    induction hy with
    | refl => simp
    | tail _ edge ih => exact closed ih edge
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Reachable.rfl
    · exact M.stepFirst x
    · exact M.stepSecond x
    · exact (M.stepSecond x).trans (M.stepFirst (M.second x))

private theorem square_card [Finite V] (x : V) :
    ({x, M.first x, M.second x, M.first (M.second x)} : Set V).ncard = 4 := by
  have hf := M.first_involutive
  have hg := M.second_involutive
  have nf := M.first_ne_self
  have ng := M.second_ne_self
  have nd := M.partners_ne
  have h₁ : x ∉ ({M.first x, M.second x, M.first (M.second x)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₂ : M.first x ∉ ({M.second x, M.first (M.second x)} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₃ : M.second x ∉ ({M.first (M.second x)} : Set V) := by
    simpa using (nf (M.second x)).symm
  rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂,
    Set.ncard_insert_of_notMem h₃, Set.ncard_singleton]

/-- A failure of commutation exhibits six distinct vertices in the same component. -/
private theorem six_le_component_of_noncommute [Finite V] {x : V}
    (h : M.first (M.second x) ≠ M.second (M.first x)) :
    6 ≤ (M.graph.connectedComponentMk x).supp.ncard := by
  let f := M.first
  let g := M.second
  change f (g x) ≠ g (f x) at h
  let six : Set V := {x, f x, g x, f (g x), g (f x), f (g (f x))}
  have hf : Function.Involutive f := M.first_involutive
  have hg : Function.Involutive g := M.second_involutive
  have nf : ∀ y, f y ≠ y := M.first_ne_self
  have ng : ∀ y, g y ≠ y := M.second_ne_self
  have nd : ∀ y, f y ≠ g y := M.partners_ne
  have h₁ : x ∉ ({f x, g x, f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₂ : f x ∉ ({g x, f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₃ : g x ∉ ({f (g x), g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₄ : f (g x) ∉ ({g (f x), f (g (f x))} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    grind [Function.Involutive]
  have h₅ : g (f x) ∉ ({f (g (f x))} : Set V) := by
    simpa using (nf (g (f x))).symm
  have count : six.ncard = 6 := by
    dsimp [six]
    rw [Set.ncard_insert_of_notMem h₁, Set.ncard_insert_of_notMem h₂,
      Set.ncard_insert_of_notMem h₃, Set.ncard_insert_of_notMem h₄,
      Set.ncard_insert_of_notMem h₅, Set.ncard_singleton]
  rw [← count, M.supp_eq_reachable x]
  refine Set.ncard_le_ncard (fun y hy => ?_) (Set.toFinite _)
  simp only [six, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Reachable.rfl
  · exact M.stepFirst x
  · exact M.stepSecond x
  · exact (M.stepSecond x).trans (M.stepFirst (g x))
  · exact (M.stepFirst x).trans (M.stepSecond (f x))
  · exact ((M.stepFirst x).trans (M.stepSecond (f x))).trans (M.stepFirst (g (f x)))

/-- A vertex fails to commute exactly when its component has at least six vertices. -/
private theorem noncommute_iff_six_le_component [Finite V] (x : V) :
    M.first (M.second x) ≠ M.second (M.first x) ↔
      6 ≤ (M.graph.connectedComponentMk x).supp.ncard := by
  refine ⟨M.six_le_component_of_noncommute, fun size h => ?_⟩
  rw [M.component_eq_square h, M.square_card x] at size
  omega

/-- A total vertex count not divisible by four forces a component with at least six vertices. -/
private theorem exists_large_component_of_not_dvd [Fintype V] (hcard : ¬ 4 ∣ Fintype.card V) :
    ∃ C : M.graph.ConnectedComponent, 6 ≤ C.supp.ncard := by
  classical
  by_contra! h
  let _ := Fintype.ofFinite M.graph.ConnectedComponent
  have four (C : M.graph.ConnectedComponent) : C.supp.ncard = 4 := by
    induction C using ConnectedComponent.ind with
    | _ x =>
      have hc : M.first (M.second x) = M.second (M.first x) := by
        by_contra nh
        exact (Nat.not_le_of_gt (h _)) ((M.noncommute_iff_six_le_component x).mp nh)
      rw [M.component_eq_square hc, M.square_card x]
  have count : Fintype.card V = ∑ C : M.graph.ConnectedComponent, C.supp.ncard := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := M.graph.connectedComponentMk) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    exact Finset.sum_congr rfl fun C _ => by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [count] at hcard
  simp only [four, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcard
  exact hcard (dvd_mul_left 4 _)

end Matchings

/-- The two matching translations for deletion at q and a fixed pivot. -/
private noncomputable def pivotMatchings {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) (v : Fin r) : Matchings (Option (Fin (r + 1))) where
  first := translate valid complete q
  second := translate valid complete (q.succAbove v)
  first_involutive := translate_involutive valid complete q
  second_involutive := translate_involutive valid complete (q.succAbove v)
  first_ne_self := translate_ne_self valid complete q
  second_ne_self := translate_ne_self valid complete (q.succAbove v)
  partners_ne := translate_ne_translate valid complete (Fin.succAbove_ne q v).symm

/-- The graph whose two edges at each point come from the deleted and retained pivots. -/
noncomputable def pivotGraph {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) (v : Fin r) : SimpleGraph (Option (Fin (r + 1))) :=
  (pivotMatchings valid complete q v).graph

/-- A starting label with the two retained blocks and a successful switch. -/
def SuccessfulStart {r : ℕ} (P : Set (Set (Fin r))) (m : Fin r → Fin r) (v a : Fin r) : Prop :=
  v ≠ a ∧ v ≠ m a ∧
    ∃ b d : Fin r, ({a,v,b} : Set (Fin r)) ∈ P ∧
      ({m a,v,d} : Set (Fin r)) ∈ P ∧ d ≠ m b

/-- The successful labels correspond exactly to the vertices outside the square components. -/
theorem point_deleted_successful_starts {r : ℕ} (S : Set (Set (Fin (r + 1))))
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) :
    let P := pointDeletedFamily S q
    IsPartialSteiner P ∧ ∃ m : Fin r → Fin r,
      (∀ a b, Uncovered P a b ↔ m a = b) ∧
      ∀ v : Fin r,
        let G := pivotGraph valid complete q v
        let large := {x | 6 ≤ (G.connectedComponentMk x).supp.ncard}
        (G.connectedComponentMk none).supp =
          {none, some q, some (q.succAbove v), some (q.succAbove (m v))} ∧
        (Option.some ∘ q.succAbove) '' {a | SuccessfulStart P m v a} = large ∧
          (4 ∣ r → 6 ≤ ({a | SuccessfulStart P m v a} : Set (Fin r)).ncard) := by
  classical
  obtain ⟨validP,m,inv,_,leave,switch⟩ := point_deleted_switch S valid complete q
  refine ⟨validP,m,leave,?_⟩
  intro v G large
  let M := pivotMatchings valid complete q v
  let embed : Fin r → Option (Fin (r + 1)) := Option.some ∘ q.succAbove
  have inj : Function.Injective embed := Option.some_injective _ |>.comp Fin.succAbove_right_injective
  obtain ⟨z,_,_,qv,vq⟩ :=
    translate_special_square valid complete (Fin.succAbove_ne q v).symm
  have hqv : M.first (some (q.succAbove v)) = some z := qv
  have hvq : M.second (some q) = some z := vq
  have hq : M.first none = some q := translate_none valid complete q
  have hv : M.second none = embed v := translate_none valid complete (q.succAbove v)
  have hm : M.first (embed v) = embed (m v) :=
    translate_deleted_match valid complete q leave v
  have hz : some z = embed (m v) := hqv.symm.trans hm
  have commute : M.first (M.second none) = M.second (M.first none) := by
    rw [hv,hq,hvq,hm,hz]
  have special : (M.graph.connectedComponentMk none).supp =
      {none, some q, embed v, embed (m v)} := by
    rw [M.component_eq_square commute, hq,hv,hm]
  have excluded (x) (hx : x ∈ ({none, some q, embed v, embed (m v)} : Set _)) :
      x ∉ large := by
    rw [← special] at hx
    have eq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx
    intro hxlarge
    change 6 ≤ (M.graph.connectedComponentMk x).supp.ncard at hxlarge
    rw [eq] at hxlarge
    exact ((M.noncommute_iff_six_le_component none).mpr hxlarge) commute
  have on_labels (a : Fin r) : embed a ∈ large ↔ SuccessfulStart (pointDeletedFamily S q) m v a := by
    constructor
    · intro h
      have ne₁ : v ≠ a := by
        rintro rfl
        exact excluded (embed v) (by simp) h
      have ne₂ : v ≠ m a := by
        intro eq
        have e : a = m v := by rw [eq, inv a]
        exact excluded (embed a) (by rw [e]; simp) h
      obtain ⟨b,d,hb,hd,_,_,_,_,_⟩ := switch a v ne₁ ne₂
      refine ⟨ne₁,ne₂,b,d,hb,hd,?_⟩
      intro eq
      have hcomm := (switch_commutes_iff valid complete q leave ne₁ ne₂ hb hd).mpr eq
      exact ((M.noncommute_iff_six_le_component (embed a)).mpr h) hcomm.symm
    · rintro ⟨ne₁,ne₂,b,d,hb,hd,hn⟩
      apply (M.noncommute_iff_six_le_component (embed a)).mp
      intro h
      exact hn ((switch_commutes_iff valid complete q leave ne₁ ne₂ hb hd).mp h.symm)
  have image_eq : embed '' {a | SuccessfulStart (pointDeletedFamily S q) m v a} = large := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (on_labels a).mpr ha
    · intro h
      cases x with
      | none => exact (excluded none (by simp) h).elim
      | some u =>
        by_cases eq : u = q
        · subst u
          exact (excluded (some q) (by simp) h).elim
        · obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq eq
          have e : embed a = some u := congrArg some ha
          exact ⟨a,(on_labels a).mp (e.symm ▸ h),e⟩
  refine ⟨special,image_eq,?_⟩
  intro four
  have nodvd : ¬4 ∣ Fintype.card (Option (Fin (r + 1))) := by
    simp only [Fintype.card_option, Fintype.card_fin]
    obtain ⟨k,hk⟩ := four
    intro h
    obtain ⟨l,hl⟩ := h
    omega
  obtain ⟨C,hC⟩ := M.exists_large_component_of_not_dvd nodvd
  have sub : C.supp ⊆ large := by
    intro x hx
    change 6 ≤ (M.graph.connectedComponentMk x).supp.ncard
    rwa [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx]
  rw [← Set.ncard_image_of_injective _ inj, image_eq]
  exact hC.trans (Set.ncard_mono sub)

open RankThreeInternalTriplePotentials (Row LiftedLineFamily)
open RankThreeOmissionPotentials (covers)
open RankThreeInternalSizeSpectrum (IsInternalExtension IsSaturatedInternalExtension)

/-- A complete system with a multiple of four retained labels realizes the first deficit. -/
theorem point_deleted_first_deficit_of_four_dvd {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b) (four : 4 ∣ r) :
    let N := 3 ^ d * r ^ 2 + 3 ^ (d + 1) * (r * (r - 2) / 6)
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard = N) ∧
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard + 1 = N) ∧
    (∀ G, IsInternalExtension mixed G → G.ncard ≤ N) := by
  let q : Fin (r + 1) := 0
  have hr : 0 < r := by
    by_contra! h
    have rz : r = 0 := by omega
    exact (NeZero.ne (3 * r)) (by simp [rz])
  let v : Fin r := ⟨0,hr⟩
  obtain ⟨validP,m,leave,counts⟩ := point_deleted_successful_starts S valid complete q
  have card := (counts v).2.2 four
  have nonempty : {a | SuccessfulStart (pointDeletedFamily S q) m v a}.Nonempty := by
    by_contra h
    rw [(Set.not_nonempty_iff_eq_empty).mp h, Set.ncard_empty] at card
    omega
  obtain ⟨a,_,_,b,c,hb,hc,success⟩ := nonempty
  let path : Fin 5 → Fin r := [a,b,v,c,m a].get
  exact PointDeletedSteinerSwitch.matching_switch_first_deficit hd mixed family crosses
    mixedUnique (pointDeletedFamily S q) validP m leave path rfl (by
      convert hb using 1
      ext x
      simp only [path, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto) (by
      convert hc using 1
      ext x
      simp only [path, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto) (by
      change m b ≠ c
      exact Ne.symm success)

end D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches
