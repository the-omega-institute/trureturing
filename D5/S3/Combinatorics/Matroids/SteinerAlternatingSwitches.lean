/- GID: D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerAlternatingSwitches
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The large components of two translations give exactly the successful Steiner switches. -/

import D5.S3.Combinatorics.Matroids.AlternatingMatchingComponents
import D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations

/-! # Successful switches in a point-deleted Steiner system -/

namespace D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches

open Set SimpleGraph
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open PointDeletedSteinerSwitch (pointDeletedFamily point_deleted_switch)
open AlternatingMatchingComponents (Matchings)
open SteinerMatchingTranslations

/-- The two matching translations for deletion at q and a fixed pivot. -/
noncomputable def pivotMatchings {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) (v : Fin r) : Matchings (Option (Fin (r + 1))) where
  first := translate valid complete q
  second := translate valid complete (q.succAbove v)
  first_involutive := translate_involutive valid complete q
  second_involutive := translate_involutive valid complete (q.succAbove v)
  first_ne_self := translate_ne_self valid complete q
  second_ne_self := translate_ne_self valid complete (q.succAbove v)
  partners_ne := translate_ne_translate valid complete (Fin.succAbove_ne q v).symm

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
        let M := pivotMatchings valid complete q v
        let large := {x | 6 ≤ (M.graph.connectedComponentMk x).supp.ncard}
        (Option.some ∘ q.succAbove) '' {a | SuccessfulStart P m v a} = large ∧
          (4 ∣ r → 6 ≤ ({a | SuccessfulStart P m v a} : Set (Fin r)).ncard) := by
  classical
  obtain ⟨validP,m,inv,_,leave,switch⟩ := point_deleted_switch S valid complete q
  refine ⟨validP,m,leave,?_⟩
  intro v M large
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
  refine ⟨image_eq,?_⟩
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
  have card := (counts v).2 four
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

