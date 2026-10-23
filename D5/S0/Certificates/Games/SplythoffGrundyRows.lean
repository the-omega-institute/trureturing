/- GID: D5/S0/Certificates/Games/SplythoffGrundyRows
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/SplythoffGrundyRows
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Each Splythoff Nim row and column contains every Grundy value exactly once. -/

/- admission_basis: open-problem-resolution (#15902; Proved).
   escape_witness: none.
   Direct frozen dependencies (declaration statement_id, not module pins):
     D5/S0/Certificates/Games/CrimGrundyRefutation.mex
       sha256:0738bcb6bb6cf5e757f0f1af9901368f863881b2fcbf2dce0386cf7450eb031d
     D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec
       sha256:dad28424985fb7ac4bdbd2bce2995c3a0490e168af57bfc8286a5352b0dce7a7
   The bounded follower rectangle equals the literal move relation,
   including its unbounded existential for double moves.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16101.
   Per-declaration classification; dependency names refer to the identities above:
   splythoffMove: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: diagonal_injective, follower_bound, followers, followers_iff, grundy_symm, move_decreases, move_swap, move_value_ne, window_cover.
   followers: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: followers_iff, grundy, grundyPair_eq, grundy_symm, move_value_ne, window_cover.
   follower_bound: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: followers_iff.
   move_decreases: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: grundy, grundy_symm.
   grundy: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: claim, column_injective, diagonal_injective, doubleColumns, doubleColumns_card, grundy, grundyPair_eq, grundy_symm, lowColumns, lowColumns_card, matching, matching_card_bound, matching_coordinate_disjoint, matching_fst_inj, matching_overlap_diag, matching_property, matching_snd_inj, move_value_ne, result, row_exists_bound, row_injective, targetSums, targetSums_card_bound, verticalColumns, verticalColumns_card, window_cover.
   grundyPair_eq: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: grundy_symm, move_value_ne.
   claim: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: result.
   followers_iff: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: grundy_symm, move_value_ne, window_cover.
   move_swap: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: none.
     Consumers: grundy_symm.
   grundy_symm: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: column_injective, matching_coordinate_disjoint, result, targetSums_card_bound.
   move_value_ne: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: diagonal_injective, row_injective.
   row_injective: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: column_injective, doubleColumns_card, lowColumns_card, matching_coordinate_disjoint, matching_fst_inj, result, verticalColumns_card.
   column_injective: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_coordinate_disjoint, matching_snd_inj, result.
   diagonal_injective: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_card_bound.
   matching: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: matching_card_bound, matching_coordinate_disjoint, matching_fst_inj, matching_overlap_diag, matching_property, matching_snd_inj, targetSums_card_bound.
   matching_property: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: matching_card_bound, matching_coordinate_disjoint, matching_fst_inj, matching_overlap_diag, matching_snd_inj.
   matching_fst_inj: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_card_bound, matching_coordinate_disjoint.
   matching_snd_inj: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_card_bound, matching_coordinate_disjoint.
   matching_coordinate_disjoint: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_overlap_diag.
   matching_overlap_diag: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: matching_card_bound.
   matching_card_bound: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: targetSums_card_bound.
   targetSums: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: splitColumns, splitColumns_card, targetSums_card_bound, window_cover.
   targetSums_card_bound: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: splitColumns_card.
   lowColumns: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: lowColumns_card, row_exists_bound, window_cover.
   verticalColumns: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: obstruction_card, row_exists_bound, window_cover.
   doubleColumns: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: obstruction_card, row_exists_bound, window_cover.
   splitColumns: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex.
     Consumers: row_exists_bound, splitColumns_card, window_cover.
   lowColumns_card: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: row_exists_bound.
   verticalColumns_card: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: obstruction_card.
   doubleColumns_card: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: obstruction_card.
   splitColumns_card: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: row_exists_bound.
   obstruction_card: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: row_exists_bound.
   window_cover: proof_shape: bind-only; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: row_exists_bound.
   row_exists_bound: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: result.
   result: proof_shape: content; escape_witness: none.
     Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation.mex, D5/S0/Certificates/Games/CrimGrundyRefutation.mex_spec.
     Consumers: settling result.
-/

import D5.S0.Certificates.Games.CrimGrundyRefutation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
namespace D5.S0.Certificates.Games.SplythoffGrundyRows
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

def splythoffMove (p q : (ℕ × ℕ)) : Prop :=
  (q.1 < p.1 ∧ q.2 = p.2) ∨
  (q.1 = p.1 ∧ q.2 < p.2) ∨
  (∃ k, 1 ≤ k ∧ k ≤ min p.1 p.2 ∧ q = (p.1 - k, p.2 - k)) ∨
  (1 ≤ min p.1 p.2 ∧ q.1 + q.2 = max p.1 p.2 - min p.1 p.2)

noncomputable def followers (p : (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range (max p.1 p.2 + 1)).product (Finset.range (max p.1 p.2 + 1)) |>.filter (splythoffMove p)

private theorem follower_bound (p q : (ℕ × ℕ)) (h : splythoffMove p q) :
    q.1 ≤ max p.1 p.2 ∧ q.2 ≤ max p.1 p.2 := by
  rcases h with h | h | h | h
  · omega
  · omega
  · rcases h with ⟨k, hk, hkm, rfl⟩
    omega
  · omega

private theorem move_decreases (p q : (ℕ × ℕ)) (h : splythoffMove p q) :
    q.1 + q.2 < p.1 + p.2 := by
  rcases h with h | h | h | h
  · omega
  · omega
  · rcases h with ⟨k, hk, hkm, rfl⟩
    omega
  · omega

noncomputable def grundy (x y : ℕ) : ℕ := by
  classical
  exact mex (((followers (x, y)).attach.toList.map
    (fun q => grundy q.val.1 q.val.2)).toFinset)
termination_by x + y
decreasing_by
  classical
  exact move_decreases (x, y) q.val ((Finset.mem_filter.mp q.property).2)

private theorem grundyPair_eq (p : (ℕ × ℕ)) :
    grundy p.1 p.2 = mex ((followers p).image (fun q => grundy q.1 q.2)) := by
  classical
  rw [grundy]
  congr 1
  apply Finset.ext
  intro n
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Finset.mem_coe]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, q.2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, by simp, rfl⟩
def claim : Prop := (∀ x g : ℕ, ∃! y, grundy x y = g) ∧
  (∀ y g : ℕ, ∃! x, grundy x y = g)

private theorem followers_iff (p q : (ℕ × ℕ)) : q ∈ followers p ↔ splythoffMove p q := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb := follower_bound p q h
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, h⟩

private theorem move_swap (p q : (ℕ × ℕ)) :
    splythoffMove (p.2, p.1) (q.2, q.1) ↔ splythoffMove p q := by
  constructor <;> intro h <;> rcases h with h | h | h | h
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  · exact Or.inl ⟨h.2, h.1⟩
  · rcases h with ⟨k, hk, hkm, hq⟩
    exact Or.inr (Or.inr (Or.inl ⟨k, hk, by simpa [min_comm] using hkm,
      Prod.ext (congrArg Prod.snd hq) (congrArg Prod.fst hq)⟩))
  · exact Or.inr (Or.inr (Or.inr (by simpa [min_comm, max_comm, Nat.add_comm] using h)))
  · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  · exact Or.inl ⟨h.2, h.1⟩
  · rcases h with ⟨k, hk, hkm, hq⟩
    exact Or.inr (Or.inr (Or.inl ⟨k, hk, by simpa [min_comm] using hkm,
      Prod.ext (congrArg Prod.snd hq) (congrArg Prod.fst hq)⟩))
  · exact Or.inr (Or.inr (Or.inr (by simpa [min_comm, max_comm, Nat.add_comm] using h)))

private theorem grundy_symm (x y : ℕ) : grundy x y = grundy y x := by
  classical
  have hs : ∀ p : (ℕ × ℕ), grundy p.1 p.2 = grundy p.2 p.1 := by
    intro p
    induction p using (measure (fun p : (ℕ × ℕ) => p.1 + p.2)).wf.induction with
    | h p ih =>
      rw [grundyPair_eq p, grundyPair_eq (p.2,p.1)]
      congr 1
      ext n
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hm := (followers_iff p q).mp hq
        refine ⟨(q.2,q.1), (followers_iff _ _).mpr ((move_swap p q).mpr hm), ?_⟩
        exact (ih q (move_decreases p q hm)).symm
      · rintro ⟨q, hq, rfl⟩
        have hm := (followers_iff (p.2,p.1) q).mp hq
        have hm' : splythoffMove p (q.2,q.1) := (move_swap p (q.2,q.1)).mp hm
        refine ⟨(q.2,q.1), (followers_iff _ _).mpr hm', ?_⟩
        exact ih (q.2,q.1) (move_decreases p (q.2,q.1) hm')
  exact hs (x,y)

private theorem move_value_ne (p q : (ℕ × ℕ)) (hm : splythoffMove p q) : grundy p.1 p.2 ≠ grundy q.1 q.2 := by
  classical
  rw [grundyPair_eq]
  intro he
  have hmiss := (mex_spec ((followers p).image (fun q => grundy q.1 q.2))).1
  apply hmiss
  rw [he]
  exact Finset.mem_image.mpr ⟨q, (followers_iff _ _).mpr hm, rfl⟩

private theorem row_injective (x : ℕ) : Function.Injective (grundy x) := by
  intro y z he
  rcases lt_trichotomy y z with h | h | h
  · exact False.elim ((move_value_ne (x,z) (x,y) (Or.inr (Or.inl ⟨rfl,h⟩))) he.symm)
  · exact h
  · exact False.elim ((move_value_ne (x,y) (x,z) (Or.inr (Or.inl ⟨rfl,h⟩))) he)

private theorem column_injective (y : ℕ) : Function.Injective (fun x => grundy x y) := by
  intro x z he
  apply row_injective y
  simpa only [grundy_symm] using he

private theorem diagonal_injective : Function.Injective (fun x => grundy x x) := by
  intro x y he
  suffices h : ∀ a b : ℕ, a < b → grundy a a ≠ grundy b b by
    rcases lt_trichotomy x y with hlt | heq | hlt
    · exact False.elim (h x y hlt he)
    · exact heq
    · exact False.elim (h y x hlt he.symm)
  intro a b hab he
  have hm : splythoffMove (b,b) (a,a) := by
    right; right; left
    refine ⟨b-a, by omega, by omega, ?_⟩
    congr 1 <;> omega
  exact move_value_ne (b,b) (a,a) hm he.symm

private noncomputable def matching (g M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (M+1)).product (Finset.range (M+1))).filter
    (fun p => p.1 ≤ p.2 ∧ p.1+p.2 ≤ M ∧ grundy p.1 p.2 = g)

private theorem matching_property (g M : ℕ) {p : (ℕ × ℕ)} (h : p ∈ matching g M) :
    p.1 ≤ p.2 ∧ p.1+p.2 ≤ M ∧ grundy p.1 p.2 = g := by
  exact (Finset.mem_filter.mp h).2

private theorem matching_fst_inj (g M : ℕ) :
    Set.InjOn Prod.fst (matching g M : Set (ℕ × ℕ)) := by
  intro p hp q hq he
  have hpv := (matching_property g M hp).2.2
  have hqv := (matching_property g M hq).2.2
  apply Prod.ext he
  apply row_injective p.1
  rw [hpv, he, hqv]

private theorem matching_snd_inj (g M : ℕ) :
    Set.InjOn Prod.snd (matching g M : Set (ℕ × ℕ)) := by
  intro p hp q hq he
  have hpv := (matching_property g M hp).2.2
  have hqv := (matching_property g M hq).2.2
  apply Prod.ext _ he
  apply column_injective p.2
  change grundy p.1 p.2 = grundy q.1 p.2
  rw [hpv, he, hqv]

private theorem matching_coordinate_disjoint (g M : ℕ) {p q : (ℕ × ℕ)}
    (hp : p ∈ matching g M) (hq : q ∈ matching g M)
    (hc : p.1=q.1 ∨ p.1=q.2 ∨ p.2=q.1 ∨ p.2=q.2) : p=q := by
  obtain ⟨hpo,hps,hpg⟩ := matching_property g M hp
  obtain ⟨hqo,hqs,hqg⟩ := matching_property g M hq
  rcases hc with hc | hc | hc | hc
  · exact matching_fst_inj g M hp hq hc
  · have he : p.2=q.1 := by
      apply row_injective p.1
      calc
        grundy p.1 p.2 = g := hpg
        _ = grundy p.1 q.1 := by rw [hc,grundy_symm,hqg]
    apply Prod.ext <;> omega
  · have he : p.1=q.2 := by
      apply column_injective p.2
      change grundy p.1 p.2=grundy q.2 p.2
      calc
        grundy p.1 p.2 = g := hpg
        _ = grundy q.2 p.2 := by rw [hc,grundy_symm,hqg]
    apply Prod.ext <;> omega
  · exact matching_snd_inj g M hp hq hc

private theorem matching_overlap_diag (g M : ℕ) {a : ℕ}
    (h : a ∈ (matching g M).image Prod.fst ∩ (matching g M).image Prod.snd) :
    grundy a a = g := by
  classical
  obtain ⟨hf,hs⟩ := Finset.mem_inter.mp h
  obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp hf
  obtain ⟨q,hq,hqa⟩ := Finset.mem_image.mp hs
  obtain ⟨hpord,hpsum,hpv⟩ := matching_property g M hp
  obtain ⟨hqord,hqsum,hqv⟩ := matching_property g M hq
  have heq : p=q := matching_coordinate_disjoint g M hp hq
    (Or.inr (Or.inl (hpa.trans hqa.symm)))
  have hdiag : p.2=a := (congrArg Prod.snd heq).trans hqa
  simpa only [hpa,hdiag] using hpv

private theorem matching_card_bound (g M : ℕ) : 2 * (matching g M).card ≤ M+2 := by
  classical
  let F := (matching g M).image Prod.fst
  let S := (matching g M).image Prod.snd
  have hf : F.card = (matching g M).card := Finset.card_image_of_injOn (matching_fst_inj g M)
  have hs : S.card = (matching g M).card := Finset.card_image_of_injOn (matching_snd_inj g M)
  have hi : (F ∩ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply diagonal_injective
    change grundy a a = grundy b b
    rw [matching_overlap_diag g M ha, matching_overlap_diag g M hb]
  have hu : F ∪ S ⊆ Finset.range (M+1) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      have hp' := matching_property g M hp
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      have hp' := matching_property g M hp
      exact Finset.mem_range.mpr (by omega)
  have huc := Finset.card_le_card hu
  have hc := Finset.card_union_add_card_inter F S
  rw [Finset.card_range] at huc
  omega

private noncomputable def targetSums (g M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (M+1)).filter (fun n => ∃ u v, u+v=n ∧ grundy u v=g)

private theorem targetSums_card_bound (g M : ℕ) : (targetSums g M).card ≤ (M+2)/2 := by
  classical
  have hsub : targetSums g M ⊆ (matching g M).image (fun p => p.1+p.2) := by
    intro n hn
    obtain ⟨hnb, u,v, huv,hg⟩ := Finset.mem_filter.mp hn
    have hnM := Finset.mem_range.mp hnb
    by_cases hu : u ≤ v
    · refine Finset.mem_image.mpr ⟨(u,v), ?_, huv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩, hu,by omega,hg⟩
    · refine Finset.mem_image.mpr ⟨(v,u), ?_, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
        by omega,by omega,by rw [grundy_symm];exact hg⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := matching_card_bound g M
  omega

private noncomputable def lowColumns (x g M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc x (x+M)).filter (fun y => grundy x y < g)

private noncomputable def verticalColumns (x g M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range x).biUnion (fun r => (Finset.Ioc x (x+M)).filter (fun y => grundy r y=g))

private noncomputable def doubleColumns (x g M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range x).biUnion (fun k =>
    (Finset.Ioc x (x+M)).filter (fun y => grundy (x-(k+1)) (y-(k+1))=g))

private noncomputable def splitColumns (x g M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc x (x+M)).filter (fun y => y-x ∈ targetSums g M)

private theorem lowColumns_card (x g M : ℕ) : (lowColumns x g M).card ≤ g := by
  classical
  have hi : Set.InjOn (grundy x) (lowColumns x g M : Set ℕ) :=
    (row_injective x).injOn
  have hs : (lowColumns x g M).image (grundy x) ⊆ Finset.range g := by
    intro n hn
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr ((Finset.mem_filter.mp hy).2)
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn hi, Finset.card_range] at hc
  exact hc

private theorem verticalColumns_card (x g M : ℕ) : (verticalColumns x g M).card ≤ x := by
  classical
  have he : ∀ r ∈ Finset.range x,
      ((Finset.Ioc x (x+M)).filter (fun y => grundy r y=g)).card ≤ 1 := by
    intro r hr
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply row_injective r
    rw [(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2]
  have hb := Finset.card_biUnion_le (s:=Finset.range x)
    (t:=fun r => (Finset.Ioc x (x+M)).filter (fun y => grundy r y=g))
  have hc := Finset.sum_le_sum he
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_one] at hc
  exact hb.trans hc

private theorem doubleColumns_card (x g M : ℕ) : (doubleColumns x g M).card ≤ x := by
  classical
  have he : ∀ k ∈ Finset.range x,
      ((Finset.Ioc x (x+M)).filter (fun y => grundy (x-(k+1)) (y-(k+1))=g)).card ≤ 1 := by
    intro k hk
    have hkx := Finset.mem_range.mp hk
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,hga⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hgb⟩ := Finset.mem_filter.mp hb
    have hab : a-(k+1)=b-(k+1) := row_injective (x-(k+1)) (hga.trans hgb.symm)
    have hwa := Finset.mem_Ioc.mp ha
    have hwb := Finset.mem_Ioc.mp hb
    omega
  have hb := Finset.card_biUnion_le (s:=Finset.range x)
    (t:=fun k => (Finset.Ioc x (x+M)).filter (fun y => grundy (x-(k+1)) (y-(k+1))=g))
  have hc := Finset.sum_le_sum he
  simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_one] at hc
  exact hb.trans hc

private theorem splitColumns_card (x g M : ℕ) : (splitColumns x g M).card ≤ (M+2)/2 := by
  classical
  have hi : Set.InjOn (fun y => y-x) (splitColumns x g M : Set ℕ) := by
    intro a ha b hb he
    change a-x=b-x at he
    have hwa := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
    have hwb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
    omega
  have hs : (splitColumns x g M).image (fun y => y-x) ⊆ targetSums g M := by
    intro n hn
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hy).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn hi] at hc
  exact hc.trans (targetSums_card_bound g M)

private theorem obstruction_card (x g M : ℕ) :
    (verticalColumns x g M ∪ doubleColumns x g M).card ≤ 2*x := by
  have hv := verticalColumns_card x g M
  have hd := doubleColumns_card x g M
  have hu := Finset.card_union_le (verticalColumns x g M) (doubleColumns x g M)
  omega
private theorem window_cover (x g M : ℕ)
    (habs : ∀ y ≤ x+M, grundy x y ≠ g) :
    Finset.Ioc x (x+M) ⊆ lowColumns x g M ∪
      (verticalColumns x g M ∪ doubleColumns x g M) ∪ splitColumns x g M := by
  classical
  intro y hy
  obtain ⟨hyx,hyM⟩ := Finset.mem_Ioc.mp hy
  by_cases hl : grundy x y < g
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_filter.mpr ⟨hy,hl⟩))))
  have hgt : g < grundy x y := by have hn:=habs y hyM; omega
  have hgF := (mex_spec ((followers (x,y)).image (fun q => grundy q.1 q.2))).2 g
    (by rw [← grundyPair_eq (x,y)];exact hgt)
  obtain ⟨q,hq,hqg⟩ := Finset.mem_image.mp hgF
  have hm := (followers_iff (x,y) q).mp hq
  rcases hm with hv | hh | hd | hs
  · have hg : grundy q.1 y=g := by simpa only [hv.2] using hqg
    have hmem : y ∈ verticalColumns x g M := Finset.mem_biUnion.mpr
      ⟨q.1,Finset.mem_range.mpr hv.1,Finset.mem_filter.mpr ⟨hy,hg⟩⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inl hmem)))))
  · have hg : grundy x q.2=g := by simpa only [hh.1] using hqg
    exact False.elim (habs q.2 (by omega) hg)
  · obtain ⟨k,hk,hkm,hqeq⟩ := hd
    have hkx : k≤x := by omega
    have hki : k-1+1=k := by omega
    have hg : grundy (x-(k-1+1)) (y-(k-1+1))=g := by
      simpa only [hki,hqeq] using hqg
    have hmem : y ∈ doubleColumns x g M := Finset.mem_biUnion.mpr
      ⟨k-1,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hy,hg⟩⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inr hmem)))))
  · have hsum : q.1+q.2=y-x := by
      simpa only [min_eq_left (le_of_lt hyx),max_eq_right (le_of_lt hyx)] using hs.2
    have hsumMem : y-x ∈ targetSums g M := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),q.1,q.2,hsum,hqg⟩
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hy,hsumMem⟩))
theorem row_exists_bound (x g : ℕ) : ∃ y, grundy x y=g ∧ y ≤ 5*x+2*g+3 := by
  classical
  by_contra hn
  have habs : ∀ y ≤ 5*x+2*g+3, grundy x y≠g := by
    intro y hy hg
    exact hn ⟨y,hg,hy⟩
  let M := 2*g+4*x+3
  have hsub := window_cover x g M (by intro y hy;exact habs y (by dsimp [M] at *;omega))
  have hw : (Finset.Ioc x (x+M)).card=M := by rw [Nat.card_Ioc];omega
  have hc := Finset.card_le_card hsub
  have h1 := Finset.card_union_le
    (lowColumns x g M ∪ (verticalColumns x g M ∪ doubleColumns x g M)) (splitColumns x g M)
  have h2 := Finset.card_union_le (lowColumns x g M)
    (verticalColumns x g M ∪ doubleColumns x g M)
  have hl := lowColumns_card x g M
  have ho := obstruction_card x g M
  have hs := splitColumns_card x g M
  rw [hw] at hc
  dsimp [M] at *
  omega

theorem result : claim := by
  constructor
  · intro x g
    obtain ⟨y,hg,hb⟩ := row_exists_bound x g
    exact ⟨y,hg,fun z hz => row_injective x (hz.trans hg.symm)⟩
  · intro y g
    obtain ⟨x,hg,hb⟩ := row_exists_bound y g
    have hxy : grundy x y=g := by rw [grundy_symm];exact hg
    exact ⟨x,hxy,fun z hz => column_injective y (hz.trans hxy.symm)⟩

end D5.S0.Certificates.Games.SplythoffGrundyRows
