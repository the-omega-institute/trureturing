/- GID: D5/S3/Geometry/FiveAnchorFaithfulPlacement
   generality: G
   mirror-B: D5/B/S3/Geometry/FiveAnchorFaithfulPlacement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Faithful finite bipartite placement from small cospherical anchor families. -/
module

public import D5.S3.Geometry.CosphericalUnitLocus
import all D5.S3.Geometry.CosphericalUnitLocus
public import D5.S3.Geometry.SphereGeneralPosition
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Finite faithful placements with strict norm bounds and unchanged original labels. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.FiveAnchorFaithfulPlacement

local notation "E₅" => EuclideanSpace ℝ (Fin 5)

private def omega : Set E₅ := {p | (1 / 4 : ℝ) < ‖p‖ ∧ ‖p‖ < 1}

private theorem omega_open : IsOpen omega :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

private theorem choose_empty {ι κ : Type*} [Finite ι] [Finite κ]
    (z : ι → E₅) (q : κ → E₅) :
    ∃ p ∈ omega, (∀ i, dist p (z i) ≠ 1) ∧ ∀ j, p ≠ q j := by
  let K : Submodule ℝ E₅ := ⊤
  have hd : 2 ≤ Module.finrank ℝ K := by simp [K]
  have : Nontrivial K := Module.finrank_pos_iff (R := ℝ) |>.mp (by omega)
  obtain ⟨w, hw⟩ := exists_norm_eq K (by norm_num : (0 : ℝ) ≤ 3 / 4)
  obtain ⟨w, hwU, _, hz, hq⟩ :=
    SphereSectionAvoidance.exists_on_affine_sphere_avoiding K hd 0
      (by norm_num : (0 : ℝ) < 3 / 4) omega_open
      ⟨w, by simp only [zero_add]; change (1 / 4 : ℝ) < ‖(w : E₅)‖ ∧ ‖(w : E₅)‖ < 1; rw [show ‖(w : E₅)‖ = 3 / 4 from hw]; norm_num, hw⟩
      z q (by
        intro i hi
        have hz0 : z i = 0 := by
          simpa [K] using Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hi
        simp [hz0]; norm_num)
  exact ⟨(w : E₅), by simpa using hwU, by simpa using hz, by simpa using hq⟩

private theorem choose_row {α β : Type*} [Fintype α] [Finite β]
    (x : α → E₅) (hx : ∀ a, ‖x a‖ = 1 / 4)
    (q : E₅) (hq : q ∈ omega) (hqx : ∀ a, dist q (x a) = 1)
    (N : Finset α)
    (hd : ∀ a₀ : N, 2 ≤ Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀)ᗮ)
    (hsep : ∀ a₀ : N, ∀ a ∉ N,
      x a - CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀ ∉
        CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀)
    (y : β → E₅) (hy : ∀ b, y b ∈ omega) :
    ∃ p ∈ omega, (∀ a, dist p (x a) = 1 ↔ a ∈ N) ∧
      (∀ b, dist p (y b) ≠ 1) ∧ ∀ b, p ≠ y b := by
  classical
  by_cases hN : N.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hN
    let z : {a // a ∉ N} ⊕ β → E₅ := Sum.elim (fun a => x a.val) y
    obtain ⟨p, hp, hpx, hpz, hpy⟩ := CosphericalUnitLocus.exists_common_unit_avoiding
      (fun a : N => x a.val) ⟨a₀, ha₀⟩ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1) (fun a => hx a.val) (hd ⟨a₀, ha₀⟩)
      omega_open ⟨q, hq, fun a => hqx a.val⟩ z y (by
        rintro (a | b)
        · exact Or.inr (hsep ⟨a₀, ha₀⟩ a.val a.property)
        · exact Or.inl (ne_of_gt (hy b).1))
    refine ⟨p, hp, fun a => ?_, fun b => hpz (.inr b), hpy⟩
    by_cases ha : a ∈ N
    · exact ⟨fun _ => ha, fun _ => hpx ⟨a, ha⟩⟩
    · exact ⟨fun h => (hpz (.inl ⟨a, ha⟩) h).elim, fun h => (ha h).elim⟩
  · have hN0 : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    obtain ⟨p, hp, hz, hpy⟩ := choose_empty (Sum.elim x y) y
    exact ⟨p, hp, fun a => by simpa [hN0] using hz (.inl a), fun b => hz (.inr b), hpy⟩

private theorem place_rows {α β : Type*} [Fintype α] [Fintype β]
    (x : α → E₅) (hx : ∀ a, ‖x a‖ = 1 / 4)
    (q : E₅) (hq : q ∈ omega) (hqx : ∀ a, dist q (x a) = 1)
    (N : β → Finset α)
    (s₀ : Finset β) (y₀ : s₀ → E₅) (hinj₀ : Function.Injective y₀)
    (hunit₀ : ∀ b c, dist (y₀ b) (y₀ c) ≠ 1)
    (hnorm₀ : ∀ b, y₀ b ∈ omega)
    (hrow₀ : ∀ b : s₀, ∀ a, dist (y₀ b) (x a) = 1 ↔ a ∈ N b.val)
    (hd : ∀ b ∉ s₀, ∀ a₀ : N b, 2 ≤ Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀)ᗮ)
    (hsep : ∀ b ∉ s₀, ∀ a₀ : N b, ∀ a ∉ N b,
      x a - CosphericalUnitLocus.anchorCenter (fun a : N b => x a.val) a₀ ∉
        CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀) :
    ∃ y : β → E₅, Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ (∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b) ∧
      ∀ b : s₀, y b.val = y₀ b := by
  classical
  generalize hn : (Finset.univ \ s₀).card = n
  induction n generalizing s₀ with
  | zero =>
    have hs (b : β) : b ∈ s₀ := by
      have he : Finset.univ \ s₀ = ∅ := Finset.card_eq_zero.mp hn
      have : b ∉ Finset.univ \ s₀ := by rw [he]; simp
      simpa using this
    let y : β → E₅ := fun b => y₀ ⟨b, hs b⟩
    exact ⟨y, fun b c h => congrArg Subtype.val (hinj₀ h),
      fun b c => hunit₀ _ _, fun b => hnorm₀ _, fun b a => hrow₀ _ _, fun b => rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ s₀).card by omega)
    have hbs : b ∉ s₀ := (Finset.mem_sdiff.mp hb).2
    obtain ⟨p, hp, hpx, hpy, hpne⟩ :=
      choose_row x hx q hq hqx (N b) (hd b hbs) (hsep b hbs) y₀ hnorm₀
    let y₁ : ↥(insert b s₀ : Finset β) → E₅ := fun c =>
      if hc : c.val = b then p
      else y₀ ⟨c.val, (Finset.mem_insert.mp c.property).resolve_left hc⟩
    have hold (c : s₀) : y₁ ⟨c.val, Finset.mem_insert_of_mem c.property⟩ = y₀ c := by
      have hc : c.val ≠ b := by intro he; exact hbs (he ▸ c.property)
      simp [y₁, hc]
    have hnew : y₁ ⟨b, Finset.mem_insert_self b s₀⟩ = p := by simp [y₁]
    have hsplit (c : ↥(insert b s₀ : Finset β)) :
        c = ⟨b, Finset.mem_insert_self b s₀⟩ ∨
          ∃ d : s₀, c = ⟨d.val, Finset.mem_insert_of_mem d.property⟩ := by
      rcases Finset.mem_insert.mp c.property with hc | hc
      · exact Or.inl (Subtype.ext hc)
      · exact Or.inr ⟨⟨c.val, hc⟩, rfl⟩
    have hinj₁ : Function.Injective y₁ := by
      intro c d he
      rcases hsplit c with rfl | ⟨c, rfl⟩ <;> rcases hsplit d with rfl | ⟨d, rfl⟩
      · rfl
      · rw [hnew, hold] at he; exact (hpne d he).elim
      · rw [hold, hnew] at he; exact (hpne c he.symm).elim
      · rw [hold, hold] at he
        exact Subtype.ext (congrArg (fun w : s₀ => w.val) (hinj₀ he))
    have hunit₁ : ∀ c d, dist (y₁ c) (y₁ d) ≠ 1 := by
      intro c d
      rcases hsplit c with rfl | ⟨c, rfl⟩ <;> rcases hsplit d with rfl | ⟨d, rfl⟩
      · simp
      · rw [hnew, hold]; exact hpy d
      · rw [hold, hnew, dist_comm]; exact hpy c
      · rw [hold, hold]; exact hunit₀ c d
    have hnorm₁ : ∀ c, y₁ c ∈ omega := by
      intro c
      rcases hsplit c with rfl | ⟨c, rfl⟩
      · rw [hnew]; exact hp
      · rw [hold]; exact hnorm₀ c
    have hrow₁ : ∀ c : ↥(insert b s₀ : Finset β), ∀ a,
        dist (y₁ c) (x a) = 1 ↔ a ∈ N c.val := by
      intro c a
      rcases hsplit c with rfl | ⟨c, rfl⟩
      · rw [hnew]; exact hpx a
      · rw [hold]; exact hrow₀ c a
    have hn₁ : (Finset.univ \ insert b s₀).card = n := by
      have he : Finset.univ \ insert b s₀ = (Finset.univ \ s₀).erase b := by
        ext v; simp
      rw [he, Finset.card_erase_of_mem hb, hn]; omega
    obtain ⟨y, hyi, hyu, hyn, hyr, hyo⟩ := ih (insert b s₀) y₁ hinj₁ hunit₁ hnorm₁ hrow₁
      (by intro c hc; exact hd c (fun h => hc (Finset.mem_insert_of_mem h)))
      (by intro c hc; exact hsep c (fun h => hc (Finset.mem_insert_of_mem h))) hn₁
    exact ⟨y, hyi, hyu, hyn, hyr, fun c =>
      (hyo ⟨c.val, Finset.mem_insert_of_mem c.property⟩).trans (hold c)⟩

private theorem direction_eq {ι : Type*} (x : ι → E₅) (i₀ : ι) :
    CosphericalUnitLocus.anchorDirection x i₀ = vectorSpan ℝ (Set.range x) := by
  exact (vectorSpan_range_eq_span_range_vsub_right ℝ x i₀).symm

private theorem row_dimension {α : Type*} [Fintype α]
    (x : α → E₅) (N : Finset α) (hN : N.card ≤ 4) (a₀ : N) :
    2 ≤ Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀)ᗮ := by
  letI : Nonempty N := ⟨a₀⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ (fun a : N => x a.val)
  have hcard : Fintype.card N = N.card := Fintype.card_coe _
  have hsum := (CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀).finrank_add_finrank_orthogonal
  rw [direction_eq] at hsum ⊢
  have he : Module.finrank ℝ E₅ = 5 := by simp
  omega

private theorem center_mem_hull {ι : Type*} (x : ι → E₅) (i₀ : ι) :
    CosphericalUnitLocus.anchorCenter x i₀ ∈ affineSpan ℝ (Set.range x) := by
  have hmem : (CosphericalUnitLocus.anchorDirection x i₀).starProjection (x i₀) ∈
      (affineSpan ℝ (Set.range x)).direction := by
    rw [direction_affineSpan, ← direction_eq x i₀, Submodule.starProjection_apply]
    exact Subtype.coe_prop _
  have hbase := mem_affineSpan ℝ (Set.mem_range_self i₀ : x i₀ ∈ Set.range x)
  have hh := (affineSpan ℝ (Set.range x)).vadd_mem_of_mem_direction ((affineSpan ℝ (Set.range x)).direction.neg_mem hmem) hbase
  convert hh using 1 <;> dsimp [CosphericalUnitLocus.anchorCenter] <;> abel

private theorem separated_direction {α : Type*} (x : α → E₅) (N : Finset α)
    (a₀ : N) (a : α) (hsep : x a ∉ affineSpan ℝ (x '' (N : Set α))) :
    x a - CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀ ∉
      CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀ := by
  intro hh
  have hrange : Set.range (fun a : N => x a.val) = x '' (N : Set α) := by
    ext p; simp
  have hdir : x a - CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀ ∈
      (affineSpan ℝ (Set.range (fun a : N => x a.val))).direction := by
    rwa [direction_affineSpan, ← direction_eq]
  have hmem := (affineSpan ℝ (Set.range (fun a : N => x a.val))).vadd_mem_of_mem_direction
    hdir (center_mem_hull _ a₀)
  have he : x a ∈ affineSpan ℝ (Set.range (fun a : N => x a.val)) := by simpa using hmem
  exact hsep (hrange ▸ he)

private theorem independent_separation {α : Type*} (x : α → E₅)
    (hi : AffineIndependent ℝ x) (N : Finset α) (a₀ : N) (a : α) (ha : a ∉ N) :
    x a - CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀ ∉
      CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀ :=
  separated_direction x N a₀ a (by simpa only [hi.mem_affineSpan_iff, Finset.mem_coe] using ha)

private def embed (d : ℕ) (hd : d ≤ 5) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] E₅ :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hd)

private def north : E₅ := EuclideanSpace.single 4 (Real.sqrt 15 / 4)

private theorem north_norm : ‖north‖ = Real.sqrt 15 / 4 := by
  simp [north, PiLp.norm_single, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 15 / 4)]

private theorem north_omega : north ∈ omega := by
  have hs : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  change (1 / 4 : ℝ) < ‖north‖ ∧ ‖north‖ < 1
  rw [north_norm]
  constructor <;> nlinarith [Real.sqrt_nonneg 15]

private theorem embed_last {d : ℕ} (hd : d ≤ 4) (p : EuclideanSpace ℝ (Fin d)) :
    embed d (by omega) p 4 = 0 := by
  apply LinearIsometry.piLpExtendByZero_apply_eq_zero
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [Fin.castLEEmb_apply, Fin.coe_castLE] at this
  omega

private theorem north_unit {d : ℕ} (hd : d ≤ 4)
    (p : EuclideanSpace ℝ (Fin d)) (hp : ‖p‖ = 1 / 4) :
    dist north (embed d (by omega) p) = 1 := by
  have hi : ⟪north, embed d (by omega) p⟫_ℝ = 0 := by
    simp [north, EuclideanSpace.inner_single_left, embed_last hd]
  have hh : dist north (embed d (by omega) p) ^ 2 = 1 := by
    rw [dist_eq_norm, norm_sub_sq_real, north_norm, (embed d (by omega)).norm_map, hp, hi]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
    nlinarith
  nlinarith [dist_nonneg (x := north) (y := embed d (by omega) p)]

private theorem independent_anchors {α : Type*} [Fintype α] (hc : Fintype.card α ≤ 5) :
    ∃ x : α → E₅, AffineIndependent ℝ x ∧
      (∀ a, ‖x a‖ = 1 / 4) ∧ (∀ a, dist north (x a) = 1) ∧
      ∀ a, x a ∈ (embed 4 (by omega)).toLinearMap.range := by
  classical
  obtain ⟨s, hsc, hsn, hsi⟩ := SphereGeneralPosition.exists_sphere_general_position
    (E := EuclideanSpace ℝ (Fin 4)) (by simp) (by norm_num : (0 : ℝ) < 1 / 4)
    (Fintype.card α)
  let e : α ≃ s := Fintype.equivOfCardEq (by simpa using hsc.symm)
  let x₀ : α → EuclideanSpace ℝ (Fin 4) := fun a => (e a).val
  have hi₀ : AffineIndependent ℝ x₀ :=
    (hsi s Finset.Subset.rfl (by simpa [hsc] using hc)).comp_embedding e.toEmbedding
  let f := embed 4 (by omega)
  refine ⟨fun a => f (x₀ a), hi₀.map' f.toLinearMap.toAffineMap f.injective, ?_, ?_, ?_⟩
  · intro a
    rw [f.norm_map]
    exact hsn _ (e a).property
  · intro a
    exact north_unit (by norm_num : 4 ≤ 4) _ (hsn _ (e a).property)
  · intro a
    exact ⟨x₀ a, rfl⟩

private theorem general_anchors {α : Type*} [Fintype α]
    (d : ℕ) (hd : 2 ≤ d) (hd4 : d ≤ 4) :
    ∃ x : α → E₅, Function.Injective x ∧
      (∀ a, ‖x a‖ = 1 / 4) ∧ (∀ a, dist north (x a) = 1) ∧
      (∀ a, x a ∈ (embed d (by omega)).toLinearMap.range) ∧
      ∀ T : Finset α, T.card ≤ d + 1 → AffineIndepOn ℝ x (T : Set α) := by
  classical
  obtain ⟨s, hsc, hsn, hsi⟩ := SphereGeneralPosition.exists_sphere_general_position
    (E := EuclideanSpace ℝ (Fin d)) (by simpa using hd)
    (by norm_num : (0 : ℝ) < 1 / 4) (Fintype.card α)
  let e : α ≃ s := Fintype.equivOfCardEq (by simpa using hsc.symm)
  let x₀ : α → EuclideanSpace ℝ (Fin d) := fun a => (e a).val
  have hinj₀ : Function.Injective x₀ := Subtype.val_injective.comp e.injective
  let f := embed d (by omega)
  refine ⟨fun a => f (x₀ a), f.injective.comp hinj₀, ?_, ?_, ?_, ?_⟩
  · intro a; rw [f.norm_map]; exact hsn _ (e a).property
  · intro a; exact north_unit hd4 _ (hsn _ (e a).property)
  · intro a; exact ⟨x₀ a, rfl⟩
  · intro T hT
    have ht : T.image x₀ ⊆ s := by
      intro p hp; obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e a).property
    have hc : (T.image x₀).card ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 := by
      simpa [Finset.card_image_of_injective _ hinj₀] using hT
    have hi : AffineIndepOn ℝ id (x₀ '' (T : Set α)) := by
      simpa only [Finset.coe_image] using hsi (T.image x₀) ht hc
    have hi₀ : AffineIndepOn ℝ x₀ (T : Set α) := by
      simpa only [Function.id_comp] using hi.comp_of_image hinj₀.injOn
    exact hi₀.map' f.toLinearMap.toAffineMap f.injective

private theorem general_separation {α : Type*} (x : α → E₅)
    {d : ℕ} (hgp : ∀ T : Finset α, T.card ≤ d + 1 → AffineIndepOn ℝ x (T : Set α))
    (N : Finset α) (hc : N.card ≤ d) (a₀ : N) (a : α) (ha : a ∉ N) :
    x a - CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀ ∉
      CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀ := by
  classical
  apply separated_direction x N a₀ a
  have hi := hgp (insert a N) (by simp [ha]; omega)
  have hi' : AffineIndepOn ℝ x (insert a (N : Set α)) := by simpa using hi
  exact ((affineIndepOn_insert ℝ (by simpa using ha)).mp hi').2

private theorem rank_of_four {α : Type*} [Fintype α] (x : α → E₅)
    (K : Submodule ℝ E₅) (hK : Module.finrank ℝ K ≤ 3) (hx : ∀ a, x a ∈ K)
    (T : Finset α) (hT : T.card = 4) (hi : AffineIndepOn ℝ x (T : Set α))
    (a₀ : α) : Module.finrank ℝ (CosphericalUnitLocus.anchorDirection x a₀) = 3 := by
  classical
  haveI : Nonempty T := Finset.Nonempty.to_subtype (Finset.card_pos.mp (by omega))
  have hr : Module.finrank ℝ (vectorSpan ℝ (Set.range (fun a : T => x a.val))) + 1 = 4 := by
    have hh := hi.affineIndependent.finrank_vectorSpan_add_one
    convert hh using 1 <;> simp [hT]
  have hm := Submodule.finrank_mono (vectorSpan_mono ℝ
    (show Set.range (fun a : T => x a.val) ⊆ Set.range x from by
      rintro _ ⟨a, rfl⟩; exact Set.mem_range_self a.val))
  have hW : CosphericalUnitLocus.anchorDirection x a₀ ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩; exact K.sub_mem (hx a) (hx a₀)
  have hu := Submodule.finrank_mono hW
  have he := congrArg (fun S : Submodule ℝ E₅ => Module.finrank ℝ S) (direction_eq x a₀)
  omega

private theorem row_rank_le_two {α : Type*} (x : α → E₅)
    (N : Finset α) (hc : N.card ≤ 3) (a₀ : N) :
    Module.finrank ℝ (CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀) ≤ 2 := by
  haveI : Nonempty N := ⟨a₀⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ (fun a : N => x a.val)
  have he := congrArg (fun S : Submodule ℝ E₅ => Module.finrank ℝ S)
    (direction_eq (fun a : N => x a.val) a₀)
  have hn : Fintype.card N = N.card := Fintype.card_coe _
  omega

private theorem place_three_dimensional_rows {α β : Type*} [Fintype α] [Fintype β]
    (hc : Fintype.card α = 5)
    (N : β → Finset α) (hN : ∀ b, N b = Finset.univ ∨ (N b).card ≤ 3) :
    ∃ x : α → E₅, ∃ y : β → E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  obtain ⟨x, hxi, hxn, hxq, hxr, hxgp⟩ := general_anchors (α := α) 3 (by omega) (by omega)
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset α).card by simpa [hc])
  have hK : Module.finrank ℝ (embed 3 (by omega)).toLinearMap.range ≤ 3 := by
    have h := LinearMap.finrank_range_of_inj (embed 3 (by omega)).injective
    simpa using h.le
  have hfull (a₀ : α) := rank_of_four x _ hK hxr T hT (hxgp T (by omega)) a₀
  have hdim (b : β) (a₀ : N b) : 2 ≤ Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀)ᗮ := by
    rcases hN b with hb | hb
    · have hi := hfull a₀.val
      have hf : CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀ =
          CosphericalUnitLocus.anchorDirection x a₀.val := by
        apply congrArg (Submodule.span ℝ)
        ext p; constructor
        · rintro ⟨a, rfl⟩; exact Set.mem_range_self a.val
        · rintro ⟨a, rfl⟩; exact ⟨⟨a, by simp [hb]⟩, rfl⟩
      have hs := (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀).finrank_add_finrank_orthogonal
      have he := congrArg (fun S : Submodule ℝ E₅ => Module.finrank ℝ S) hf
      have h5 : Module.finrank ℝ E₅ = 5 := by simp
      omega
    · have hr := row_rank_le_two x (N b) hb a₀
      have hs := (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀).finrank_add_finrank_orthogonal
      have h5 : Module.finrank ℝ E₅ = 5 := by simp
      omega
  obtain ⟨y, hyi, hyu, hyn, hyr, _⟩ := place_rows x hxn north north_omega hxq N
    (∅ : Finset β) (fun b : (∅ : Finset β) => False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b _ a₀; exact hdim b a₀)
    (by
      intro b _ a₀ a ha
      rcases hN b with hb | hb
      · simp [hb] at ha
      · exact general_separation x hxgp (N b) hb a₀ a ha)
  exact ⟨x, y, hxi, hxn, hyi, hyu, hyn, hyr⟩

private def pole (i : Fin 2) : E₅ := if i = 0 then north else -north

private theorem pole_norm (i : Fin 2) : ‖pole i‖ = ‖north‖ := by
  simp only [pole]; split <;> simp

private theorem pole_injective : Function.Injective pole := by
  have hn : north ≠ -north := by
    intro he
    have hh := congrArg (fun p : E₅ => p 4) he
    simp [north, PiLp.single_apply] at hh
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
    nlinarith [Real.sqrt_nonneg 15]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pole]

private theorem pole_nonunit (i j : Fin 2) : dist (pole i) (pole j) ≠ 1 := by
  have hn : dist north (-north) ≠ 1 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ north, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), north_norm]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
    intro he; nlinarith
  fin_cases i <;> fin_cases j <;> simp_all [pole, dist_comm]

private theorem pole_unit {α : Type*} (x : α → E₅)
    (hx : ∀ a, ‖x a‖ = 1 / 4) (hxlast : ∀ a, x a 4 = 0) (i : Fin 2) (a : α) :
    dist (pole i) (x a) = 1 := by
  have hi : ⟪pole i, x a⟫_ℝ = 0 := by
    simp only [pole]; split <;> simp [north, EuclideanSpace.inner_single_left, hxlast]
  have hh : dist (pole i) (x a) ^ 2 = 1 := by
    rw [dist_eq_norm, norm_sub_sq_real, pole_norm, north_norm, hx a, hi]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
    nlinarith
  nlinarith [dist_nonneg (x := pole i) (y := x a)]

private theorem full_simplex_locus {α : Type*} [Fintype α]
    (x : α → E₅) (hi : AffineIndependent ℝ x) (hc : Fintype.card α = 5)
    (hn : ∀ a, ‖x a‖ = 1 / 4)
    (hx : ∀ a, x a ∈ (embed 4 (by omega)).toLinearMap.range) (p : E₅) :
    (∀ a, dist p (x a) = 1) ↔ p = north ∨ p = -north := by
  classical
  haveI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let a₀ := Classical.arbitrary α
  let W := CosphericalUnitLocus.anchorDirection x a₀
  let K := (embed 4 (by omega)).toLinearMap.range
  let n : E₅ := EuclideanSpace.single 4 1
  have hK : Module.finrank ℝ K = 4 := by
    simpa [K] using LinearMap.finrank_range_of_inj (embed 4 (by omega)).injective
  have hW : CosphericalUnitLocus.anchorDirection x a₀ = K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact K.sub_mem (hx a) (hx a₀)
    · have hh := hi.finrank_vectorSpan_add_one
      have hh4 : Module.finrank ℝ (vectorSpan ℝ (Set.range x)) = 4 := by omega
      exact (congrArg (fun S : Submodule ℝ E₅ => Module.finrank ℝ S)
        (direction_eq x a₀)).trans (hh4.trans hK.symm)
  have hc0 : CosphericalUnitLocus.anchorCenter x a₀ = 0 := by
    change x a₀ - (CosphericalUnitLocus.anchorDirection x a₀).starProjection (x a₀) = 0
    rw [hW, Submodule.starProjection_eq_self_iff.mpr (hx a₀), sub_self]
  have hn1 : ‖n‖ = 1 := by simp [n, PiLp.norm_single]
  have hn0 : n ≠ 0 := by intro he; simpa [he] using hn1
  have hnp : n ∈ Kᗮ := by
    apply (K.mem_orthogonal' n).mpr
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    simp [n, EuclideanSpace.inner_single_left, embed_last (by omega : 4 ≤ 4)]
  have hperp : Kᗮ = ℝ ∙ n := by
    apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem n Kᗮ).mpr hnp)
    have hs := K.finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hn0]
    have he : Module.finrank ℝ E₅ = 5 := by simp
    omega
  have hlast (a : α) : x a 4 = 0 := by
    obtain ⟨v, hv⟩ := hx a
    rw [← hv]; exact embed_last (by omega : 4 ≤ 4) v
  constructor
  · intro hp
    have hh := (CosphericalUnitLocus.common_unit_locus_iff x a₀ (1 / 4) hn p).mp hp
    rw [hc0, sub_zero, hW, hperp] at hh
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hh.1
    have hs : t ^ 2 = (Real.sqrt 15 / 4) ^ 2 := by
      have h := hh.2
      rw [← ht, norm_smul, Real.norm_eq_abs, hn1] at h
      have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
      simp only [mul_one, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
      nlinarith [sq_abs t]
    have ht' : t = Real.sqrt 15 / 4 ∨ t = -(Real.sqrt 15 / 4) :=
      (sq_eq_sq_iff_eq_or_eq_neg).mp hs
    rcases ht' with ht' | ht'
    · left; rw [← ht, ht']; ext i; simp [north, n, PiLp.single_apply]
    · right; rw [← ht, ht']; ext i; simp [north, n, PiLp.single_apply]
  · rintro (rfl | rfl)
    · simpa [pole] using pole_unit x hn hlast 0
    · simpa [pole] using pole_unit x hn hlast 1

private theorem place_simplex_rows {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (hc : Fintype.card α ≤ 5) (N : β → Finset α)
    (hfull : (Finset.univ.filter (fun b => N b = Finset.univ)).card ≤ 2) :
    ∃ x : α → E₅, ∃ y : β → E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  obtain ⟨x, hxi, hxn, hxq, hxrange⟩ := independent_anchors hc
  have hxlast (a : α) : x a 4 = 0 := by
    obtain ⟨p, hp⟩ := hxrange a
    rw [← hp]
    exact embed_last (by norm_num : 4 ≤ 4) p
  let F := Finset.univ.filter (fun b => N b = Finset.univ)
  let e : F ↪ Fin 2 := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe, Fintype.card_fin] using hfull))
  let y₀ : F → E₅ := fun b => pole (e b)
  have hnorm (b : F) : y₀ b ∈ omega := by
    change (1 / 4 : ℝ) < ‖pole (e b)‖ ∧ ‖pole (e b)‖ < 1
    rw [pole_norm]
    exact north_omega
  have hrow (b : F) (a : α) : dist (y₀ b) (x a) = 1 ↔ a ∈ N b.val := by
    have hb : N b.val = Finset.univ := (Finset.mem_filter.mp b.property).2
    simp only [hb, Finset.mem_univ, iff_true]
    by_cases hc5 : Fintype.card α = 5
    · apply ((full_simplex_locus x hxi hc5 hxn hxrange (y₀ b)).mpr ?_) a
      simp only [y₀, pole]
      split <;> simp
    · exact pole_unit x hxn hxlast (e b) a
  have hsmall (b : β) (hb : b ∉ F) : (N b).card ≤ 4 := by
    have hne : N b ≠ Finset.univ := by simpa only [F, Finset.mem_filter,
      Finset.mem_univ, true_and] using hb
    have hh := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
    have hcu : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
    omega
  obtain ⟨y, hyi, hyu, hyn, hyr, _⟩ := place_rows x hxn north north_omega hxq N F y₀
    (pole_injective.comp e.injective) (fun b c => pole_nonunit (e b) (e c)) hnorm hrow
    (by intro b hb a₀; exact row_dimension x (N b) (hsmall b hb) a₀)
    (by intro b _ a₀ a ha; exact independent_separation x hxi (N b) a₀ a ha)
  exact ⟨x, y, hxi.injective, hxn, hyi, hyu, hyn, hyr⟩

private theorem equatorial_anchors {α : Type*} [Fintype α]
    (H : Finset α) (hc : Fintype.card α = 5) (hH : H.card = 4) :
    ∃ x : α → E₅, ∃ K : Submodule ℝ E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      (∀ a, dist north (x a) = 1) ∧ Module.finrank ℝ K ≤ 3 ∧
      (∀ a, x a ∈ K) ∧
      (∀ T : Finset α, T.card ≤ 3 → AffineIndepOn ℝ x (T : Set α)) ∧
      (∀ a₀ : α, Module.finrank ℝ (CosphericalUnitLocus.anchorDirection x a₀) = 3) ∧
      (∀ a₀ : H, Module.finrank ℝ
        (CosphericalUnitLocus.anchorDirection (fun a : H => x a.val) a₀) ≤ 2) ∧
      ∀ a ∉ H, x a ∉ affineSpan ℝ (x '' (H : Set α)) := by
  classical
  have hh : (Finset.univ \ H).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hc, hH]
  obtain ⟨c, hcH⟩ := Finset.card_eq_one.mp hh
  have hout (a : α) : a ∉ H ↔ a = c := by
    have := congrArg (fun S : Finset α => a ∈ S) hcH
    simpa using this
  have hcnot : c ∉ H := (hout c).mpr rfl
  obtain ⟨z, hzi, hzn, _, hzr, hzgp⟩ := general_anchors (α := α) 2 (by omega) (by omega)
  let L := (embed 2 (by omega)).toLinearMap.range
  let p : E₅ := EuclideanSpace.single 2 (1 / 4)
  have hz2 (a : α) : z a 2 = 0 := by
    obtain ⟨v, hv⟩ := hzr a
    rw [← hv]
    apply LinearIsometry.piLpExtendByZero_apply_eq_zero
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    simp only [Fin.castLEEmb_apply, Fin.val_castLE] at this
    omega
  have hpL : p ∉ L := by
    rintro ⟨v, hv⟩
    have hh := congrArg (fun w : E₅ => w 2) hv
    have hv2 : embed 2 (by omega) v 2 = 0 := by
      apply LinearIsometry.piLpExtendByZero_apply_eq_zero
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp only [Fin.castLEEmb_apply, Fin.val_castLE] at this
      omega
    simp [p, hv2] at hh
  let x : α → E₅ := Function.update z c p
  have hxc : x c = p := Function.update_self _ _ _
  have hxz (a : α) (ha : a ≠ c) : x a = z a := Function.update_of_ne ha _ _
  have hxL (a : α) (ha : a ≠ c) : x a ∈ L := by rw [hxz a ha]; exact hzr a
  have hspan (T : Finset α) (hTc : c ∉ T) : affineSpan ℝ (x '' (T : Set α)) ≤
      L.toAffineSubspace := by
    apply affineSpan_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact hxL a (fun he => hTc (he ▸ ha))
  have hgp (T : Finset α) (hT : T.card ≤ 3) : AffineIndepOn ℝ x (T : Set α) := by
    by_cases hcT : c ∈ T
    · have hi : AffineIndepOn ℝ x (↑(T.erase c) : Set α) :=
        (hzgp (T.erase c) (by exact (Finset.card_erase_le).trans hT)).congr (by
          intro a ha
          exact (hxz a (Finset.mem_erase.mp ha).1).symm)
      have hnot : x c ∉ affineSpan ℝ (x '' (↑(T.erase c) : Set α)) := by
        rw [hxc]
        exact fun h => hpL (hspan (T.erase c) (Finset.notMem_erase _ _) h)
      have hh := hi.insert hnot
      simpa only [← Finset.coe_insert, Finset.insert_erase hcT] using hh
    · exact (hzgp T hT).congr (by
        intro a ha
        exact (hxz a (fun he => hcT (he ▸ ha))).symm)
  let K := L ⊔ ℝ ∙ p
  have hL : Module.finrank ℝ L = 2 := by
    simpa [L] using LinearMap.finrank_range_of_inj (embed 2 (by omega)).injective
  have hdim : Module.finrank ℝ K ≤ 3 := by
    have hp0 : p ≠ 0 := by
      intro he; apply hpL; rw [he]; exact L.zero_mem
    have hline : Module.finrank ℝ (ℝ ∙ p) = 1 := finrank_span_singleton hp0
    have hh := Submodule.finrank_sup_add_finrank_inf_eq L (ℝ ∙ p)
    dsimp only [K]
    omega
  have hxK (a : α) : x a ∈ K := by
    by_cases ha : a = c
    · subst a; rw [hxc]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self p)
    · exact Submodule.mem_sup_left (hxL a ha)
  have hfull (a₀ : α) : Module.finrank ℝ (CosphericalUnitLocus.anchorDirection x a₀) = 3 := by
    obtain ⟨T, hTH, hT⟩ := Finset.exists_subset_card_eq (show 3 ≤ H.card by omega)
    have hcT : c ∉ T := fun h => hcnot (hTH h)
    have hnot : x c ∉ affineSpan ℝ (x '' (T : Set α)) := by
      rw [hxc]; exact fun h => hpL (hspan T hcT h)
    have hi := (hgp T (by omega)).insert hnot
    exact rank_of_four x K hdim hxK (insert c T) (by simp [hcT, hT])
      (by simpa only [Finset.coe_insert] using hi) a₀
  have hHdim (a₀ : H) : Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : H => x a.val) a₀) ≤ 2 := by
    have hW : CosphericalUnitLocus.anchorDirection (fun a : H => x a.val) a₀ ≤ L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact L.sub_mem (hxL a.val (fun he => hcnot (he ▸ a.property)))
        (hxL a₀.val (fun he => hcnot (he ▸ a₀.property)))
    exact (Submodule.finrank_mono hW).trans hL.le
  refine ⟨x, K, ?_, ?_, ?_, hdim, hxK, hgp, hfull, hHdim, ?_⟩
  · intro a b he
    by_cases ha : a = c <;> by_cases hb : b = c
    · exact ha.trans hb.symm
    · subst a
      rw [hxc] at he
      exact (hpL (he.symm ▸ hxL b hb)).elim
    · subst b
      rw [hxc] at he
      exact (hpL (he ▸ hxL a ha)).elim
    · rw [hxz a ha, hxz b hb] at he
      exact hzi he
  · intro a
    by_cases ha : a = c
    · subst a; rw [hxc]; norm_num [p, PiLp.norm_single]
    · rw [hxz a ha]; exact hzn a
  · intro a
    have hn : ‖x a‖ = 1 / 4 := by
      by_cases ha : a = c
      · subst a; rw [hxc]; norm_num [p, PiLp.norm_single]
      · rw [hxz a ha]; exact hzn a
    have hx4 : x a 4 = 0 := by
      by_cases ha : a = c
      · subst a; simp [hxc, p]
      · rw [hxz a ha]
        obtain ⟨v, hv⟩ := hzr a
        rw [← hv]; exact embed_last (by omega : 2 ≤ 4) v
    simpa [pole] using pole_unit x (fun b => by
      by_cases hb : b = c
      · subst b; rw [hxc]; norm_num [p, PiLp.norm_single]
      · rw [hxz b hb]; exact hzn b) (fun b => by
        by_cases hb : b = c
        · subst b; simp [hxc, p]
        · rw [hxz b hb]
          obtain ⟨v, hv⟩ := hzr b
          rw [← hv]; exact embed_last (by omega : 2 ≤ 4) v) 0 a
  · intro a ha
    have he := (hout a).mp ha
    subst a
    rw [hxc]
    exact fun h => hpL (hspan H hcnot h)

private theorem place_equatorial_rows {α β : Type*} [Fintype α] [Fintype β]
    (hc : Fintype.card α = 5) (N : β → Finset α) (H : Finset α) (hH : H.card = 4)
    (hN : ∀ b, N b = Finset.univ ∨ N b = H ∨ (N b).card ≤ 2) :
    ∃ x : α → E₅, ∃ y : β → E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  obtain ⟨x, K, hxi, hxn, hxq, hKd, hxK, hxgp, hfull, hHdim, hxH⟩ := equatorial_anchors H hc hH
  have hdim (b : β) (a₀ : N b) : 2 ≤ Module.finrank ℝ
      (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀)ᗮ := by
    rcases hN b with hb | hb | hb
    · have hi := hfull a₀.val
      have hf : CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀ =
          CosphericalUnitLocus.anchorDirection x a₀.val := by
        apply congrArg (Submodule.span ℝ)
        ext p; constructor
        · rintro ⟨a, rfl⟩; exact Set.mem_range_self a.val
        · rintro ⟨a, rfl⟩; exact ⟨⟨a, by simp [hb]⟩, rfl⟩
      have hs := (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀).finrank_add_finrank_orthogonal
      have he := congrArg (fun S : Submodule ℝ E₅ => Module.finrank ℝ S) hf
      have h5 : Module.finrank ℝ E₅ = 5 := by simp
      omega
    · subst H
      have hr := hHdim a₀
      have hs := (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀).finrank_add_finrank_orthogonal
      have h5 : Module.finrank ℝ E₅ = 5 := by simp
      omega
    · have hr := row_rank_le_two x (N b) (by omega) a₀
      have hs := (CosphericalUnitLocus.anchorDirection (fun a : N b => x a.val) a₀).finrank_add_finrank_orthogonal
      have h5 : Module.finrank ℝ E₅ = 5 := by simp
      omega
  obtain ⟨y, hyi, hyu, hyn, hyr, _⟩ := place_rows x hxn north north_omega hxq N
    (∅ : Finset β) (fun b : (∅ : Finset β) => False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
    (by intro b _ a₀; exact hdim b a₀)
    (by
      intro b _ a₀ a ha
      rcases hN b with hb | hb | hb
      · simp [hb] at ha
      · apply separated_direction x (N b) a₀ a
        simpa only [hb] using hxH a (by simpa [hb] using ha)
      · exact general_separation x hxgp (N b) hb a₀ a ha)
  exact ⟨x, y, hxi, hxn, hyi, hyu, hyn, hyr⟩

private theorem place_empty_rows {α β : Type*} [Fintype α] [Fintype β] [IsEmpty α]
    (N : β → Finset α) :
    ∃ x : α → E₅, ∃ y : β → E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  let e := Fintype.equivFin β
  let D : ℝ := 4 * (Fintype.card β + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  let t : β → ℝ := fun b => 1 / 2 + (e b).val / D
  have ht (b : β) : (1 / 2 : ℝ) ≤ t b ∧ t b < 3 / 4 := by
    have hn : ((e b).val : ℝ) < Fintype.card β + 1 := by
      exact_mod_cast (show (e b).val < Fintype.card β + 1 by omega)
    have hdiv : ((e b).val : ℝ) / D < 1 / 4 := by
      apply (div_lt_iff₀ hD).mpr
      dsimp only [D]; linarith
    exact ⟨by dsimp only [t]; linarith [div_nonneg (Nat.cast_nonneg (e b).val) hD.le],
      by dsimp only [t]; linarith⟩
  let y : β → E₅ := fun b => EuclideanSpace.single 0 (t b)
  have hd (b c : β) : dist (y b) (y c) < 1 := by
    change dist (EuclideanSpace.single (0 : Fin 5) (t b)) (EuclideanSpace.single (0 : Fin 5) (t c)) < 1
    rw [PiLp.dist_single_same, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [(ht b).1, (ht c).2], by linarith [(ht b).2, (ht c).1]⟩
  refine ⟨fun a => isEmptyElim a, y, fun a => isEmptyElim a,
    fun a => isEmptyElim a, ?_, fun b c => ne_of_lt (hd b c), ?_, fun _ a => isEmptyElim a⟩
  · intro b c he
    have he' := congrArg (fun p : E₅ => p 0) he
    change t b = t c at he'
    have hh : ((e b).val : ℝ) = (e c).val := by
      apply (div_left_inj' hD.ne').mp
      dsimp only [t] at he'; linarith
    exact e.injective (Fin.ext (Nat.cast_injective hh))
  · intro b
    have hn : ‖y b‖ = t b := by
      change ‖EuclideanSpace.single (0 : Fin 5) (t b)‖ = t b
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith [(ht b).1])]
    change (1 / 4 : ℝ) < ‖y b‖ ∧ ‖y b‖ < 1
    rw [hn]; constructor <;> linarith [(ht b).1, (ht b).2]

private theorem place_budget_rows {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (hc : Fintype.card α ≤ 5) (N : β → Finset α)
    (hsum : ∑ b, (N b).card ≤ 21) :
    ∃ x : α → E₅, ∃ y : β → E₅,
      Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
      Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, y b ∈ omega) ∧ ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  by_cases hc0 : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hc0
    exact place_empty_rows N
  by_cases hc4 : Fintype.card α ≤ 4
  · obtain ⟨x, hxi, hxn, hxq, _⟩ := independent_anchors hc
    obtain ⟨y, hyi, hyu, hyn, hyr, _⟩ := place_rows x hxn north north_omega hxq N
      (∅ : Finset β) (fun b : (∅ : Finset β) => False.elim (Finset.notMem_empty _ b.property))
      (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
      (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
      (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
      (by intro b; exact False.elim (Finset.notMem_empty _ b.property))
      (by intro b _ a₀; exact row_dimension x (N b) ((Finset.card_le_univ _).trans hc4) a₀)
      (by intro b _ a₀ a ha; exact independent_separation x hxi (N b) a₀ a ha)
    exact ⟨x, y, hxi.injective, hxn, hyi, hyu, hyn, hyr⟩
  have hc5 : Fintype.card α = 5 := by omega
  let F := Finset.univ.filter (fun b => N b = Finset.univ)
  by_cases hF : F.card ≤ 2
  · exact place_simplex_rows hc N hF
  have hF3 : 3 ≤ F.card := by omega
  have hfullsum : ∑ b ∈ F, (N b).card = 5 * F.card := by
    calc
      _ = ∑ _b ∈ F, 5 := Finset.sum_congr rfl (fun b hb => by
        rw [(Finset.mem_filter.mp hb).2, Finset.card_univ, hc5])
      _ = _ := by simp [Nat.mul_comm]
  have hrem : ∑ b ∈ Fᶜ, (N b).card ≤ 6 := by
    have hh := Finset.sum_add_sum_compl F (fun b => (N b).card)
    rw [hfullsum] at hh
    omega
  have hsmall (b : β) (hb : b ∈ Fᶜ) : (N b).card ≤ 4 := by
    have hne : N b ≠ Finset.univ := by simpa [F] using hb
    have hh := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
    simp only [Finset.card_univ, hc5] at hh
    omega
  by_cases hfour : ∃ b ∈ Fᶜ, (N b).card = 4
  · obtain ⟨b₀, hb₀, hN₀⟩ := hfour
    apply place_equatorial_rows hc5 N (N b₀) hN₀
    intro b
    by_cases hb : b ∈ F
    · exact Or.inl ((Finset.mem_filter.mp hb).2)
    have hb' : b ∈ Fᶜ := Finset.mem_compl.mpr hb
    by_cases he : b = b₀
    · exact Or.inr (Or.inl (he ▸ rfl))
    have hsum₀ := Finset.sum_erase_add (Fᶜ) (fun b => (N b).card) hb₀
    have hsingle : (N b).card ≤ ∑ b ∈ (Fᶜ).erase b₀, (N b).card :=
      Finset.single_le_sum (f := fun b => (N b).card) (fun b _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨he, hb'⟩)
    exact Or.inr (Or.inr (by omega))
  · apply place_three_dimensional_rows hc5 N
    intro b
    by_cases hb : b ∈ F
    · exact Or.inl ((Finset.mem_filter.mp hb).2)
    have hb' : b ∈ Fᶜ := Finset.mem_compl.mpr hb
    have hh := hsmall b hb'
    have hh4 : (N b).card ≠ 4 := fun he => hfour ⟨b, hb', he⟩
    exact Or.inr (by omega)

private theorem combine_placement {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (x : A → E₅) (hxi : Function.Injective x) (hxn : ∀ a, ‖x a‖ = 1 / 4)
    (y : B → E₅) (hyi : Function.Injective y)
    (hyu : ∀ b c, dist (y b) (y c) ≠ 1) (hyn : ∀ b, y b ∈ omega)
    (hxy : ∀ a : A, ∀ b : B, G.Adj a.val b.val ↔ dist (x a) (y b) = 1) :
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v, G.Adj u v ↔ dist (P u) (P v) = 1) ∧
      (∀ a ∈ A, ‖P a‖ = 1 / 4) ∧
      (∀ a ∈ A, ∀ a' ∈ A, dist (P a) (P a') < 1) ∧
      (∀ b ∈ B, (1 / 4 : ℝ) < ‖P b‖ ∧ ‖P b‖ < 1) ∧
      ∀ b ∈ B, ∀ b' ∈ B, dist (P b) (P b') < 2 := by
  classical
  have hAB (a : V) (ha : a ∈ A) : a ∉ B := fun hb => Set.disjoint_left.mp hG.disjoint ha hb
  have hBA (b : V) (hb : b ∈ B) : b ∉ A := fun ha => hAB b ha hb
  have hB (v : V) (hv : v ∉ A) : v ∈ B := by
    exact (hcover v).resolve_left hv
  let P : V → E₅ := fun v => if hv : v ∈ A then x ⟨v, hv⟩ else y ⟨v, hB v hv⟩
  have hPA (a : A) : P a.val = x a := by simp [P, a.property]
  have hPB (b : B) : P b.val = y b := by simp [P, hBA b.val b.property]
  have hAn (a : A) : ‖P a.val‖ = 1 / 4 := by rw [hPA]; exact hxn a
  have hBn (b : B) : (1 / 4 : ℝ) < ‖P b.val‖ ∧ ‖P b.val‖ < 1 := by
    rw [hPB]; exact hyn b
  have hAd (a c : A) : dist (P a.val) (P c.val) < 1 := by
    calc
      dist (P a.val) (P c.val) ≤ ‖P a.val‖ + ‖P c.val‖ := dist_le_norm_add_norm _ _
      _ < 1 := by rw [hAn a, hAn c]; norm_num
  have hBd (b c : B) : dist (P b.val) (P c.val) < 2 :=
    (dist_le_norm_add_norm _ _).trans_lt (by linarith [(hBn b).2, (hBn c).2])
  refine ⟨P, ?_, ?_, fun a ha => hAn ⟨a, ha⟩,
    fun a ha c hc => hAd ⟨a, ha⟩ ⟨c, hc⟩, fun b hb => hBn ⟨b, hb⟩,
    fun b hb c hc => hBd ⟨b, hb⟩ ⟨c, hc⟩⟩
  · intro u v he
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
    · rw [hPA ⟨u, hu⟩, hPA ⟨v, hv⟩] at he
      exact congrArg Subtype.val (hxi he)
    · have hvB := hB v hv
      have hn := congrArg norm he
      rw [hAn ⟨u, hu⟩] at hn
      exact (lt_irrefl (1 / 4 : ℝ) ((hBn ⟨v, hvB⟩).1.trans_eq hn.symm)).elim
    · have huB := hB u hu
      have hn := congrArg norm he
      rw [hAn ⟨v, hv⟩] at hn
      exact (lt_irrefl (1 / 4 : ℝ) ((hBn ⟨u, huB⟩).1.trans_eq hn)).elim
    · rw [hPB ⟨u, hB u hu⟩, hPB ⟨v, hB v hv⟩] at he
      exact congrArg Subtype.val (hyi he)
  · intro u v
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
    · have hnot : ¬G.Adj u v := fun h => hAB v hv (hG.mem_of_mem_adj hu h)
      exact iff_of_false hnot (ne_of_lt (hAd ⟨u, hu⟩ ⟨v, hv⟩))
    · rw [hPA ⟨u, hu⟩, hPB ⟨v, hB v hv⟩]
      exact hxy ⟨u, hu⟩ ⟨v, hB v hv⟩
    · rw [G.adj_comm, dist_comm, hPA ⟨v, hv⟩, hPB ⟨u, hB u hu⟩]
      exact hxy ⟨v, hv⟩ ⟨u, hB u hu⟩
    · have huB := hB u hu
      have hvB := hB v hv
      have hnot : ¬G.Adj u v := fun h => hBA v hvB (hG.symm.mem_of_mem_adj huB h)
      rw [hPB ⟨u, huB⟩, hPB ⟨v, hvB⟩]
      exact iff_of_false hnot (hyu _ _)

/-- Every finite simple graph with a full bipartition, at most five vertices
on its first side and at most twenty-one edges has one injective faithful
placement on its original vertex type. The anchor diameter is below one,
and the opposite side lies strictly between radii one quarter and one. -/
theorem exists_faithful_five_anchor_placement {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ v, v ∈ A ∨ v ∈ B) (hA : A.card ≤ 5)
    (hE : G.edgeFinset.card ≤ 21) :
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v, G.Adj u v ↔ dist (P u) (P v) = 1) ∧
      (∀ a ∈ A, ‖P a‖ = 1 / 4) ∧
      (∀ a ∈ A, ∀ a' ∈ A, dist (P a) (P a') < 1) ∧
      (∀ b ∈ B, (1 / 4 : ℝ) < ‖P b‖ ∧ ‖P b‖ < 1) ∧
      ∀ b ∈ B, ∀ b' ∈ B, dist (P b) (P b') < 2 := by
  classical
  let N : B → Finset A := fun b => Finset.univ.filter (fun a => G.Adj a.val b.val)
  have hdegree (b : B) : (N b).card = G.degree b.val := by
    have he : N b = (G.neighborFinset b.val).subtype (fun a => a ∈ A) := by
      ext a
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_subtype, SimpleGraph.mem_neighborFinset, G.adj_comm]
    rw [he, Finset.card_subtype]
    have hf : (G.neighborFinset b.val).filter (fun a => a ∈ A) =
        G.neighborFinset b.val := Finset.filter_eq_self.mpr
      (fun a ha => hG.symm.mem_of_mem_adj b.property ((G.mem_neighborFinset _ _).mp ha))
    rw [hf, G.card_neighborFinset_eq_degree]
  have hsum : ∑ b, (N b).card ≤ 21 := by
    calc
      ∑ b, (N b).card = ∑ b : B, G.degree b.val := Finset.sum_congr rfl (fun b _ => hdegree b)
      _ = ∑ b ∈ B, G.degree b := by simpa using (Finset.sum_attach B (fun b => G.degree b))
      _ = G.edgeFinset.card := G.isBipartiteWith_sum_degrees_eq_card_edges' hG
      _ ≤ 21 := hE
  obtain ⟨x, y, hxi, hxn, hyi, hyu, hyn, hyr⟩ :=
    place_budget_rows (by simpa using hA) N hsum
  apply combine_placement G A B hG hcover x hxi hxn y hyi hyu hyn
  intro a b
  simpa only [N, Finset.mem_filter, Finset.mem_univ, true_and, dist_comm] using (hyr b a).symm

end D5.S3.Geometry.FiveAnchorFaithfulPlacement
