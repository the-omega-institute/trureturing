/- GID: D5/S3/Geometry/FaithfulBipartiteTwentyOne
   generality: G
   mirror-B: D5/B/S3/Geometry/FaithfulBipartiteTwentyOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Faithful bipartite realizations at the twenty-one-edge budget. -/
module

public import D5.S3.Geometry.FiveAnchorFaithfulPlacement
import all D5.S3.Geometry.FiveAnchorFaithfulPlacement
public import D5.S3.Geometry.LowDegreeFaithfulExtension
import all D5.S3.Geometry.CosphericalUnitLocus

/-! Exceptional latitudes, followed by fixed-label low-degree restoration.
The final carrier includes every original isolated vertex. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.FaithfulBipartiteTwentyOne

local notation "E₅" => EuclideanSpace ℝ (Fin 5)

open FiveAnchorFaithfulPlacement

private def equatorialProjection : E₅ →ₗ[ℝ] E₅ where
  toFun p := p - p 4 • EuclideanSpace.single 4 1
  map_add' p q := by simp only [PiLp.add_apply, add_smul]; module
  map_smul' t p := by simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; module

private theorem projection_latitude (p : E₅) (hp : p 4 = 0) (s t : ℝ) :
    equatorialProjection (s • p + EuclideanSpace.single 4 t) = s • p := by
  ext i
  by_cases hi : i = 4
  · subst i; simp [equatorialProjection, hp]
  · simp [equatorialProjection, hp, hi]

/-- The two latitude signs retain every affine independence visible in the
uniform nonzero equatorial projection. The pole is checked against each
label, including every label outside the exceptional neighborhood. -/
private theorem latitude_anchors {α : Type*} [Finite α] (H : Finset α) :
    ∃ x : α → E₅, Function.Injective x ∧
      (∀ a, ‖x a‖ = 1 / 4) ∧
      (∀ T : Finset α, T.card ≤ 5 → AffineIndepOn ℝ x (T : Set α)) ∧
      ∃ p : E₅, (1 / 4 : ℝ) < ‖p‖ ∧
        ∀ a, dist p (x a) = 1 ↔ a ∈ H := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨y, hyi, hyn, _, hyr, hyg⟩ := general_anchors (α := α) 4 (by norm_num) (by norm_num)
  have hy4 (a : α) : y a 4 = 0 := by
    obtain ⟨z, hz⟩ := hyr a
    rw [← hz]
    exact embed_last (by norm_num : 4 ≤ 4) z
  let s : ℝ := Real.sqrt 3 / 2
  have hs : s ≠ 0 := ne_of_gt (by dsimp [s]; positivity)
  have hs2 : s ^ 2 = 3 / 4 := by
    dsimp [s]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  let t : α → ℝ := fun a => if a ∈ H then 1 / 8 else -1 / 8
  let x : α → E₅ := fun a => s • y a + EuclideanSpace.single 4 (t a)
  have ht2 (a : α) : t a ^ 2 = 1 / 64 := by dsimp [t]; split <;> norm_num
  have hx4 (a : α) : x a 4 = t a := by simp [x, hy4]
  have hxnorm (a : α) : ‖x a‖ = 1 / 4 := by
    have hi : ⟪s • y a, EuclideanSpace.single 4 (t a)⟫_ℝ = 0 := by
      simp [EuclideanSpace.inner_single_right, hy4]
    have hh := norm_add_sq_real (s • y a) (EuclideanSpace.single 4 (t a))
    simp only [hi, mul_zero, add_zero, norm_smul, Real.norm_eq_abs,
      PiLp.norm_single, mul_pow, sq_abs, hyn, hs2, ht2] at hh
    change ‖x a‖ ^ 2 = _ at hh
    nlinarith [norm_nonneg (x a)]
  have hproj (a : α) : equatorialProjection (x a) = s • y a :=
    projection_latitude (y a) (hy4 a) s (t a)
  have hxgp (T : Finset α) (hT : T.card ≤ 5) : AffineIndepOn ℝ x (T : Set α) := by
    apply AffineIndepOn.of_comp equatorialProjection.toAffineMap
    have hi := (hyg T hT).map' (s • (LinearMap.id : E₅ →ₗ[ℝ] E₅)).toAffineMap
      (by intro u v h; exact (smul_right_injective _ hs) h)
    change AffineIndepOn ℝ (fun a => s • y a) (T : Set α) at hi
    change AffineIndepOn ℝ (fun a => equatorialProjection (x a)) (T : Set α)
    simpa only [hproj] using hi
  have hxi : Function.Injective x := by
    intro a b hab
    apply hyi
    exact (smul_right_injective _ hs)
      (by simpa only [hproj] using congrArg equatorialProjection hab)
  let k : ℝ := (1 + Real.sqrt 61) / 8
  have hk2 : k ^ 2 - k / 4 = 15 / 16 := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61)]
  have hk : 1 / 4 < k := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61), Real.sqrt_nonneg 61]
  let p : E₅ := EuclideanSpace.single 4 k
  have hpn : ‖p‖ = k := by simp [p, PiLp.norm_single, abs_of_pos (by linarith : 0 < k)]
  have hdist (a : α) : dist p (x a) ^ 2 = k ^ 2 + 1 / 16 - 2 * k * t a := by
    rw [dist_eq_norm, norm_sub_sq_real, hpn, hxnorm]
    simp [p, EuclideanSpace.inner_single_left, hx4]
    ring
  refine ⟨x, hxi, hxnorm, hxgp, p, by rw [hpn]; exact hk, fun a => ?_⟩
  by_cases ha : a ∈ H
  · have ht : t a = 1 / 8 := by simp [t, ha]
    constructor
    · intro _; exact ha
    · intro _
      have hh := hdist a
      rw [ht] at hh
      nlinarith [dist_nonneg (x := p) (y := x a)]
  · have ht : t a = -1 / 8 := by simp [t, ha]
    constructor
    · intro hd
      have hh := hdist a
      rw [ht, hd] at hh
      nlinarith
    · exact fun h => (ha h).elim

private theorem common_unit_nonempty {α : Type*} [Finite α]
    (x : α → E₅) (hx : ∀ a, ‖x a‖ = 1 / 4)
    (N : Finset α) (hN : N.card ≤ 4) (a₀ : N) :
    ∃ p : E₅, ∀ a : N, dist p (x a.val) = 1 := by
  classical
  letI := Fintype.ofFinite α
  let W := CosphericalUnitLocus.anchorDirection (fun a : N => x a.val) a₀
  let c := CosphericalUnitLocus.anchorCenter (fun a : N => x a.val) a₀
  let R := Real.sqrt (1 - (1 / 4 : ℝ) ^ 2 + ‖c‖ ^ 2)
  have hd : 2 ≤ Module.finrank ℝ Wᗮ := row_dimension x N hN a₀
  have : Nontrivial Wᗮ := Module.finrank_pos_iff (R := ℝ) |>.mp (by omega)
  have hpos : 0 < 1 - (1 / 4 : ℝ) ^ 2 + ‖c‖ ^ 2 := by positivity
  obtain ⟨w, hw⟩ := exists_norm_eq Wᗮ (show 0 ≤ R from Real.sqrt_nonneg _)
  refine ⟨c + (w : E₅), ?_⟩
  apply (CosphericalUnitLocus.common_unit_locus_iff (fun a : N => x a.val) a₀
    (1 / 4) (fun a => hx a.val) _).mpr
  constructor
  · change c + (w : E₅) - c ∈ Wᗮ
    simpa only [add_sub_cancel_left] using w.property
  · change ‖c + (w : E₅) - c‖ ^ 2 = 1 - (1 / 4 : ℝ) ^ 2 + ‖c‖ ^ 2
    rw [add_sub_cancel_left]
    change ‖w‖ ^ 2 = _
    rw [hw]
    exact Real.sq_sqrt hpos.le

private theorem choose_ordinary {α β : Type*} [Finite α] [Finite β]
    (x : α → E₅) (hx : ∀ a, ‖x a‖ = 1 / 4)
    (hgp : ∀ T : Finset α, T.card ≤ 5 → AffineIndepOn ℝ x (T : Set α))
    (N : Finset α) (hN : N.card ≤ 4) (hne : N.Nonempty)
    (y : β → E₅) (hy : ∀ b, (1 / 4 : ℝ) < ‖y b‖) :
    ∃ p : E₅, (1 / 4 : ℝ) < ‖p‖ ∧
      (∀ a, dist p (x a) = 1 ↔ a ∈ N) ∧
      (∀ b, dist p (y b) ≠ 1) ∧ ∀ b, p ≠ y b := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨a, ha⟩ := hne
  let a₀ : N := ⟨a, ha⟩
  obtain ⟨p₀, hp₀⟩ := common_unit_nonempty x hx N hN a₀
  let z : {a // a ∉ N} ⊕ β → E₅ := Sum.elim (fun a => x a.val) y
  obtain ⟨p, _, hpx, hpz, hpy⟩ := CosphericalUnitLocus.exists_common_unit_avoiding
    (fun a : N => x a.val) a₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) (fun a => hx a.val) (row_dimension x N hN a₀)
    isOpen_univ ⟨p₀, Set.mem_univ _, hp₀⟩ z y (by
      rintro (a | b)
      · exact Or.inr (general_separation x hgp N hN a₀ a.val a.property)
      · exact Or.inl (ne_of_gt (hy b)))
  have hlower : (3 / 4 : ℝ) ≤ ‖p‖ := by
    have hh := dist_le_norm_add_norm p (x a)
    rw [hpx a₀, hx] at hh
    linarith
  refine ⟨p, by linarith, fun a => ?_, fun b => hpz (.inr b), hpy⟩
  by_cases ha : a ∈ N
  · exact ⟨fun _ => ha, fun _ => hpx ⟨a, ha⟩⟩
  · exact ⟨fun h => (hpz (.inl ⟨a, ha⟩) h).elim, fun h => (ha h).elim⟩
private theorem place_positive_rows {α β : Type*} [Finite α] [Finite β]
    (x : α → E₅) (hx : ∀ a, ‖x a‖ = 1 / 4)
    (hgp : ∀ T : Finset α, T.card ≤ 5 → AffineIndepOn ℝ x (T : Set α))
    (N : β → Finset α)
    (s₀ : Finset β) (y₀ : s₀ → E₅) (hinj₀ : Function.Injective y₀)
    (hunit₀ : ∀ b c, dist (y₀ b) (y₀ c) ≠ 1)
    (hnorm₀ : ∀ b, (1 / 4 : ℝ) < ‖y₀ b‖)
    (hrow₀ : ∀ b : s₀, ∀ a, dist (y₀ b) (x a) = 1 ↔ a ∈ N b.val)
    (hsmall : ∀ b ∉ s₀, (N b).card ≤ 4)
    (hne : ∀ b, (N b).Nonempty) :
    ∃ y : β → E₅, Function.Injective y ∧ (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, (1 / 4 : ℝ) < ‖y b‖) ∧ (∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b) ∧
      ∀ b : s₀, y b.val = y₀ b := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
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
      choose_ordinary x hx hgp (N b) (hsmall b hbs) (hne b) y₀ hnorm₀
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
    have hnorm₁ : ∀ c, (1 / 4 : ℝ) < ‖y₁ c‖ := by
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
      (by intro c hc; exact hsmall c (fun h => hc (Finset.mem_insert_of_mem h))) hn₁
    exact ⟨y, hyi, hyu, hyn, hyr, fun c =>
      (hyo ⟨c.val, Finset.mem_insert_of_mem c.property⟩).trans (hold c)⟩

private theorem exceptional_rows {α β : Type*} [Finite α] [Fintype β]
    (N : β → Finset α) (hne : ∀ b, (N b).Nonempty)
    (hhigh : (Finset.univ.filter (fun b => 5 ≤ (N b).card)).card ≤ 1) :
    ∃ (x : α → E₅) (y : β → E₅), Function.Injective x ∧
      (∀ a, ‖x a‖ = 1 / 4) ∧ Function.Injective y ∧
      (∀ b c, dist (y b) (y c) ≠ 1) ∧
      (∀ b, (1 / 4 : ℝ) < ‖y b‖) ∧
      ∀ b a, dist (y b) (x a) = 1 ↔ a ∈ N b := by
  classical
  letI := Fintype.ofFinite α
  let T := Finset.univ.filter (fun b => 5 ≤ (N b).card)
  have huniq (b : T) (c : T) : b = c :=
    Subtype.ext ((Finset.card_le_one.mp hhigh) b.val b.property c.val c.property)
  have hsmall (b : β) (hb : b ∉ T) : (N b).card ≤ 4 := by
    have : ¬5 ≤ (N b).card := by simpa [T] using hb
    omega
  obtain ⟨x, hxi, hxn, hxg, y₀, hyi, hyu, hyn, hyr⟩ :
      ∃ x : α → E₅, Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
        (∀ U : Finset α, U.card ≤ 5 → AffineIndepOn ℝ x (U : Set α)) ∧
        ∃ y₀ : T → E₅, Function.Injective y₀ ∧
          (∀ b c, dist (y₀ b) (y₀ c) ≠ 1) ∧
          (∀ b, (1 / 4 : ℝ) < ‖y₀ b‖) ∧
          ∀ b : T, ∀ a, dist (y₀ b) (x a) = 1 ↔ a ∈ N b.val := by
    by_cases hT : T.Nonempty
    · obtain ⟨e, he⟩ := hT
      obtain ⟨x, hxi, hxn, hxg, p, hpn, hpr⟩ :
          ∃ x : α → E₅, Function.Injective x ∧ (∀ a, ‖x a‖ = 1 / 4) ∧
            (∀ U : Finset α, U.card ≤ 5 → AffineIndepOn ℝ x (U : Set α)) ∧
            ∃ p : E₅, (1 / 4 : ℝ) < ‖p‖ ∧
              ∀ a, dist p (x a) = 1 ↔ a ∈ N e := by
        by_cases hfull : N e = Finset.univ
        · obtain ⟨x, hxi, hxn, hxq, _, hxg⟩ := general_anchors (α := α) 4
            (by norm_num) (by norm_num)
          exact ⟨x, hxi, hxn, hxg, north, north_omega.1,
            fun a => by simp [hfull, hxq]⟩
        · exact latitude_anchors (N e)
      refine ⟨x, hxi, hxn, hxg, fun _ => p, ?_, ?_, fun _ => hpn, ?_⟩
      · intro b c _; exact huniq b c
      · intro b c; simp
      · intro b a
        have hb : b.val = e := congrArg Subtype.val (huniq b ⟨e, he⟩)
        simpa only [hb] using hpr a
    · obtain ⟨x, hxi, hxn, _, _, hxg⟩ := general_anchors (α := α) 4
        (by norm_num) (by norm_num)
      have hempty (b : T) : False := hT ⟨b.val, b.property⟩
      exact ⟨x, hxi, hxn, hxg, fun b => (hempty b).elim,
        fun b => (hempty b).elim, fun b => (hempty b).elim,
        fun b => (hempty b).elim, fun b => (hempty b).elim⟩
  obtain ⟨y, hyi, hyu, hyn, hyr, _⟩ :=
    place_positive_rows x hxn hxg N T y₀ hyi hyu hyn hyr hsmall hne
  exact ⟨x, y, hxi, hxn, hyi, hyu, hyn, hyr⟩

private theorem combine_rows {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B C : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V)) (hCA : C ⊆ A)
    (x : B → E₅) (hxi : Function.Injective x) (hxn : ∀ b, ‖x b‖ = 1 / 4)
    (y : C → E₅) (hyi : Function.Injective y)
    (hyu : ∀ c d, dist (y c) (y d) ≠ 1) (hyn : ∀ c, (1 / 4 : ℝ) < ‖y c‖)
    (hyr : ∀ c : C, ∀ b : B, dist (y c) (x b) = 1 ↔ G.Adj c.val b.val) :
    ∃ p : ↥(C ∪ B) → E₅, Function.Injective p ∧
      (∀ u v : ↥(C ∪ B), G.Adj u.val v.val ↔ dist (p u) (p v) = 1) ∧
      ∀ b : B, p ⟨b.val, Finset.mem_union_right C b.property⟩ = x b := by
  classical
  have hCB (c : V) (hc : c ∈ C) : c ∉ B :=
    fun hb => Set.disjoint_left.mp hG.disjoint (hCA hc) hb
  have hC (v : ↥(C ∪ B)) (hv : v.val ∉ B) : v.val ∈ C :=
    (Finset.mem_union.mp v.property).resolve_right hv
  let p : ↥(C ∪ B) → E₅ := fun v =>
    if hv : v.val ∈ B then x ⟨v.val, hv⟩ else y ⟨v.val, hC v hv⟩
  have hpB (b : B) : p ⟨b.val, Finset.mem_union_right C b.property⟩ = x b := by
    simp [p, b.property]
  have hpC (c : C) : p ⟨c.val, Finset.mem_union_left B c.property⟩ = y c := by
    simp [p, hCB c.val c.property]
  have hnormB (v : ↥(C ∪ B)) (hv : v.val ∈ B) : ‖p v‖ = 1 / 4 := by
    rw [hpB ⟨v.val, hv⟩]; exact hxn _
  have hnormC (v : ↥(C ∪ B)) (hv : v.val ∉ B) : (1 / 4 : ℝ) < ‖p v‖ := by
    rw [hpC ⟨v.val, hC v hv⟩]; exact hyn _
  have hdistB (u v : ↥(C ∪ B)) (hu : u.val ∈ B) (hv : v.val ∈ B) :
      dist (p u) (p v) < 1 :=
    (dist_le_norm_add_norm _ _).trans_lt (by rw [hnormB u hu, hnormB v hv]; norm_num)
  refine ⟨p, ?_, ?_, hpB⟩
  · intro u v he
    by_cases hu : u.val ∈ B <;> by_cases hv : v.val ∈ B
    · rw [hpB ⟨u.val, hu⟩, hpB ⟨v.val, hv⟩] at he
      exact Subtype.ext (congrArg (fun b : B => b.val) (hxi he))
    · have hn := congrArg norm he
      rw [hnormB u hu] at hn
      exact (lt_irrefl (1 / 4 : ℝ) ((hnormC v hv).trans_eq hn.symm)).elim
    · have hn := congrArg norm he
      rw [hnormB v hv] at hn
      exact (lt_irrefl (1 / 4 : ℝ) ((hnormC u hu).trans_eq hn)).elim
    · rw [hpC ⟨u.val, hC u hu⟩, hpC ⟨v.val, hC v hv⟩] at he
      exact Subtype.ext (congrArg (fun c : C => c.val) (hyi he))
  · intro u v
    by_cases hu : u.val ∈ B <;> by_cases hv : v.val ∈ B
    · have hnot : ¬G.Adj u.val v.val := by
        intro h
        exact Set.disjoint_left.mp hG.disjoint (hG.symm.mem_of_mem_adj hu h) hv
      exact iff_of_false hnot (ne_of_lt (hdistB u v hu hv))
    · rw [hpB ⟨u.val, hu⟩, hpC ⟨v.val, hC v hv⟩, dist_comm, G.adj_comm]
      exact (hyr ⟨v.val, hC v hv⟩ ⟨u.val, hu⟩).symm
    · rw [hpC ⟨u.val, hC u hu⟩, hpB ⟨v.val, hv⟩]
      exact (hyr ⟨u.val, hC u hu⟩ ⟨v.val, hv⟩).symm
    · have hnot : ¬G.Adj u.val v.val := by
        intro h
        exact hCB v.val (hC v hv) (hG.mem_of_mem_adj (hCA (hC u hu)) h)
      rw [hpC ⟨u.val, hC u hu⟩, hpC ⟨v.val, hC v hv⟩]
      exact iff_of_false hnot (hyu _ _)

private theorem restore_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hsmall : ∀ a ∈ A, a ∉ C → G.degree a ≤ 2)
    (p : ↥(C ∪ B) → E₅) (hpi : Function.Injective p)
    (hpf : ∀ u v : ↥(C ∪ B), G.Adj u.val v.val ↔ dist (p u) (p v) = 1)
    (hdiam : ∀ b : B, ∀ c : B,
      dist (p ⟨b.val, Finset.mem_union_right C b.property⟩)
        (p ⟨c.val, Finset.mem_union_right C c.property⟩) < 2) :
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v, G.Adj u v ↔ dist (P u) (P v) = 1) ∧
      ∀ u : ↥(C ∪ B), P u.val = p u := by
  classical
  apply LowDegreeFaithfulExtension.exists_faithful_extension G B (C ∪ B)
    (Finset.subset_union_right) p hpi hpf
  · intro b hb c hc _; exact hdiam ⟨b, hb⟩ ⟨c, hc⟩
  · intro a ha b hb
    have haB : a ∉ B := fun h => ha (Finset.mem_union_right C h)
    exact hG.mem_of_mem_adj ((hcover a).resolve_right haB)
      ((G.mem_neighborFinset a b).mp hb)
  · intro a ha
    have haB : a ∉ B := fun h => ha (Finset.mem_union_right C h)
    exact hsmall a ((hcover a).resolve_right haB)
      (fun h => ha (Finset.mem_union_left B h))

private theorem exists_exceptional_placement {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hhigh : (A.filter (fun a => 5 ≤ G.degree a)).card ≤ 1) :
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v, G.Adj u v ↔ dist (P u) (P v) = 1) ∧
      (∀ b ∈ B, ‖P b‖ = 1 / 4) ∧
      ∀ b ∈ B, ∀ c ∈ B, dist (P b) (P c) < 1 := by
  classical
  let C := A.filter (fun a => 3 ≤ G.degree a)
  have hCA : C ⊆ A := Finset.filter_subset _ _
  let N : C → Finset B := fun c => Finset.univ.filter (fun b => G.Adj c.val b.val)
  have hdegree (c : C) : (N c).card = G.degree c.val := by
    have he : N c = (G.neighborFinset c.val).subtype (fun b => b ∈ B) := by
      ext b
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_subtype, SimpleGraph.mem_neighborFinset]
    rw [he, Finset.card_subtype]
    have hf : (G.neighborFinset c.val).filter (fun b => b ∈ B) =
        G.neighborFinset c.val := Finset.filter_eq_self.mpr
      (fun b hb => hG.mem_of_mem_adj (hCA c.property) ((G.mem_neighborFinset _ _).mp hb))
    rw [hf, G.card_neighborFinset_eq_degree]
  have hne (c : C) : (N c).Nonempty := by
    apply Finset.card_pos.mp
    rw [hdegree]
    have := (Finset.mem_filter.mp c.property).2
    omega
  have hhigh' : (Finset.univ.filter (fun c => 5 ≤ (N c).card)).card ≤ 1 := by
    calc
      _ ≤ (A.filter (fun a => 5 ≤ G.degree a)).card :=
        Finset.card_le_card_of_injOn (fun c : C => c.val)
          (by
            intro c hc
            exact Finset.mem_filter.mpr ⟨hCA c.property,
              by
                have hh := (Finset.mem_filter.mp hc).2
                rwa [hdegree] at hh⟩)
          (by intro c _ d _ he; exact Subtype.ext he)
      _ ≤ 1 := hhigh
  obtain ⟨x, y, hxi, hxn, hyi, hyu, hyn, hyr⟩ := exceptional_rows N hne hhigh'
  obtain ⟨p, hpi, hpf, hpB⟩ := combine_rows G A B C hG hCA x hxi hxn y hyi hyu hyn
    (by intro c b; simpa [N] using hyr c b)
  have hdiam (b c : B) :
      dist (p ⟨b.val, Finset.mem_union_right C b.property⟩)
        (p ⟨c.val, Finset.mem_union_right C c.property⟩) < 2 := by
    rw [hpB b, hpB c]
    exact (dist_le_norm_add_norm _ _).trans_lt (by rw [hxn, hxn]; norm_num)
  obtain ⟨P, hPi, hPf, hPo⟩ := restore_core G A B C hG hcover
    (by
      intro a ha hac
      have hn : ¬3 ≤ G.degree a := by simpa [C, ha] using hac
      omega)
    p hpi hpf hdiam
  have hPn (b : V) (hb : b ∈ B) : ‖P b‖ = 1 / 4 := by
    rw [hPo ⟨b, Finset.mem_union_right C hb⟩, hpB ⟨b, hb⟩]
    exact hxn _
  refine ⟨P, hPi, hPf, hPn, fun b hb c hc => ?_⟩
  exact (dist_le_norm_add_norm _ _).trans_lt (by rw [hPn b hb, hPn c hc]; norm_num)

private theorem exists_small_core {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hcover : ∀ v, v ∈ A ∨ v ∈ B) (hCA : C ⊆ A) (hC : C.card ≤ 5)
    (hsmall : ∀ a ∈ A, a ∉ C → G.degree a ≤ 2)
    (hE : G.edgeFinset.card ≤ 21) :
    ∃ P : V → E₅, Function.Injective P ∧
      ∀ u v, G.Adj u v ↔ dist (P u) (P v) = 1 := by
  classical
  let S := C ∪ B
  let C' : Finset S := C.subtype (fun v => v ∈ S)
  let B' : Finset S := B.subtype (fun v => v ∈ S)
  have hmemC (v : S) : v ∈ C' ↔ v.val ∈ C := by simp [C']
  have hmemB (v : S) : v ∈ B' ↔ v.val ∈ B := by simp [B']
  have hAtoC (v : S) (hv : v.val ∈ A) : v.val ∈ C := by
    rcases Finset.mem_union.mp v.property with hc | hb
    · exact hc
    · exact (Set.disjoint_left.mp hG.disjoint hv hb).elim
  have hG' : (G.induce (S : Set V)).IsBipartiteWith (C' : Set S) (B' : Set S) := by
    constructor
    · exact Set.disjoint_left.mpr (fun v hv hw =>
        Set.disjoint_left.mp hG.disjoint (hCA ((hmemC v).mp hv)) ((hmemB v).mp hw))
    · intro u v huv
      rcases hG.mem_of_adj huv with h | h
      · exact Or.inl ⟨(hmemC u).mpr (hAtoC u h.1), (hmemB v).mpr h.2⟩
      · exact Or.inr ⟨(hmemB u).mpr h.1, (hmemC v).mpr (hAtoC v h.2)⟩
  have hcover' (v : S) : v ∈ C' ∨ v ∈ B' := by
    simpa only [hmemC, hmemB] using Finset.mem_union.mp v.property
  have hcard : C'.card ≤ 5 := by
    have hf : C.filter (fun v => v ∈ S) = C :=
      Finset.filter_eq_self.mpr (fun v hv => Finset.mem_union_left B hv)
    simpa only [C', Finset.card_subtype, hf] using hC
  have hE' : (G.induce (S : Set V)).edgeFinset.card ≤ 21 := by
    rw [← G.card_filter_edgeFinset_toFinset_subset S]
    exact (Finset.card_filter_le _ _).trans hE
  obtain ⟨p, hpi, hpf, _, _, _, hdiam⟩ :=
    exists_faithful_five_anchor_placement (G.induce (S : Set V)) C' B' hG' hcover' hcard hE'
  obtain ⟨P, hPi, hPf, _⟩ := restore_core G A B C hG hcover hsmall p hpi hpf (by
    intro b c
    exact hdiam ⟨b.val, Finset.mem_union_right C b.property⟩
      ((hmemB _).mpr b.property) ⟨c.val, Finset.mem_union_right C c.property⟩
      ((hmemB _).mpr c.property))
  exact ⟨P, hPi, hPf⟩

/-- Every finite simple bipartite graph with at most twenty-one edges has
one injective faithful unit-distance realization in real five-space. The
map is total on the original vertex type, including every isolated vertex;
the equivalence concerns all ordered pairs, including diagonals. -/
theorem exists_faithful_realization_of_card_edges_le_twenty_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite) (hE : G.edgeFinset.card ≤ 21) :
    ∃ P : V → EuclideanSpace ℝ (Fin 5), Function.Injective P ∧
      ∀ u v : V, G.Adj u v ↔ dist (P u) (P v) = 1 := by
  classical
  obtain ⟨c, hc⟩ := hG
  let A : Finset V := Finset.univ.filter (fun v => c v = 0)
  let B : Finset V := Finset.univ.filter (fun v => c v = 1)
  have hcover (v : V) : v ∈ A ∨ v ∈ B := by
    have hcv : c v = 0 ∨ c v = 1 := by omega
    simpa [A, B] using hcv
  have hAB : G.IsBipartiteWith (A : Set V) (B : Set V) := by
    constructor
    · exact Set.disjoint_left.mpr (by intro v hv hw; simp_all [A, B])
    · intro u v huv
      have hne : c u ≠ c v := hc huv
      simp only [Finset.mem_coe, A, B, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  let C := A.filter (fun a => 3 ≤ G.degree a)
  let H := A.filter (fun a => 5 ≤ G.degree a)
  have hcount : 3 * C.card + 2 * H.card ≤ G.edgeFinset.card := by
    calc
      3 * C.card + 2 * H.card =
          (∑ a ∈ A, if 3 ≤ G.degree a then 3 else 0) +
          (∑ a ∈ A, if 5 ≤ G.degree a then 2 else 0) := by
        simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, C, H]
        omega
      _ = ∑ a ∈ A, ((if 3 ≤ G.degree a then 3 else 0) +
          (if 5 ≤ G.degree a then 2 else 0)) := (Finset.sum_add_distrib).symm
      _ ≤ ∑ a ∈ A, G.degree a := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs <;> omega
      _ = G.edgeFinset.card := G.isBipartiteWith_sum_degrees_eq_card_edges hAB
  by_cases hC : C.card ≤ 5
  · exact exists_small_core G A B C hAB hcover (Finset.filter_subset _ _) hC
      (by
        intro a ha hac
        have hn : ¬3 ≤ G.degree a := by simpa [C, ha] using hac
        omega) hE
  · have hH : H.card ≤ 1 := by omega
    obtain ⟨P, hPi, hPf, _, _⟩ := exists_exceptional_placement G A B hAB hcover hH
    exact ⟨P, hPi, hPf⟩

end D5.S3.Geometry.FaithfulBipartiteTwentyOne
