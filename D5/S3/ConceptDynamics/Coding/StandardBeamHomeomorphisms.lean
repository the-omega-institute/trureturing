/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Whole-ray images for every homeomorphism commuting with the original unit shift. -/
import D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion (shift)
open scoped BigOperators

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace V] [DiscreteTopology V]
variable [TopologicalSpace E] [DiscreteTopology E]

/-- Closedness of the ACTUAL legal subspace of the finite discrete product. -/
theorem legal_isClosed :
    IsClosed {x : ℤ → E | ∀ k, G.target (x k) = G.source (x (k + 1))} := by
  have ht : Continuous G.target := continuous_of_discreteTopology
  have hs : Continuous G.source := continuous_of_discreteTopology
  have he : {x : ℤ → E | ∀ k, G.target (x k) = G.source (x (k + 1))} =
      ⋂ k : ℤ, {x : ℤ → E | G.target (x k) = G.source (x (k + 1))} := by
    ext x
    simp
  rw [he]
  exact isClosed_iInter (fun k => isClosed_eq
    (ht.comp (continuous_apply k)) (hs.comp (continuous_apply (k + 1))))

instance historyCompactSpace : CompactSpace (History G) :=
  isCompact_iff_compactSpace.mp (legal_isClosed G).isCompact

/-- Honest composition convention: (g*h)(x)=g(h(x)). -/
def fullAutSubgroup : Subgroup (History G ≃ₜ History G) where
  carrier := {h | ∀ x, h (shift G x) = shift G (h x)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    change g (h (shift G x)) = shift G (g (h x))
    rw [hh, hg]
  inv_mem' := by
    intro h hh y
    change h.symm (shift G y) = shift G (h.symm y)
    apply h.injective
    simpa only [h.apply_symm_apply] using (hh (h.symm y)).symm

abbrev FullAut := fullAutSubgroup G

/-- Actual unit left shift, with its actual inverse, belongs to the FULL domain. -/
def unitShift : FullAut G := by
  let S : History G ≃ₜ History G := {
    toFun := shift G
    invFun := fun x => ⟨fun k => x.val (k - 1), fun k => by
      simpa only [sub_add_cancel, add_sub_cancel_right] using x.property (k - 1)⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext k
      simp [shift]
    right_inv := by
      intro x
      apply Subtype.ext
      funext k
      simp [shift]
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      exact (continuous_apply (k + 1)).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      exact (continuous_apply (k - 1)).comp continuous_subtype_val }
  exact ⟨S, fun _ => rfl⟩

def translate (t : ℤ) (x : History G) : History G :=
  ⟨fun k => x.val (k + t), fun k => by
    simpa [add_assoc, add_left_comm, add_comm] using x.property (k + t)⟩

@[simp] theorem translate_zero (x : History G) : translate G 0 x = x := by
  apply Subtype.ext
  funext k
  simp [translate]

theorem translate_add (s t : ℤ) (x : History G) :
    translate G s (translate G t x) = translate G (s + t) x := by
  apply Subtype.ext
  funext k
  simp [translate, add_assoc]

theorem commute_translate_nat (h : FullAut G) (n : ℕ) (x : History G) :
    h.val (translate G (n : ℤ) x) = translate G (n : ℤ) (h.val x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep (y : History G) : translate G ((n + 1 : ℕ) : ℤ) y =
        shift G (translate G (n : ℤ) y) := by
      apply Subtype.ext
      funext k
      simp [translate, shift, Int.natCast_add, add_assoc, add_left_comm, add_comm]
    rw [hstep, h.property, ih, ← hstep]

theorem commute_translate (h : FullAut G) (t : ℤ) (x : History G) :
    h.val (translate G t x) = translate G t (h.val x) := by
  cases t with
  | ofNat n => exact commute_translate_nat G h n x
  | negSucc n =>
    have ht : (Int.negSucc n : ℤ) + ((n + 1 : ℕ) : ℤ) = 0 := by omega
    have hinj : Function.Injective (translate G ((n + 1 : ℕ) : ℤ)) := by
      intro x y he
      have he' := congrArg (translate G (Int.negSucc n)) he
      simpa only [translate_add, ht, translate_zero] using he'
    apply hinj
    rw [← commute_translate_nat G h (n + 1), translate_add, translate_add]
    have ht' : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [ht', translate_zero, translate_zero]

def cylinder (s : Finset ℤ) (x : History G) : Set (History G) :=
  {y | ∀ k ∈ s, y.val k = x.val k}

theorem cylinder_open (s : Finset ℤ) (x : History G) : IsOpen (cylinder G s x) := by
  have he : cylinder G s x = Subtype.val ⁻¹' (s : Set ℤ).pi (fun k => {x.val k}) := by
    ext y
    simp [cylinder, Set.mem_pi]
  rw [he]
  exact (isOpen_set_pi s.finite_toSet (fun k _ => isOpen_discrete _)).preimage
    continuous_subtype_val

/-- Relative product topology first gives a finite-coordinate cylinder
on which one continuous discrete-valued output is constant. -/
theorem local_finite_control (f : History G → E) (hf : Continuous f) (x : History G) :
    ∃ s : Finset ℤ, ∀ y ∈ cylinder G s x, f y = f x := by
  have ho : IsOpen (f ⁻¹' {f x}) := (isOpen_discrete _).preimage hf
  obtain ⟨W, hW, hpre⟩ := isOpen_induced_iff.mp ho
  have hx : x.val ∈ W := by
    change x ∈ Subtype.val ⁻¹' W
    rw [hpre]
    rfl
  obtain ⟨s, U, hU, hsub⟩ := isOpen_pi_iff.mp hW x.val hx
  refine ⟨s, ?_⟩
  intro y hy
  have hyW : y.val ∈ W := hsub (by
    intro k hk
    rw [hy k hk]
    exact (hU k hk).2)
  have hyf : y ∈ f ⁻¹' {f x} := by
    rw [← hpre]
    exact hyW
  exact hyf

/-- Compactness makes the output's finite-coordinate dependence UNIFORM. -/
theorem finite_control (f : History G → E) (hf : Continuous f) :
    ∃ s : Finset ℤ, ∀ x y : History G,
      (∀ k ∈ s, x.val k = y.val k) → f x = f y := by
  classical
  choose s hs using local_finite_control G f hf
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : History G => cylinder G (s x) x)
    (fun x => cylinder_open G (s x) x)
    (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, fun _ _ => rfl⟩)
  refine ⟨t.biUnion s, ?_⟩
  intro x y hxy
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hzt, hxz⟩ := Set.mem_iUnion.mp hz
  have hyz : y ∈ cylinder G (s z) z := by
    intro k hk
    exact (hxy k (Finset.mem_biUnion.mpr ⟨z, hzt, hk⟩)).symm.trans (hxz k hk)
  exact (hs z x hxz).trans (hs z y hyz).symm

/-- This predicate records a PROVED window, not the automorphism domain. -/
def Controls (f : History G → History G) (a b : ℕ) : Prop :=
  ∀ x y k, (∀ t : ℤ, k - (a : ℤ) ≤ t → t ≤ k + (b : ℤ) → x.val t = y.val t) →
    (f x).val k = (f y).val k

/-- Curtis-Hedlund locality for every member of the FULL subgroup. -/
theorem fullAut_has_window (h : FullAut G) : ∃ a b : ℕ, Controls G h.val a b := by
  have hc : Continuous (fun x : History G => (h.val x).val 0) :=
    (continuous_apply 0).comp (continuous_subtype_val.comp h.val.continuous)
  obtain ⟨s, hs⟩ := finite_control G (fun x => (h.val x).val 0) hc
  let a := s.sup (fun k => (-k).toNat)
  let b := s.sup Int.toNat
  refine ⟨a, b, ?_⟩
  intro x y k hxy
  have he := hs (translate G k x) (translate G k y) (by
    intro t ht
    have ha : (-t).toNat ≤ a := Finset.le_sup (f := fun k => (-k).toNat) ht
    have hb : t.toNat ≤ b := Finset.le_sup (f := Int.toNat) ht
    change x.val (t + k) = y.val (t + k)
    exact hxy _ (by omega) (by omega))
  rw [commute_translate G h, commute_translate G h] at he
  simpa only [translate, zero_add] using he

/-- Forward AND actual inverse windows come from the same compact history space. -/
theorem fullAut_has_two_windows (h : FullAut G) :
    ∃ a b c d : ℕ, Controls G h.val a b ∧ Controls G h.val.symm c d := by
  obtain ⟨a, b, hab⟩ := fullAut_has_window G h
  obtain ⟨c, d, hcd⟩ := fullAut_has_window G h⁻¹
  exact ⟨a, b, c, d, hab, hcd⟩

/-- In particular the far past in the image is fixed through n-b. -/
theorem image_ray_outer (h : FullAut G) {a b : ℕ} (hab : Controls G h.val a b)
    (alpha : History G) (n : ℤ) :
    h.val '' ray G alpha n ⊆ ray G (h.val alpha) (n - (b : ℤ)) := by
  rintro y ⟨x, hx, rfl⟩ k hk
  exact hab x alpha k (fun t _ htk => hx t (by omega))

/-- Every image point carries its WHOLE (n+d)-ray, with arbitrary future. -/
theorem image_ray_saturated (h : FullAut G) {c d : ℕ}
    (hcd : Controls G h.val.symm c d) (alpha : History G) (n : ℤ)
    (y : History G) (hy : y ∈ h.val '' ray G alpha n) :
    ray G y (n + (d : ℤ)) ⊆ h.val '' ray G alpha n := by
  obtain ⟨x, hx, hxy⟩ := hy
  intro z hz
  refine ⟨h.val.symm z, ?_, h.val.apply_symm_apply z⟩
  intro k hk
  have he := hcd z y k (fun t _ htk => hz t (by omega))
  have hback : h.val.symm y = x := by rw [← hxy]; exact h.val.symm_apply_apply x
  rw [hback] at he
  exact he.trans (hx k hk)

section ImageBeams
variable (hG : Essential G)
include hG

/-- Images are beams as a THEOREM, for every commuting homeomorphism. -/
theorem image_ray_atCut (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha : History G) (n : ℤ) :
    AtCut G (h.val '' ray G alpha n) (n + (d : ℤ)) := by
  have hout := image_ray_outer G h hab alpha n
  have ho := ray_atCut_later G hG (h.val alpha)
    (show n - (b : ℤ) ≤ n + (d : ℤ) by omega)
  letI : Finite (Parts G (ray G (h.val alpha) (n - (b : ℤ))) (n + (d : ℤ))) := ho.1
  let incl : Parts G (h.val '' ray G alpha n) (n + (d : ℤ)) →
      Parts G (ray G (h.val alpha) (n - (b : ℤ))) (n + (d : ℤ)) := fun P =>
    ⟨P.val, P.property.trans hout⟩
  haveI : Finite (Parts G (h.val '' ray G alpha n) (n + (d : ℤ))) :=
    Finite.of_injective incl
      (fun P Q he => Subtype.ext (congrArg
        (fun R : Parts G (ray G (h.val alpha) (n - (b : ℤ))) (n + (d : ℤ)) => R.val)
        he))
  exact ⟨inferInstance, image_ray_saturated G h hcd alpha n⟩

/-- Explicit finite whole-ray bound Delta^(b+d). -/
theorem image_ray_parts_bound (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha : History G) (n : ℤ) :
    Nat.card (Parts G (h.val '' ray G alpha n) (n + (d : ℤ))) ≤ Delta G ^ (b + d) := by
  let m := n + (d : ℤ)
  let s := n - (b : ℤ)
  have him := image_ray_atCut G hG h hab hcd alpha n
  have ho := ray_atCut_later G hG (h.val alpha) (show s ≤ m by dsimp [s, m]; omega)
  letI : Finite (Parts G (h.val '' ray G alpha n) m) := him.1
  letI : Finite (Parts G (ray G (h.val alpha) s) m) := ho.1
  letI : Fintype (Parts G (h.val '' ray G alpha n) m) := Fintype.ofFinite _
  letI : Fintype (Parts G (ray G (h.val alpha) s) m) := Fintype.ofFinite _
  have hout := image_ray_outer G h hab alpha n
  let incl : Parts G (h.val '' ray G alpha n) m →
      Parts G (ray G (h.val alpha) s) m := fun P => ⟨P.val, P.property.trans hout⟩
  have hle := Fintype.card_le_of_injective incl
    (fun P Q he => Subtype.ext (congrArg
      (fun R : Parts G (ray G (h.val alpha) s) m => R.val) he))
  have he : s + ((b + d : ℕ) : ℤ) = m := by dsimp [s, m]; omega
  have e := rayPartsEquiv G hG (h.val alpha) s (b + d)
  rw [he] at e
  have hc := Fintype.card_congr e
  calc
    _ = Fintype.card (Parts G (h.val '' ray G alpha n) m) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Parts G (ray G (h.val alpha) s) m) := hle
    _ = Fintype.card (Continuation G (endpoint G (h.val alpha) s) (b + d)) := hc.symm
    _ ≤ _ := continuation_card_bound G _ _

/-- Actual image of an arbitrary finite beam. -/
theorem image_isBeam (h : FullAut G) (U : Beam G) : IsBeam G (h.val '' U.val) := by
  obtain ⟨n, hn⟩ := U.property
  obtain ⟨a, b, c, d, hab, hcd⟩ := fullAut_has_two_windows G h
  letI : Finite (Parts G U.val n) := hn.1
  have hpart (P : Parts G U.val n) :
      AtCut G (h.val '' P.val.val) (n + (d : ℤ)) := by
    rw [RayAt.set_eq G P.val]
    exact image_ray_atCut G hG h hab hcd _ n
  have he : h.val '' U.val = ⋃ P : Parts G U.val n, h.val '' P.val.val := by
    calc
      h.val '' U.val = h.val '' (⋃ P : Parts G U.val n, P.val.val) :=
        congrArg (fun S : Set (History G) => h.val '' S) (parts_union G hn)
      _ = _ := Set.image_iUnion
  exact ⟨n + (d : ℤ), he ▸ atCut_iUnion G _ _ hpart⟩

def imageBeam (h : FullAut G) (U : Beam G) : Beam G :=
  ⟨h.val '' U.val, image_isBeam G hG h U⟩

/-- These identities concern actual sets, so they also retain every copy
when applied pointwise to a tagged finite family. -/
@[simp] theorem imageBeam_one (U : Beam G) : imageBeam G hG 1 U = U := by
  apply Subtype.ext
  exact Set.image_id _

theorem imageBeam_mul (g h : FullAut G) (U : Beam G) :
    imageBeam G hG (g * h) U = imageBeam G hG g (imageBeam G hG h U) := by
  apply Subtype.ext
  change (fun x => g.val (h.val x)) '' U.val = g.val '' (h.val '' U.val)
  exact (Set.image_image g.val h.val U.val).symm

end ImageBeams

/-- Restrict an actual bijection to its actual image set. -/
def imageRestriction (h : History G ≃ₜ History G) (U : Set (History G)) : U ≃ (h '' U) where
  toFun x := ⟨h x.val, x.val, x.property, rfl⟩
  invFun y := ⟨h.symm y.val, by
    obtain ⟨x, hx, he⟩ := y.property
    simpa only [← he, h.symm_apply_apply] using hx⟩
  left_inv x := Subtype.ext (h.symm_apply_apply x.val)
  right_inv y := Subtype.ext (h.apply_symm_apply y.val)

/-- h p h^{-1} on the two ACTUAL image subsets. -/
def conjugateSplice (h : FullAut G) (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) :
    (h.val '' ray G alpha n) ≃ (h.val '' ray G beta n) :=
  (imageRestriction G h.val (ray G alpha n)).symm.trans
    ((spliceEquiv G alpha beta n ep).trans (imageRestriction G h.val (ray G beta n)))

/-- This is the key future assertion for the conjugate of a parallel splice. -/
theorem conjugateSplice_future (h : FullAut G) {a b : ℕ} (hab : Controls G h.val a b)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (y : h.val '' ray G alpha n) (k : ℤ) (hk : n + (a : ℤ) < k) :
    (conjugateSplice G h alpha beta n ep y).val.val k = y.val.val k := by
  let x := (imageRestriction G h.val (ray G alpha n)).symm y
  have hf := hab (splice G alpha beta n ep x) x.val k (by
    intro t hkt _
    exact splice_future G alpha beta n ep x t (by omega))
  change (h.val (splice G alpha beta n ep x)).val k = y.val.val k
  exact hf.trans (congrArg (fun z : History G => z.val k)
    (h.val.apply_symm_apply y.val))

/-- At ell=n+a+b+d, the conjugate sends all points with the same past
through ell to points with the same past through ell. -/
theorem conjugateSplice_past (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (y z : h.val '' ray G alpha n)
    (hyz : z.val ∈ ray G y.val (n + (a : ℤ) + (b : ℤ) + (d : ℤ))) :
    (conjugateSplice G h alpha beta n ep z).val ∈
      ray G (conjugateSplice G h alpha beta n ep y).val
        (n + (a : ℤ) + (b : ℤ) + (d : ℤ)) := by
  let x := (imageRestriction G h.val (ray G alpha n)).symm y
  let w := (imageRestriction G h.val (ray G alpha n)).symm z
  have hback : ∀ k : ℤ, k ≤ n + (a : ℤ) + (b : ℤ) → w.val.val k = x.val.val k := by
    intro k hk
    exact hcd z.val y.val k (fun t _ htk => hyz t (by omega))
  have hsplice : ∀ k : ℤ, k ≤ n + (a : ℤ) + (b : ℤ) →
      (splice G alpha beta n ep w).val k = (splice G alpha beta n ep x).val k := by
    intro k hk
    by_cases hkn : k ≤ n
    · simp [splice, hkn]
    · simpa only [splice, if_neg hkn] using hback k hk
  intro k hk
  by_cases hk0 : k ≤ n + (a : ℤ)
  · exact hab (splice G alpha beta n ep w) (splice G alpha beta n ep x) k
      (fun t _ htk => hsplice t (by omega))
  · rw [conjugateSplice_future G h hab alpha beta n ep z k (by omega),
      conjugateSplice_future G h hab alpha beta n ep y k (by omega)]
    exact hyz k hk

/-- Cut endpoints agree because the actual next edge agrees, not because
endpoint preservation was added as a hypothesis on h. -/
theorem conjugateSplice_endpoint (h : FullAut G) {a b : ℕ} (hab : Controls G h.val a b)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (y : h.val '' ray G alpha n) {ell : ℤ} (hell : n + (a : ℤ) ≤ ell) :
    endpoint G (conjugateSplice G h alpha beta n ep y).val ell = endpoint G y.val ell := by
  have he := conjugateSplice_future G h hab alpha beta n ep y (ell + 1) (by omega)
  exact ((conjugateSplice G h alpha beta n ep y).val.property ell).trans
    ((congrArg G.source he).trans (y.val.property ell).symm)

/-- The conjugate's restriction to one intrinsic ell-ray is PRECISELY the
future-preserving past splice between its two actual representative histories. -/
theorem conjugateSplice_on_ray (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (y z : h.val '' ray G alpha n)
    (hyz : z.val ∈ ray G y.val (n + (a : ℤ) + (b : ℤ) + (d : ℤ))) :
    (conjugateSplice G h alpha beta n ep z).val =
      splice G y.val (conjugateSplice G h alpha beta n ep y).val
        (n + (a : ℤ) + (b : ℤ) + (d : ℤ))
        (conjugateSplice_endpoint G h hab alpha beta n ep y (by omega)).symm
        ⟨z.val, hyz⟩ := by
  apply Subtype.ext
  funext k
  by_cases hk : k ≤ n + (a : ℤ) + (b : ℤ) + (d : ℤ)
  · simpa only [splice, if_pos hk] using
      conjugateSplice_past G h hab hcd alpha beta n ep y z hyz k hk
  · simpa only [splice, if_neg hk] using
      conjugateSplice_future G h hab alpha beta n ep z k (by omega)

@[simp] theorem conjugateSplice_symm (h : FullAut G) (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) :
    (conjugateSplice G h alpha beta n ep).symm =
      conjugateSplice G h beta alpha n ep.symm := rfl

/-- The image is the WHOLE target intrinsic ray, not merely a subset. -/
theorem conjugateSplice_rayImage (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (y : h.val '' ray G alpha n) :
    conjugateSplice G h alpha beta n ep ''
        {z | z.val ∈ ray G y.val (n + (a : ℤ) + (b : ℤ) + (d : ℤ))} =
      {z | z.val ∈ ray G (conjugateSplice G h alpha beta n ep y).val
        (n + (a : ℤ) + (b : ℤ) + (d : ℤ))} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact conjugateSplice_past G h hab hcd alpha beta n ep y w hw
  · intro hz
    let e := conjugateSplice G h alpha beta n ep
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    have he := conjugateSplice_past G h hab hcd beta alpha n ep.symm (e y) z hz
    change (e.symm z).val ∈
      ray G (e.symm (e y)).val (n + (a : ℤ) + (b : ℤ) + (d : ℤ)) at he
    change (e.symm z).val ∈ ray G y.val (n + (a : ℤ) + (b : ℤ) + (d : ℤ))
    simpa only [Equiv.symm_apply_apply] using he

/-- Actual endpoint-preserving bijection of the two intrinsic ray partitions.
Each restriction is the actual past splice proved by conjugateSplice_on_ray. -/
def conjugatePartsEquiv (hG : Essential G) (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n) :
    Parts G (h.val '' ray G alpha n) (n + (a : ℤ) + (b : ℤ) + (d : ℤ)) ≃
      Parts G (h.val '' ray G beta n) (n + (a : ℤ) + (b : ℤ) + (d : ℤ)) := by
  let ell := n + (a : ℤ) + (b : ℤ) + (d : ℤ)
  let A := h.val '' ray G alpha n
  let B := h.val '' ray G beta n
  let e := conjugateSplice G h alpha beta n ep
  have hA : AtCut G A ell := atCut_mono G hG (image_ray_atCut G hG h hab hcd alpha n) (by
    dsimp [ell]; omega)
  have hB : AtCut G B ell := atCut_mono G hG (image_ray_atCut G hG h hab hcd beta n) (by
    dsimp [ell]; omega)
  let rep : (P : Parts G A ell) → A := fun P =>
    ⟨RayAt.representative G P.val, P.property (by
      rw [RayAt.set_eq G P.val]; exact self_mem_ray G _ _)⟩
  let f : Parts G A ell → Parts G B ell := fun P =>
    ⟨rayAt G (e (rep P)).val ell, hB.2 _ (e (rep P)).property⟩
  apply Equiv.ofBijective f
  constructor
  · intro P Q he
    have hsource (R : Parts G A ell) : (rep R).val ∈ R.val.val := by
      rw [RayAt.set_eq G R.val]; exact self_mem_ray G _ _
    have htarget : (e (rep Q)).val ∈ ray G (e (rep P)).val ell := by
      have hs := congrArg (fun R => R.val.val) he
      change ray G (e (rep P)).val ell = ray G (e (rep Q)).val ell at hs
      rw [hs]
      exact self_mem_ray G _ _
    have hinverse := conjugateSplice_past G h hab hcd beta alpha n ep.symm
      (e (rep P)) (e (rep Q)) htarget
    change (e.symm (e (rep Q))).val ∈ ray G (e.symm (e (rep P))).val ell at hinverse
    have hpast : (rep Q).val ∈ ray G (rep P).val ell := by
      simpa only [Equiv.symm_apply_apply] using hinverse
    apply Subtype.ext
    exact RayAt.eq_of_inter G _ _ (rep Q).val
      (by rw [RayAt.set_eq G P.val]; exact hpast) (hsource Q)
  · intro Q
    let z : B := ⟨RayAt.representative G Q.val, Q.property (by
      rw [RayAt.set_eq G Q.val]; exact self_mem_ray G _ _)⟩
    let y := e.symm z
    let P : Parts G A ell := ⟨rayAt G y.val ell, hA.2 _ y.property⟩
    have hrep : (rep P).val ∈ ray G y.val ell := by
      change RayAt.representative G P.val ∈ P.val.val
      rw [RayAt.set_eq G P.val]
      exact self_mem_ray G _ _
    have hpast : (e (rep P)).val ∈ ray G (e y).val ell := by
      have hwhole := conjugateSplice_rayImage G h hab hcd alpha beta n ep y
      have hmem : e (rep P) ∈ e '' {z | z.val ∈ ray G y.val ell} :=
        ⟨rep P, hrep, rfl⟩
      rw [hwhole] at hmem
      exact hmem
    have hpast' : (e (rep P)).val ∈ Q.val.val := by
      rw [RayAt.set_eq G Q.val]
      change (e (rep P)).val ∈ ray G z.val ell
      change (e (rep P)).val ∈ ray G (e (e.symm z)).val ell at hpast
      simpa only [Equiv.apply_symm_apply] using hpast
    exact ⟨P, Subtype.ext (RayAt.eq_of_inter G _ _ _ (self_mem_ray G _ _) hpast')⟩

theorem conjugatePartsEquiv_endpoint (hG : Essential G) (h : FullAut G) {a b c d : ℕ}
    (hab : Controls G h.val a b) (hcd : Controls G h.val.symm c d)
    (alpha beta : History G) (n : ℤ) (ep : endpoint G alpha n = endpoint G beta n)
    (P : Parts G (h.val '' ray G alpha n) (n + (a : ℤ) + (b : ℤ) + (d : ℤ))) :
    RayAt.endpoint G (conjugatePartsEquiv G hG h hab hcd alpha beta n ep P).val =
      RayAt.endpoint G P.val := by
  let ell := n + (a : ℤ) + (b : ℤ) + (d : ℤ)
  let y : h.val '' ray G alpha n := ⟨RayAt.representative G P.val, P.property (by
    rw [RayAt.set_eq G P.val]; exact self_mem_ray G _ _)⟩
  change RayAt.endpoint G (rayAt G (conjugateSplice G h alpha beta n ep y).val ell) = _
  rw [RayAt.endpoint_of_mem G _ _ (self_mem_ray G _ _)]
  rw [conjugateSplice_endpoint G h hab alpha beta n ep y (by dsimp [ell]; omega)]
  exact (RayAt.endpoint_of_mem G P.val y.val (by
    rw [RayAt.set_eq G P.val]; exact self_mem_ray G _ _)).symm

/-- Unit shift on actual subsets moves the cut down by ONE integer. -/
theorem shift_ray (alpha : History G) (n : ℤ) :
    shift G '' ray G alpha n = ray G (shift G alpha) (n - 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    exact hx (k + 1) (by omega)
  · intro hy
    let x : History G := ⟨fun k => y.val (k - 1), fun k => by
      simpa only [sub_add_cancel, add_sub_cancel_right] using y.property (k - 1)⟩
    refine ⟨x, ?_, ?_⟩
    · intro k hk
      simpa only [shift, sub_add_cancel] using hy (k - 1) (by omega)
    · apply Subtype.ext
      funext k
      simp [x, shift]

@[simp] theorem shift_ray_endpoint (alpha : History G) (n : ℤ) :
    endpoint G (shift G alpha) (n - 1) = endpoint G alpha n := by
  simp [endpoint, shift]

end D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
