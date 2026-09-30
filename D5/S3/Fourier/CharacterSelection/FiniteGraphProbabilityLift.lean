/- GID: D5/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/FiniteGraphProbabilityLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Component anchors classify finite graph probability lifts. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.FiniteGraphProbabilityLift

noncomputable section

open SimpleGraph
open MeasureTheory ProbabilityTheory
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

abbrev Config {V : Type*} (_G : SimpleGraph V) := V → ZMod 2

abbrev Label {V : Type*} (G : SimpleGraph V) := Set.range (edgeDifferential G)

abbrev Anchor {V : Type*} (G : SimpleGraph V) := G.ConnectedComponent → ZMod 2

noncomputable instance anchorFintype {V : Type*} (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] : Fintype (Anchor G) :=
  Fintype.ofFinite _

noncomputable def edgeLabel {V : Type*} (G : SimpleGraph V) (x : Config G) : Label G :=
  ⟨edgeDifferential G x, ⟨x, rfl⟩⟩

noncomputable def rootAnchors {V : Type*} (G : SimpleGraph V)
    (o : (K : G.ConnectedComponent) → K) (x : Config G) : Anchor G :=
  fun K => x (o K)

noncomputable def phi {V : Type*} (G : SimpleGraph V)
    (o : (K : G.ConnectedComponent) → K) : Config G → Label G × Anchor G :=
  fun x => (edgeLabel G x, rootAnchors G o x)

theorem phi_bijective
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) :
    Function.Bijective (phi G o) := by
  have H := (finite_graph_cycle_space G).1.2.2.2
  have fiber_bijective (y : G.edgeSet → ZMod 2) (hy : ∃ x, edgeDifferential G x = y) :
      Function.Bijective (fun x : {x // edgeDifferential G x = y} =>
        fun K => x.val (o K)) := (H y).2 hy |>.2 o
  constructor
  · intro x x' h
    have hlabel : edgeDifferential G x = edgeDifferential G x' := by
      exact congrArg Subtype.val (congrArg Prod.fst h)
    have hanchor : (fun K => x (o K)) = (fun K => x' (o K)) :=
      congrArg Prod.snd h
    have hf := fiber_bijective (edgeDifferential G x) ⟨x, rfl⟩
    have hs : (⟨x, rfl⟩ : {z // edgeDifferential G z = edgeDifferential G x}) =
        (⟨x', hlabel.symm⟩ : {z // edgeDifferential G z = edgeDifferential G x}) := by
      exact hf.1 hanchor
    exact congrArg Subtype.val hs
  · rintro ⟨y, a⟩
    obtain ⟨x, hxa⟩ := (fiber_bijective y.1 y.2).2 a
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact x.2
    · exact hxa

noncomputable def phiEquiv {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) :
    Config G ≃ Label G × Anchor G :=
  Equiv.ofBijective (phi G o) (phi_bijective G o)

/-- Flipping one bit on each connected component. -/
def componentFlip {V : Type*} (G : SimpleGraph V) (g : Anchor G) (x : Config G) : Config G :=
  fun v => x v + g (G.connectedComponentMk v)

theorem componentFlip_edgeLabel
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (g : Anchor G) (x : Config G) :
    edgeLabel G (componentFlip G g x) = edgeLabel G x := by
  apply Subtype.ext
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp he
      have hcomp : G.connectedComponentMk a = G.connectedComponentMk b :=
        ConnectedComponent.connectedComponentMk_eq_of_adj hab
      change (x a + g (G.connectedComponentMk a)) +
          (x b + g (G.connectedComponentMk b)) = x a + x b
      rw [hcomp]
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide]

theorem componentFlip_rootAnchors
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (g : Anchor G) (x : Config G) :
    rootAnchors G o (componentFlip G g x) = rootAnchors G o x + g := by
  funext K
  change x (o K) + g (G.connectedComponentMk (o K)) = x (o K) + g K
  rw [(o K).property]

abbrev LiftLaw {V : Type*} (G : SimpleGraph V) := PMF (Config G)

abbrev ConditionalFamily {V : Type*} (G : SimpleGraph V) (ν : PMF (Label G)) :=
  ∀ y : ν.support, PMF (Anchor G)

noncomputable def conditionalAt
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (ν : PMF (Label G)) (q : ConditionalFamily G ν) (y : Label G) : PMF (Anchor G) := by
  classical
  exact if hy : y ∈ ν.support then q ⟨y, hy⟩ else PMF.pure 0

noncomputable def liftFrom
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [Fintype (Anchor G)]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (q : ConditionalFamily G ν) : LiftLaw G :=
  PMF.map (phiEquiv G o).symm
    (ν.bind (fun y => PMF.map (fun a => (y, a)) (conditionalAt G ν q y)))

theorem liftFrom_marginal
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (q : ConditionalFamily G ν) :
    PMF.map (edgeLabel G) (liftFrom G o ν q) = ν := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  have hfst : edgeLabel G ∘ (phiEquiv G o).symm = Prod.fst := by
    funext z
    exact congrArg Prod.fst ((phiEquiv G o).apply_symm_apply z)
  rw [liftFrom, PMF.map_comp, hfst, PMF.map_bind]
  have hmap (y : Label G) :
      PMF.map Prod.fst (PMF.map (fun a : Anchor G => (y, a))
        (conditionalAt G ν q y)) = PMF.pure y := by
    rw [PMF.map_comp]
    convert PMF.map_const (p := conditionalAt G ν q y) (b := y) using 1 <;> rfl
  simp_rw [hmap]
  exact PMF.bind_pure ν

private theorem joint_fiber_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (j : PMF (A × B)) (ν : PMF A) (h : PMF.map Prod.fst j = ν) (a : A) :
    (∑ b, j (a, b)) = ν a := by
  classical
  have ha := congrArg (fun p : PMF A => p a) h
  rw [PMF.map_apply,
    tsum_eq_sum (s := Finset.univ) (fun b hb => (hb (Finset.mem_univ b)).elim)] at ha
  change (∑ p : A × B, if a = p.1 then j p else 0) = ν a at ha
  rw [Fintype.sum_prod_type] at ha
  have houter :
      (∑ a' : A, ∑ b : B, if a = a' then j (a', b) else 0) = ∑ b : B, j (a, b) := by
    simp [eq_comm]
  exact houter ▸ ha

private noncomputable def conditionalOf
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : LiftLaw G) (hμ : PMF.map (edgeLabel G) μ = ν) (y : ν.support) : PMF (Anchor G) := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  apply PMF.ofFintype (fun a => (PMF.map (phiEquiv G o) μ) (y.1, a) / ν y)
  calc
    (∑ a, (PMF.map (phiEquiv G o) μ) (y.1, a) / ν y) =
        (∑ a, (PMF.map (phiEquiv G o) μ) (y.1, a)) / ν y := by
      calc
        _ = ∑ a, (ν y)⁻¹ * (PMF.map (phiEquiv G o) μ) (y.1, a) := by
          simp_rw [ENNReal.div_eq_inv_mul]
        _ = (ν y)⁻¹ * ∑ a, (PMF.map (phiEquiv G o) μ) (y.1, a) := by
          rw [Finset.mul_sum]
        _ = (∑ a, (PMF.map (phiEquiv G o) μ) (y.1, a)) / ν y := by
          rw [ENNReal.div_eq_inv_mul]
    _ = ν y / ν y := by
      rw [joint_fiber_sum (PMF.map (phiEquiv G o) μ) ν]
      rw [PMF.map_comp]
      exact hμ
    _ = 1 := ENNReal.div_self y.2 (ν.apply_ne_top y)

private noncomputable def extracted
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : {μ : LiftLaw G // PMF.map (edgeLabel G) μ = ν}) :
    ConditionalFamily G ν :=
  fun y => conditionalOf G o ν μ.1 μ.2 y

private theorem map_pair_apply
    {A B : Type*} [Fintype B] [DecidableEq A] (p : PMF B) (a : A) (a' : A) (b : B) :
    PMF.map (fun z : B => (a, z)) p (a', b) = if a' = a then p b else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases haa : a' = a
  · subst a'
    simp only [Prod.mk.injEq, true_and, if_true]
    rw [tsum_eq_sum (s := Finset.univ) (fun z hz => (hz (Finset.mem_univ z)).elim)]
    simp
  · simp [haa]

private theorem bind_pair_apply
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (p : PMF A) (q : A → PMF B) (a : A) (b : B) :
    p.bind (fun x => PMF.map (fun z : B => (x, z)) (q x)) (a, b) = p a * q a b := by
  classical
  rw [PMF.bind_apply]
  rw [tsum_eq_sum (s := Finset.univ) (fun x hx => (hx (Finset.mem_univ x)).elim)]
  simp_rw [map_pair_apply]
  simp [eq_comm]

private theorem joint_zero_of_not_support
    {A B : Type*} [Fintype A] [Fintype B]
    (j : PMF (A × B)) (ν : PMF A) (h : PMF.map Prod.fst j = ν)
    {a : A} (ha : a ∉ ν.support) (b : B) : j (a, b) = 0 := by
  have hsum : (∑ b' : B, j (a, b')) = 0 := by
    rw [joint_fiber_sum j ν h, (ν.apply_eq_zero_iff a).2 ha]
  have hle : j (a, b) ≤ ∑ b' : B, j (a, b') := by
    exact Finset.single_le_sum (s := Finset.univ) (f := fun b' : B => j (a, b'))
      (fun _ _ => bot_le) (Finset.mem_univ b)
  exact le_antisymm (hsum ▸ hle) (show 0 ≤ j (a, b) from bot_le)

private theorem joint_mass_of_lift
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (q : ConditionalFamily G ν) (y : Label G) (a : Anchor G) :
    (PMF.map (phiEquiv G o) (liftFrom G o ν q)) (y, a) =
      ν y * (PMF.map (fun b : Anchor G => (y, b)) (conditionalAt G ν q y)) (y, a) := by
  classical
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  rw [liftFrom, PMF.map_comp]
  rw [Equiv.self_comp_symm, PMF.map_id]
  rw [bind_pair_apply]
  rw [map_pair_apply]
  simp

private theorem joint_mass_of_extracted
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : {μ : LiftLaw G // PMF.map (edgeLabel G) μ = ν})
    (y : ν.support) (a : Anchor G) :
    (PMF.map (phiEquiv G o) μ.1) (y.1, a) =
      ν y * extracted G o ν μ y a := by
  classical
  change (PMF.map (phiEquiv G o) μ.1) (y.1, a) =
    ν y * conditionalOf G o ν μ.1 μ.2 y a
  simp only [conditionalOf, PMF.ofFintype_apply]
  exact (ENNReal.mul_div_cancel y.2 (ν.apply_ne_top y)).symm

private theorem joint_mass_of_extracted_off_support
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : {μ : LiftLaw G // PMF.map (edgeLabel G) μ = ν})
    {y : Label G} (hy : y ∉ ν.support) (a : Anchor G) :
    (PMF.map (phiEquiv G o) μ.1) (y, a) = 0 := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  apply joint_zero_of_not_support (PMF.map (phiEquiv G o) μ.1) ν ?_ hy a
  rw [PMF.map_comp]
  exact μ.2

private theorem map_equiv_apply
    {A B : Type*} [Fintype A] (e : A ≃ B) (p : PMF A) (b : B) :
    PMF.map e p b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := Finset.univ) (fun a ha => (ha (Finset.mem_univ a)).elim)]
  have heq : ∀ a : A, (b = e a) = (a = e.symm b) := by
    intro a
    apply propext
    constructor
    · intro h
      calc
        a = e.symm (e a) := (e.symm_apply_apply a).symm
        _ = e.symm b := congrArg e.symm h.symm
    · intro h
      calc
        b = e (e.symm b) := (e.apply_symm_apply b).symm
        _ = e a := congrArg e h.symm
  simp_rw [heq]
  simp

abbrev LiftSpace {V : Type*} (G : SimpleGraph V) (ν : PMF (Label G)) :=
  {μ : LiftLaw G // PMF.map (edgeLabel G) μ = ν}

noncomputable def phi_probability_lift_classification
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G)) :
    LiftSpace G ν ≃ ConditionalFamily G ν :=
  { toFun := extracted G o ν
    invFun := fun q => ⟨liftFrom G o ν q, liftFrom_marginal G o ν q⟩
    left_inv := by
      intro μ
      letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
      apply Subtype.ext
      have hinv : Function.LeftInverse
          (PMF.map (phiEquiv G o).symm) (PMF.map (phiEquiv G o)) := by
        intro p
        simp only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
      apply hinv.injective
      apply PMF.ext
      rintro ⟨y, a⟩
      by_cases hy : y ∈ ν.support
      · calc
          (PMF.map (phiEquiv G o) (liftFrom G o ν (extracted G o ν μ))) (y, a) =
              ν y * (PMF.map (fun b : Anchor G => (y, b))
                (conditionalAt G ν (extracted G o ν μ) y)) (y, a) :=
            joint_mass_of_lift G o ν (extracted G o ν μ) y a
          _ = ν y * (extracted G o ν μ ⟨y, hy⟩ a) := by
            rw [map_pair_apply]
            simp [conditionalAt, hy]
          _ = (PMF.map (phiEquiv G o) μ.1) (y, a) :=
            (joint_mass_of_extracted G o ν μ ⟨y, hy⟩ a).symm
      · calc
          (PMF.map (phiEquiv G o) (liftFrom G o ν (extracted G o ν μ))) (y, a) =
              ν y * (PMF.map (fun b : Anchor G => (y, b))
                (conditionalAt G ν (extracted G o ν μ) y)) (y, a) :=
            joint_mass_of_lift G o ν (extracted G o ν μ) y a
          _ = 0 := by
            rw [map_pair_apply]
            simp [conditionalAt, hy, (ν.apply_eq_zero_iff y).2 hy]
          _ = (PMF.map (phiEquiv G o) μ.1) (y, a) :=
            (joint_mass_of_extracted_off_support G o ν μ hy a).symm
    right_inv := by
      intro q
      letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
      funext y
      apply PMF.ext
      intro a
      let μ : LiftSpace G ν := ⟨liftFrom G o ν q, liftFrom_marginal G o ν q⟩
      have hj := joint_mass_of_lift G o ν q y.1 a
      change conditionalOf G o ν μ.1 μ.2 y a = q y a
      simp only [conditionalOf, PMF.ofFintype_apply]
      rw [hj, map_pair_apply]
      simp only [conditionalAt, dif_pos y.2]
      rw [ENNReal.div_eq_inv_mul]
      exact ENNReal.inv_mul_cancel_left y.2 (ν.apply_ne_top y) }

noncomputable def flipEquiv
    {V : Type*} (G : SimpleGraph V) (g : Anchor G) : Config G ≃ Config G :=
  { toFun := componentFlip G g
    invFun := componentFlip G g
    left_inv := by
      intro x
      funext v
      dsimp [componentFlip]
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide]
    right_inv := by
      intro x
      funext v
      dsimp [componentFlip]
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide] }

def flipPair
    {V : Type*} (G : SimpleGraph V) (g : Anchor G) (z : Label G × Anchor G) :
    Label G × Anchor G :=
  (z.1, z.2 + g)

noncomputable def flipPairEquiv
    {V : Type*} (G : SimpleGraph V) (g : Anchor G) :
    (Label G × Anchor G) ≃ (Label G × Anchor G) :=
  { toFun := flipPair G g
    invFun := flipPair G g
    left_inv := by
      rintro ⟨y, a⟩
      apply Prod.ext
      · rfl
      · funext K
        dsimp [flipPair]
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide]
    right_inv := by
      rintro ⟨y, a⟩
      apply Prod.ext
      · rfl
      · funext K
        dsimp [flipPair]
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide] }

abbrev FlipInvariant {V : Type*} (G : SimpleGraph V) (μ : LiftLaw G) :=
  ∀ g : Anchor G, PMF.map (flipEquiv G g) μ = μ

noncomputable def uniformLift
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [Fintype (Anchor G)]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G)) : LiftSpace G ν := by
  exact ⟨liftFrom G o ν (fun _ => PMF.uniformOfFintype (Anchor G)),
    liftFrom_marginal G o ν (fun _ => PMF.uniformOfFintype (Anchor G))⟩

theorem probability_lift_point_masses
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : LiftSpace G ν) :
    (∀ (y : ν.support) (a : Anchor G),
      μ.1 ((phiEquiv G o).symm (y.1, a)) =
        ν y * (phi_probability_lift_classification G o ν μ) y a) ∧
    (∀ {y : Label G}, y ∉ ν.support → ∀ a : Anchor G,
      μ.1 ((phiEquiv G o).symm (y, a)) = 0) := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  constructor
  · intro y a
    have h := joint_mass_of_extracted G o ν μ y a
    rw [map_equiv_apply] at h
    exact h
  · intro y hy a
    have h := joint_mass_of_extracted_off_support G o ν μ hy a
    rw [map_equiv_apply] at h
    exact h

private noncomputable def addTranslateEquiv
    {A : Type*} [AddCommGroup A] (g : A) : A ≃ A :=
  { toFun := fun a => a + g
    invFun := fun a => a - g
    left_inv := by intro a; simp
    right_inv := by intro a; simp }

private theorem pmf_translation_invariant_uniform
    {A : Type*} [Fintype A] [AddCommGroup A]
    (p : PMF A) (h : ∀ g : A, PMF.map (addTranslateEquiv g) p = p) :
    p = PMF.uniformOfFintype A := by
  apply PMF.ext
  intro a
  have hmass (b : A) : p b = p 0 := by
    have hb := congrArg (fun r : PMF A => r b) (h b)
    rw [map_equiv_apply] at hb
    simpa [addTranslateEquiv] using hb.symm
  rw [PMF.uniformOfFintype_apply]
  have hsum := p.tsum_coe
  rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)] at hsum
  simp_rw [hmass] at hsum
  rw [Finset.sum_const, Finset.card_univ] at hsum
  have hcard : (Fintype.card A : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hcardtop : (Fintype.card A : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.natCast_ne_top _
  have hsum' : (Fintype.card A : ENNReal) * p 0 = 1 := by
    simpa [nsmul_eq_mul] using hsum
  calc
    p a = p 0 := hmass a
    _ = p 0 * 1 := by rw [mul_one]
    _ = p 0 * ((Fintype.card A : ENNReal) * (Fintype.card A : ENNReal)⁻¹) := by
      rw [ENNReal.mul_inv_cancel hcard hcardtop]
    _ = ((Fintype.card A : ENNReal) * p 0) * (Fintype.card A : ENNReal)⁻¹ := by
      ac_rfl
    _ = 1 * (Fintype.card A : ENNReal)⁻¹ := by rw [hsum']
    _ = (Fintype.card A : ENNReal)⁻¹ := by rw [one_mul]

theorem flip_invariant_positive_fiber_uniform
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : LiftSpace G ν) (hμ : FlipInvariant G μ.1) (y : ν.support) :
    (phi_probability_lift_classification G o ν μ) y =
      PMF.uniformOfFintype (Anchor G) := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  apply pmf_translation_invariant_uniform
  intro g
  apply PMF.ext
  intro a
  have hcommute :
      (phiEquiv G o) ∘ (flipEquiv G g) =
        (flipPairEquiv G g) ∘ (phiEquiv G o) := by
    funext x
    apply Prod.ext
    · exact componentFlip_edgeLabel G g x
    · exact componentFlip_rootAnchors G o g x
  have hpair : PMF.map (flipPairEquiv G g) (PMF.map (phiEquiv G o) μ.1) =
      PMF.map (phiEquiv G o) μ.1 := by
    rw [PMF.map_comp, ← hcommute, ← PMF.map_comp, hμ g]
  have he := congrArg (fun p : PMF (Label G × Anchor G) => p (y.1, a)) hpair
  rw [map_equiv_apply] at he
  have hsymm : (flipPairEquiv G g).symm (y.1, a) = (y.1, a - g) := by
    apply Prod.ext
    · rfl
    · dsimp [flipPairEquiv, flipPair]
      ring_nf
      have hg : -g = g := by
        funext K
        change -(g K) = g K
        exact CharTwo.neg_eq (g K)
      rw [sub_eq_add_neg, hg]
  rw [hsymm] at he
  have hj :
      (PMF.map (phiEquiv G o) μ.1) (y.1, a - g) =
        (PMF.map (phiEquiv G o) μ.1) (y.1, a) := by
    exact he
  have hleft := joint_mass_of_extracted G o ν μ y (a - g)
  have hright := joint_mass_of_extracted G o ν μ y a
  have hq' :
      ν y.1 * (extracted G o ν μ y) (a - g) =
        ν y.1 * (extracted G o ν μ y) a := by
    rw [← hleft, ← hright]
    exact hj
  have hq :
      ν y.1 * (phi_probability_lift_classification G o ν μ y) (a - g) =
        ν y.1 * (phi_probability_lift_classification G o ν μ y) a := by
    simpa [phi_probability_lift_classification] using hq'
  have hν0 : ν y.1 ≠ 0 := by
    intro hzero
    exact (ν.apply_eq_zero_iff y.1).1 hzero y.2
  have hνtop : ν y.1 ≠ (⊤ : ENNReal) := ν.apply_ne_top y
  rw [map_equiv_apply]
  simpa [addTranslateEquiv] using
    (show (phi_probability_lift_classification G o ν μ y) (a - g) =
      (phi_probability_lift_classification G o ν μ y) a by
      calc
        _ = (ν y.1)⁻¹ * (ν y.1 *
            (phi_probability_lift_classification G o ν μ y) (a - g)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hν0 hνtop, one_mul]
        _ = (ν y.1)⁻¹ * (ν y.1 *
            (phi_probability_lift_classification G o ν μ y) a) := by rw [hq]
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hν0 hνtop, one_mul])

theorem uniform_lift_flip_invariant
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G)) :
    FlipInvariant G (uniformLift G o ν).1 := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  have hmass (y : Label G) (a : Anchor G) :
      (PMF.map (phiEquiv G o) (uniformLift G o ν).1) (y, a) =
        ν y * PMF.uniformOfFintype (Anchor G) a := by
    change (PMF.map (phiEquiv G o)
      (liftFrom G o ν (fun _ => PMF.uniformOfFintype (Anchor G)))) (y, a) = _
    rw [liftFrom, PMF.map_comp, Equiv.self_comp_symm, PMF.map_id, bind_pair_apply]
    by_cases hy : y ∈ ν.support
    · simp [conditionalAt, hy]
    · simp [conditionalAt, hy, (ν.apply_eq_zero_iff y).2 hy]
  intro g
  have hcommute :
      (phiEquiv G o) ∘ (flipEquiv G g) =
        (flipPairEquiv G g) ∘ (phiEquiv G o) := by
    funext x
    apply Prod.ext
    · exact componentFlip_edgeLabel G g x
    · exact componentFlip_rootAnchors G o g x
  have hinv : Function.LeftInverse
      (PMF.map (phiEquiv G o).symm) (PMF.map (phiEquiv G o)) := by
    intro p
    simp only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
  apply hinv.injective
  apply PMF.ext
  rintro ⟨y, a⟩
  calc
    (PMF.map (phiEquiv G o) (PMF.map (flipEquiv G g) (uniformLift G o ν).1)) (y, a) =
        (PMF.map (flipPairEquiv G g)
          (PMF.map (phiEquiv G o) (uniformLift G o ν).1)) (y, a) := by
      calc
        _ = (PMF.map ((phiEquiv G o) ∘ (flipEquiv G g))
            (uniformLift G o ν).1) (y, a) := by
              rw [PMF.map_comp]
        _ = (PMF.map ((flipPairEquiv G g) ∘ (phiEquiv G o))
            (uniformLift G o ν).1) (y, a) := by rw [hcommute]
        _ = _ := by rw [← PMF.map_comp]
    _ = (PMF.map (phiEquiv G o) (uniformLift G o ν).1)
        ((flipPairEquiv G g).symm (y, a)) := map_equiv_apply _ _ _
    _ = (PMF.map (phiEquiv G o) (uniformLift G o ν).1) (y, a + g) := by
      rfl
    _ = ν y * PMF.uniformOfFintype (Anchor G) (a + g) :=
      hmass y (a + g)
    _ = ν y * PMF.uniformOfFintype (Anchor G) a := by
      rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
    _ = (PMF.map (phiEquiv G o) (uniformLift G o ν).1) (y, a) :=
      (hmass y a).symm

theorem flip_invariant_lift_unique
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G)) :
    ∃! μ : LiftSpace G ν, FlipInvariant G μ.1 := by
  letI : Fintype (Anchor G) := Fintype.ofFinite (Anchor G)
  refine ⟨uniformLift G o ν, uniform_lift_flip_invariant G o ν, ?_⟩
  intro μ hμ
  have hq (y : ν.support) :
      (phi_probability_lift_classification G o ν μ) y =
        PMF.uniformOfFintype (Anchor G) :=
    flip_invariant_positive_fiber_uniform G o ν μ hμ y
  have hquniform (y : ν.support) :
      (phi_probability_lift_classification G o ν (uniformLift G o ν)) y =
        PMF.uniformOfFintype (Anchor G) := by
    have hr := (phi_probability_lift_classification G o ν).right_inv
      (fun _ => PMF.uniformOfFintype (Anchor G))
    exact congrFun hr y
  apply (phi_probability_lift_classification G o ν).injective
  funext y
  rw [hq y, hquniform y]

/-- Conditional cylinder probabilities factor into fair bit probabilities on any finite
set of components. The second clause gives the exact mass of a complete anchor vector.
The empty cylinder has mass one, including when the graph has no vertices. -/
theorem flip_invariant_positive_fiber_fair_bits
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (o : (K : G.ConnectedComponent) → K) (ν : PMF (Label G))
    (μ : LiftSpace G ν) (hμ : FlipInvariant G μ.1) (y : ν.support) :
    (∀ (S : Finset G.ConnectedComponent) (b : S → ZMod 2),
      PMF.map (fun a : Anchor G => fun K : S => a K)
        ((phi_probability_lift_classification G o ν μ) y) b =
          (2 : ENNReal)⁻¹ ^ S.card) ∧
    (∀ a : Anchor G, (phi_probability_lift_classification G o ν μ) y a =
      (2 : ENNReal)⁻¹ ^ Fintype.card G.ConnectedComponent) := by
  classical
  have hq := flip_invariant_positive_fiber_uniform G o ν μ hμ y
  have hcard : Fintype.card (Anchor G) = 2 ^ Fintype.card G.ConnectedComponent := by
    calc
      Fintype.card (Anchor G) = Nat.card (Anchor G) := Nat.card_eq_fintype_card.symm
      _ = Nat.card (ZMod 2) ^ Nat.card G.ConnectedComponent := Nat.card_fun
      _ = 2 ^ Fintype.card G.ConnectedComponent := by
        rw [Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card]
  constructor
  · intro S b
    rw [hq]
    let C : Set (Anchor G) := {a | (fun K : S => a K) = b}
    -- Restriction identifies this cylinder with the freely chosen bits on its complement.
    let e : C ≃ (↥(Sᶜ) → ZMod 2) :=
      { toFun := fun a K => a.val K
        invFun := fun f => ⟨fun K => if h : K ∈ S then b ⟨K, h⟩
          else f ⟨K, Finset.mem_compl.mpr h⟩, by
            funext K
            simp⟩
        left_inv := by
          intro a
          apply Subtype.ext
          funext K
          dsimp
          split_ifs with h
          · exact (congrFun a.property ⟨K, h⟩).symm
          · rfl
        right_inv := by
          intro f
          funext K
          simp [Finset.mem_compl.mp K.property] }
    have hC : Fintype.card C = 2 ^ (Sᶜ).card := by
      rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]
    have hprob :
        PMF.map (fun a : Anchor G => fun K : S => a K)
          (PMF.uniformOfFintype (Anchor G)) b =
            (PMF.uniformOfFintype (Anchor G)).toOuterMeasure C := by
      rw [PMF.map_apply, PMF.toOuterMeasure_apply]
      apply tsum_congr
      intro a
      simp [C, Set.indicator_apply, eq_comm]
    rw [hprob, PMF.toOuterMeasure_uniformOfFintype_apply, hC, hcard]
    rw [← Finset.card_compl_add_card S, Nat.cast_pow, Nat.cast_pow, pow_add]
    calc
      (2 : ENNReal) ^ (Sᶜ).card /
          ((2 : ENNReal) ^ (Sᶜ).card * (2 : ENNReal) ^ S.card) =
          1 / (2 : ENNReal) ^ S.card := by
        simpa only [mul_one] using
          (ENNReal.mul_div_mul_left 1 ((2 : ENNReal) ^ S.card)
            (pow_ne_zero _ (by norm_num)) (by simp))
      _ = (2 : ENNReal)⁻¹ ^ S.card := by
        rw [one_div, ENNReal.inv_pow]
  · intro a
    rw [hq, PMF.uniformOfFintype_apply, hcard, Nat.cast_pow, ENNReal.inv_pow]
    rfl

end
end D5.S3.Fourier.CharacterSelection.FiniteGraphProbabilityLift
