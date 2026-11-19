/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingWeldOrientationLaw
   mirror-E: none(waiver:symbolic-conditioning-law)
   anchors: []
   utility: none
   digest: Prescribed orientations of uniform lifts give uniform directed completions. -/

import D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw

open D5.S3.Combinatorics.Graph.LinearForests
open UndirectedCycleCompletionLaw CompatibleCycleInventory DirectedForestCompletion
open AlternatingUndirectedCompletionLaw
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal


/-! Uniform undirected weld completions and their directed orientations on one probability space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw

private theorem project_conditioned {A B : Type*} (p : PMF A) (f : A → B) (s : Set B)
    (h : ∃ a ∈ f ⁻¹' s, a ∈ p.support) :
    ∃ h' : ∃ b ∈ s, b ∈ (p.map f).support,
      (p.filter (f ⁻¹' s) h).map f = (p.map f).filter s h' := by
  classical
  have hs : ∃ b ∈ s, b ∈ (p.map f).support := by
    obtain ⟨a, ha, hap⟩ := h
    exact ⟨f a, ha, by rw [PMF.support_map]; exact ⟨a, hap, rfl⟩⟩
  refine ⟨hs, PMF.ext (fun b => ?_)⟩
  rw [PMF.map_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_map_apply]
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb, PMF.map_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases he : b = f a
    · have has : a ∈ f ⁻¹' s := by
        change f a ∈ s
        rwa [← he]
      simpa only [ite_eq_left he, PMF.filter_apply, ← PMF.toOuterMeasure_apply] using
        congrArg (fun z : ℝ≥0∞ => z * (p.toOuterMeasure (f ⁻¹' s))⁻¹)
          (Set.indicator_of_mem has (fun a => p a))
    · simp [he]
  · rw [Set.indicator_of_notMem hb, zero_mul]
    calc
      _ = ∑' _ : A, (0 : ℝ≥0∞) := by
        apply tsum_congr
        intro a
        by_cases he : b = f a
        · rw [ite_eq_left he]
          apply PMF.filter_apply_eq_zero_of_notMem
          intro ha
          apply hb
          change f a ∈ s at ha
          exact he.symm ▸ ha
        · simp [he]
      _ = 0 := tsum_zero

universe u
variable {V : Type u} [Fintype V] {F : SimpleGraph V}

/-- A lift whose successor permutation alternates the given colors. -/
abbrev OrientedCompletion (k : V → Bool) := {l : Lift F // ∀ x, k (l.σ x) ≠ k x}

private abbrev matchingOrientation (k : V → Bool) (ref : OrientedCompletion (F := F) k) :=
  {l : OrientedCompletion (F := F) k // l.1.E = ref.1.E}

private def completionEquiv (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (ref : OrientedCompletion (F := F) k) : matchingOrientation k ref ≃ AlternatingCompletion ref.1.E k where
  toFun l := ⟨l.1.1.σ, Fintype.card_pos_iff.mp (by omega), l.1.1.full,
    (fun x y h => l.1.1.extension x y (l.2.symm ▸ h)), l.1.2⟩
  invFun C := ⟨⟨{
    E := ref.1.E
    σ := C.1
    edge := ref.1.edge
    orient := ref.1.orient
    antisymm := ref.1.antisymm
    outgoing := ref.1.outgoing
    incoming := ref.1.incoming
    full := C.2.2.1
    extension := C.2.2.2.1 }, C.2.2.2.2⟩, rfl⟩
  left_inv _ := Subtype.ext (Subtype.ext (lift_ext hn rfl))
  right_inv _ := Subtype.ext rfl

private theorem conditional_completion (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (ref : OrientedCompletion (F := F) k) (μ : PMF (OrientedCompletion (F := F) k))
    (hμ : ∀ l, μ l = (Nat.card (OrientedCompletion (F := F) k) : ℝ≥0∞)⁻¹) :
    let event : Set (OrientedCompletion (F := F) k) := {l | l.1.E = ref.1.E}
    ∀ h : ∃ l ∈ event, l ∈ μ.support,
      ∃ ν : PMF (AlternatingCompletion ref.1.E k),
        (∀ c, ν c = (Nat.card (AlternatingCompletion ref.1.E k) : ℝ≥0∞)⁻¹) ∧
        μ.filter event h = ν.map (fun c => (completionEquiv hn k ref).symm c |>.1) := by
  classical
  let A := OrientedCompletion (F := F) k
  let : Finite A := Finite.of_injective (fun l : A => l.1.σ)
    (fun _ _ h => Subtype.ext (lift_ext hn h))
  let : Fintype A := Fintype.ofFinite _
  let : Nonempty A := ⟨ref⟩
  have heq : μ = uniformPmf A := PMF.ext fun l => by
    simpa only [uniformPmf, PMF.ofFintype_apply, ← Nat.card_eq_fintype_card] using hμ l
  subst μ
  let Q := matchingOrientation k ref
  let : Fintype Q := Fintype.ofFinite _
  let : Nonempty Q := ⟨⟨ref, rfl⟩⟩
  let D := AlternatingCompletion ref.1.E k
  let e : Q ≃ D := completionEquiv hn k ref
  let : Fintype D := Fintype.ofFinite _
  let : Nonempty D := ⟨e ⟨ref, rfl⟩⟩
  intro event h
  refine ⟨uniformPmf D, ?_, ?_⟩
  · intro c
    change uniformPmf D c = (Nat.card D : ℝ≥0∞)⁻¹
    simp only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
  · calc
      _ = (uniformPmf Q).map Subtype.val :=
        @uniform_filter A inferInstance inferInstance (fun l => l.1.E = ref.1.E)
          (inferInstance : Fintype Q) (inferInstance : Nonempty Q) h
      _ = ((uniformPmf D).map e.symm).map (fun l : Q => l.1) := by rw [uniform_equiv e.symm]
      _ = _ := by simp only [PMF.map_comp]; rfl

omit [Fintype V] in
private theorem oriented_edge_card (l : Lift F) :
    Nat.card {pair : V × V // l.E pair.1 pair.2} = Nat.card F.edgeSet := by
  let forgetEdge (a : {pair : V × V // l.E pair.1 pair.2}) : F.edgeSet :=
    ⟨s(a.1.1, a.1.2), l.edge _ _ a.2⟩
  have hinj : Function.Injective forgetEdge := by
    rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨c, d⟩, hc⟩ h
    have hpair : s(a, b) = s(c, d) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hpair with hsame | hswap
    · exact Subtype.ext (Prod.ext hsame.1 hsame.2)
    · obtain ⟨rfl, rfl⟩ := hswap
      exact (l.antisymm _ _ ha hc).elim
  have hsurj : Function.Surjective forgetEdge := by
    rintro ⟨edge, he⟩
    induction edge using Sym2.ind with
    | h a b =>
      rcases l.orient a b he with hab | hba
      · exact ⟨⟨(a, b), hab⟩, rfl⟩
      · exact ⟨⟨(b, a), hba⟩, Subtype.ext (Sym2.eq_swap)⟩
  exact Nat.card_congr (Equiv.ofBijective forgetEdge ⟨hinj, hsurj⟩)

private theorem alternate_shadow_iff (hn : 3 ≤ Fintype.card V) (k : V → Bool) (l : Lift F) :
    (∀ x, k (l.σ x) ≠ k x) ↔ ∀ x y, (forget hn l).1.Adj x y → k x ≠ k y := by
  constructor
  · intro h x y hxy
    rcases (shadow_adj hn l.σ l.full x y).mp hxy with hxy | hxy
    · simpa [hxy] using (h x).symm
    · simpa [hxy] using h y
  · intro h x
    exact (h x (l.σ x) ((shadow_adj hn l.σ l.full x _).mpr (Or.inl rfl))).symm

/-- Forget the direction of a lift while retaining the actual completed graph. -/
def forgetOrientation (hn : 3 ≤ Fintype.card V) (k : V → Bool) (l : OrientedCompletion (F := F) k) :
    AlternatingCompletedGraph k F :=
  ⟨forget hn l.1, (alternate_shadow_iff hn k l.1).mp l.2⟩

private theorem uniform_orientation_push (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (reference : AlternatingCompletedGraph k F) :
    ∃ (μ : PMF (OrientedCompletion (F := F) k)) (ν : PMF (AlternatingCompletedGraph k F)),
      (∀ l, μ l = (Nat.card (OrientedCompletion (F := F) k) : ℝ≥0∞)⁻¹) ∧
      (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
      μ.map (forgetOrientation hn k) = ν := by
  classical
  let A₀ := Lift F
  let B₀ := CompletedGraph F
  let A := OrientedCompletion (F := F) k
  let B := AlternatingCompletedGraph k F
  let f : A₀ → B₀ := forget hn
  let s : Set B₀ := {C | ∀ a b, C.1.Adj a b → k a ≠ k b}
  let t : Set A₀ := {l | ∀ x, k (l.σ x) ≠ k x}
  have he : f ⁻¹' s = t := by
    ext l
    exact (alternate_shadow_iff hn k l).symm
  let : Finite A₀ := Finite.of_injective (fun l : A₀ => l.σ) (fun _ _ h => lift_ext hn h)
  let : Finite B₀ := Finite.of_surjective f (forget_surjective hn F)
  let : Fintype A₀ := Fintype.ofFinite _
  let : Fintype B₀ := Fintype.ofFinite _
  obtain ⟨ref, href⟩ := forget_surjective hn F reference.1
  let : Nonempty A₀ := ⟨ref⟩
  let : Nonempty B₀ := ⟨reference.1⟩
  let : Fintype A := Fintype.ofFinite (↑t)
  let : Fintype B := Fintype.ofFinite (↑s)
  have ht : ref ∈ t := (alternate_shadow_iff hn k ref).mpr (href.symm ▸ reference.2)
  let : Nonempty A := ⟨⟨ref, ht⟩⟩
  let : Nonempty B := ⟨reference⟩
  obtain ⟨μ, ν, hμ, hν, hpush⟩ := uniform_undirected_completion hn F ⟨reference.1⟩
  have uniformA : μ = uniformPmf A₀ := PMF.ext fun l => by
    simpa only [uniformPmf, PMF.ofFintype_apply, ← Nat.card_eq_fintype_card] using hμ l
  have uniformB : ν = uniformPmf B₀ := PMF.ext fun C => by
    simpa only [uniformPmf, PMF.ofFintype_apply, ← Nat.card_eq_fintype_card] using hν C
  subst μ
  subst ν
  have htSupport : ∃ l ∈ f ⁻¹' s, l ∈ (uniformPmf A₀).support := by
    refine ⟨ref, he.symm ▸ ht, ?_⟩
    change uniformPmf A₀ ref ≠ 0
    rw [hμ]
    exact (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne'
  obtain ⟨hsSupport, hh⟩ := project_conditioned (uniformPmf A₀) f s htSupport
  have hpush' : (uniformPmf A₀).map f = uniformPmf B₀ := hpush
  have hsSupport' : ∃ b ∈ s, b ∈ (uniformPmf B₀).support := hpush' ▸ hsSupport
  have hFilterCongr {D : Type u} {p q : PMF D} {S T : Set D}
      (hpq : p = q) (hst : S = T) (hp : ∃ a ∈ S, a ∈ p.support)
      (hq : ∃ a ∈ T, a ∈ q.support) : p.filter S hp = q.filter T hq := by
    subst q
    subst T
    rfl
  have htSupport' : ∃ a ∈ t, a ∈ (uniformPmf A₀).support := he ▸ htSupport
  have hfiltA : (uniformPmf A₀).filter (f ⁻¹' s) htSupport =
      (uniformPmf A).map (fun l : A => l.1) := by
    exact (hFilterCongr rfl he htSupport htSupport').trans
      (@uniform_filter A₀ _ _ (fun l => ∀ x, k (l.σ x) ≠ k x) _ _ htSupport')
  have hfiltB : ((uniformPmf A₀).map f).filter s hsSupport =
      (uniformPmf B).map (fun C : B => C.1) :=
    (hFilterCongr hpush' rfl hsSupport hsSupport').trans
      (@uniform_filter B₀ _ _ (fun C => ∀ a b, C.1.Adj a b → k a ≠ k b)
        (inferInstance : Fintype B) (inferInstance : Nonempty B) hsSupport')
  rw [hfiltA, hfiltB] at hh
  have hh' : ((uniformPmf A).map (forgetOrientation hn k)).map (fun C : B => C.1) =
      (uniformPmf B).map (fun C : B => C.1) := by
    rw [PMF.map_comp, ← hh, PMF.map_comp]
    rfl
  let back : B₀ → B := Function.invFun (fun C : B => C.1)
  have hBack : Function.LeftInverse back (fun C : B => C.1) :=
    Function.leftInverse_invFun Subtype.val_injective
  have hg := congrArg (fun p : PMF B₀ => p.map back) hh'
  simp only [PMF.map_comp, show back ∘ (fun C : B => C.1) = id from funext hBack,
    PMF.map_id] at hg
  have hLiftBack : back ∘ (fun C : B => C.1) ∘ forgetOrientation hn k = forgetOrientation hn k :=
    funext fun l => hBack (forgetOrientation hn k l)
  rw [hLiftBack] at hg
  refine ⟨uniformPmf A, uniformPmf B, ?_, ?_, hg⟩
  · intro l
    change uniformPmf A l = (Nat.card A : ℝ≥0∞)⁻¹
    simp only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
  · intro C
    change uniformPmf B C = (Nat.card B : ℝ≥0∞)⁻¹
    simp only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]


/-- Sample an undirected alternating completion and its oriented lift on a common law.
Conditioning on the orientation of the prescribed edges gives a uniform directed completion. -/
theorem alternating_weld_orientation_law (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (reference : AlternatingCompletedGraph k F) :
    ∃ (μ : PMF (OrientedCompletion (F := F) k)) (ν : PMF (AlternatingCompletedGraph k F)),
      (∀ l, μ l = (Nat.card (OrientedCompletion (F := F) k) : ℝ≥0∞)⁻¹) ∧
      (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
      μ.map (forgetOrientation hn k) = ν ∧
      ∀ ref : OrientedCompletion (F := F) k,
        Nat.card {edge : V × V // ref.1.E edge.1 edge.2} = Nat.card F.edgeSet ∧
        let event : Set (OrientedCompletion (F := F) k) := {l | l.1.E = ref.1.E}
        ∀ h : ∃ l ∈ event, l ∈ μ.support,
          ∃ (ρ : PMF (AlternatingCompletion ref.1.E k))
            (toLift : AlternatingCompletion ref.1.E k → OrientedCompletion (F := F) k),
            (∀ c, ρ c = (Nat.card (AlternatingCompletion ref.1.E k) : ℝ≥0∞)⁻¹) ∧
            (∀ c, (toLift c).1.E = ref.1.E ∧ (toLift c).1.σ = c.1) ∧
            μ.filter event h = ρ.map toLift := by
  obtain ⟨μ, ν, hμ, hν, hPush⟩ := uniform_orientation_push hn k reference
  refine ⟨μ, ν, hμ, hν, hPush, fun ref => ⟨oriented_edge_card ref.1, ?_⟩⟩
  intro event h
  let e := completionEquiv hn k ref
  obtain ⟨ρ, hρ, hFilter⟩ := conditional_completion hn k ref μ hμ h
  exact ⟨ρ, fun c => (e.symm c).1, hρ, fun _ => ⟨rfl, rfl⟩, hFilter⟩

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingWeldOrientationLaw
