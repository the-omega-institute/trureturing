/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Equivariant cube roots on three complete return charts are exactly local roots or a conjugate three-cycle. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.TwoOrbitSquareRootCriterion
import Mathlib.Tactic.FinCases

/-! Equivariant cube roots on three complete signed return charts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ThreeOrbitCubeRootCharts

open PrimitiveLiftRootCriterion
open TwoOrbitSquareRootCriterion (forward seam_obstruction transport transport_point transport_deck)
universe u v w x

variable {H : Type u} [Group H] {X : Type v} {Y : Type w} {Z : Type x}
  (A : ReturnAtlas H X) (B : ReturnAtlas H Y) (C : ReturnAtlas H Z)

/-- The specified time maps on the disjoint three-chart carrier. -/
def jointTime : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z) :=
  Sum.map A.time (Sum.map B.time C.time)

/-- The specified left deck action on each of the three charts. -/
def jointDeck (a : H) : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z) :=
  Sum.map (A.deck a) (Sum.map (B.deck a) (C.deck a))

/-- The exact signed local cube-root equation in one return chart. -/
def Local (A : ReturnAtlas H X) : Prop :=
  ∃ s : Fin A.period, ∃ m : ℤ, ∃ b : H, Commute b A.holonomy ∧
    (3 : ℤ) * (s.val : ℤ) = 1 + (A.period : ℤ) * m ∧ b ^ 3 * A.holonomy ^ m = 1

private theorem conjugacy_inverse {a b c : H} (h : b * c = a * b) :
    b⁻¹ * a = c * b⁻¹ := by
  apply mul_left_cancel (a := b)
  simpa [mul_assoc] using congrArg (· * b⁻¹) h.symm

private theorem cycle_obstruction (f : X → Y) (g : Y → Z) (k : Z → X)
    (hf : ∀ a q, f (A.deck a q) = B.deck a (f q))
    (hg : ∀ a q, g (B.deck a q) = C.deck a (g q))
    (hk : ∀ a q, k (C.deck a q) = A.deck a (k q))
    (ft : ∀ q, f (A.time q) = B.time (f q))
    (gt : ∀ q, g (B.time q) = C.time (g q))
    (kt : ∀ q, k (C.time q) = A.time (k q)) :
    A.period = B.period ∧ B.period = C.period ∧
      (∃ b : H, b * B.holonomy = A.holonomy * b) ∧
      (∃ c : H, c * C.holonomy = B.holonomy * c) := by
  obtain ⟨m, b, hm, hb⟩ := seam_obstruction A B f hf ft
  obtain ⟨n, c, hn, hc⟩ := seam_obstruction B C g hg gt
  obtain ⟨l, e, hl, _⟩ := seam_obstruction C A k hk kt
  have ha : (0 : ℤ) < A.period := by exact_mod_cast A.positive
  have hbp : (0 : ℤ) < B.period := by exact_mod_cast B.positive
  have hcp : (0 : ℤ) < C.period := by exact_mod_cast C.positive
  have hmpos : 1 ≤ m := by nlinarith
  have hnpos : 1 ≤ n := by nlinarith
  have hlpos : 1 ≤ l := by nlinarith
  have hab : (A.period : ℤ) ≥ B.period := by nlinarith
  have hbc : (B.period : ℤ) ≥ C.period := by nlinarith
  have hca : (C.period : ℤ) ≥ A.period := by nlinarith
  have hdab : A.period = B.period := by exact_mod_cast (show (A.period : ℤ) = B.period by omega)
  have hdbc : B.period = C.period := by exact_mod_cast (show (B.period : ℤ) = C.period by omega)
  have hmone : m = 1 := by rw [hdab] at hm; nlinarith
  have hnone : n = 1 := by rw [hdbc] at hn; nlinarith
  exact ⟨hdab, hdbc, ⟨b, by simpa [hmone] using hb⟩,
    ⟨c, by simpa [hnone] using hc⟩⟩

private def tag : X ⊕ (Y ⊕ Z) → Fin 3 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))

private theorem component_constant {W : Type*} (S : ReturnAtlas H W)
    (f : W → X ⊕ (Y ⊕ Z))
    (hf : ∀ a q, f (S.deck a q) = jointDeck A B C a (f q))
    (ht : ∀ q, f (S.time q) = jointTime A B C (f q)) :
    ∀ q, tag (f q) = tag (f (S.point 0 1)) := by
  have td : ∀ a q, tag (jointDeck A B C a q) = tag q := by
    intro a q
    rcases q with q | q | q <;> rfl
  have tt : ∀ q, tag (jointTime A B C q) = tag q := by
    intro q
    rcases q with q | q | q <;> rfl
  have hp : ∀ q : ℕ, ∀ z, tag (f (S.point q z)) = tag (f (S.point 0 1)) := by
    intro q
    induction q with
    | zero =>
      intro z
      have h := congrArg tag (hf z (S.point 0 1))
      simpa only [S.deck_point, mul_one, td, Nat.cast_zero] using h
    | succ q ih =>
      intro z
      rw [show ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 by omega,
        ← S.time_point, ht, tt, ih]
  intro q
  obtain ⟨⟨t, z⟩, rfl⟩ := S.coordinates.surjective q
  exact hp t.val z

private theorem three_component_cycles (σ : Fin 3 → Fin 3)
    (hc : ∀ i, σ (σ (σ i)) = i) :
    (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨
    (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
    (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) := by
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  generalize hσ0 : σ 0 = i0
  generalize hσ1 : σ 1 = i1
  generalize hσ2 : σ 2 = i2
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all

private theorem preserving (r : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z))
    (hr : ∀ a q, r (jointDeck A B C a q) = jointDeck A B C a (r q))
    (hs : ∀ q, r (r (r q)) = jointTime A B C q)
    (h0 : ∀ q : X, ∃ p : X, r (.inl q) = .inl p)
    (h1 : ∀ q : Y, ∃ p : Y, r (.inr (.inl q)) = .inr (.inl p))
    (h2 : ∀ q : Z, ∃ p : Z, r (.inr (.inr q)) = .inr (.inr p)) :
    Local A ∧ Local B ∧ Local C := by
  choose f hfl using h0
  choose g hgl using h1
  choose k hkl using h2
  have hf : A.Equivariant f := by
    intro a q
    apply Sum.inl.inj
    simpa only [jointDeck, Sum.map_inl, hfl] using hr a (.inl q)
  have hg : B.Equivariant g := by
    intro a q
    apply Sum.inl.inj ∘ Sum.inr.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hgl] using hr a (.inr (.inl q))
  have hk : C.Equivariant k := by
    intro a q
    apply Sum.inr.inj ∘ Sum.inr.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hkl] using hr a (.inr (.inr q))
  have fs : f^[3] = A.time := by
    funext q
    apply Sum.inl.inj
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      jointTime, Sum.map_inl, hfl] using hs (.inl q)
  have gs : g^[3] = B.time := by
    funext q
    apply Sum.inl.inj ∘ Sum.inr.inj
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      jointTime, Sum.map_inl, Sum.map_inr, hgl] using hs (.inr (.inl q))
  have ks : k^[3] = C.time := by
    funext q
    apply Sum.inr.inj ∘ Sum.inr.inj
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      jointTime, Sum.map_inl, Sum.map_inr, hkl] using hs (.inr (.inr q))
  exact ⟨(A.root_criterion 3).1 ⟨f, hf, fs⟩,
    (B.root_criterion 3).1 ⟨g, hg, gs⟩, (C.root_criterion 3).1 ⟨k, hk, ks⟩⟩

private theorem exchanging (r : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z))
    (hr : ∀ a q, r (jointDeck A B C a q) = jointDeck A B C a (r q))
    (ht : ∀ q, r (jointTime A B C q) = jointTime A B C (r q))
    (h0 : ∀ q : X, ∃ p : Y, r (.inl q) = .inr (.inl p))
    (h1 : ∀ q : Y, ∃ p : Z, r (.inr (.inl q)) = .inr (.inr p))
    (h2 : ∀ q : Z, ∃ p : X, r (.inr (.inr q)) = .inl p) :
    A.period = B.period ∧ B.period = C.period ∧
      (∃ b : H, b * B.holonomy = A.holonomy * b) ∧
      (∃ c : H, c * C.holonomy = B.holonomy * c) := by
  choose f hfl using h0
  choose g hgl using h1
  choose k hkl using h2
  apply cycle_obstruction A B C f g k
  · intro a q
    apply Sum.inl.inj ∘ Sum.inr.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hfl] using hr a (.inl q)
  · intro a q
    apply Sum.inr.inj ∘ Sum.inr.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hgl] using hr a (.inr (.inl q))
  · intro a q
    apply Sum.inl.inj
    simpa only [jointDeck, Sum.map_inl, Sum.map_inr, hkl] using hr a (.inr (.inr q))
  · intro q
    apply Sum.inl.inj ∘ Sum.inr.inj
    simpa only [jointTime, Sum.map_inl, Sum.map_inr, hfl] using ht (.inl q)
  · intro q
    apply Sum.inr.inj ∘ Sum.inr.inj
    simpa only [jointTime, Sum.map_inl, Sum.map_inr, hgl] using ht (.inr (.inl q))
  · intro q
    apply Sum.inl.inj
    simpa only [jointTime, Sum.map_inl, Sum.map_inr, hkl] using ht (.inr (.inr q))

private theorem tag_zero_iff (q : X ⊕ (Y ⊕ Z)) : tag q = 0 ↔ ∃ p : X, q = .inl p := by
  rcases q with q | q | q <;> simp [tag]

private theorem tag_one_iff (q : X ⊕ (Y ⊕ Z)) :
    tag q = 1 ↔ ∃ p : Y, q = .inr (.inl p) := by
  rcases q with q | q | q <;> simp [tag]

private theorem tag_two_iff (q : X ⊕ (Y ⊕ Z)) :
    tag q = 2 ↔ ∃ p : Z, q = .inr (.inr p) := by
  rcases q with q | q | q <;> simp [tag]

/-- An equivariant cube root either acts locally in all three charts or cycles
three charts with equal periods and conjugate holonomies. -/
theorem chart_criterion :
    (∃ r : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z),
      (∀ a q, r (jointDeck A B C a q) = jointDeck A B C a (r q)) ∧
      r^[3] = jointTime A B C) ↔
    ((Local A ∧ Local B ∧ Local C) ∨
      (A.period = B.period ∧ B.period = C.period ∧
        (∃ b : H, b * B.holonomy = A.holonomy * b) ∧
        (∃ c : H, c * C.holonomy = B.holonomy * c))) := by
  constructor
  · rintro ⟨r, hr, hs⟩
    have cube : ∀ q, r (r (r q)) = jointTime A B C q := by
      intro q
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using congrFun hs q
    have ht : ∀ q, r (jointTime A B C q) = jointTime A B C (r q) := by
      intro q
      rw [← hs]
      exact Function.Commute.self_iterate r 3 q
    have h0 := component_constant A B C A (fun q => r (.inl q))
      (by intro a q; exact hr a (.inl q)) (by intro q; exact ht (.inl q))
    have h1 := component_constant A B C B (fun q => r (.inr (.inl q)))
      (by intro a q; exact hr a (.inr (.inl q))) (by intro q; exact ht (.inr (.inl q)))
    have h2 := component_constant A B C C (fun q => r (.inr (.inr q)))
      (by intro a q; exact hr a (.inr (.inr q))) (by intro q; exact ht (.inr (.inr q)))
    let σ : Fin 3 → Fin 3 := ![tag (r (.inl (A.point 0 1))),
      tag (r (.inr (.inl (B.point 0 1)))), tag (r (.inr (.inr (C.point 0 1))))]
    have law : ∀ q, tag (r q) = σ (tag q) := by
      intro q
      rcases q with q | q | q
      · simpa [σ, tag] using h0 q
      · simpa [σ, tag] using h1 q
      · simpa [σ, tag] using h2 q
    have σcube : ∀ i, σ (σ (σ i)) = i := by
      intro i
      fin_cases i
      · have h := congrArg tag (cube (.inl (A.point 0 1)))
        rw [law, law, law] at h
        simpa [jointTime, tag] using h
      · have h := congrArg tag (cube (.inr (.inl (B.point 0 1))))
        rw [law, law, law] at h
        simpa [jointTime, tag] using h
      · have h := congrArg tag (cube (.inr (.inr (C.point 0 1))))
        rw [law, law, law] at h
        simpa [jointTime, tag] using h
    rcases three_component_cycles σ σcube with ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩
    · left
      apply preserving A B C r hr cube
      · intro q
        apply (tag_zero_iff _).1
        rw [law]
        exact s0
      · intro q
        apply (tag_one_iff _).1
        rw [law]
        exact s1
      · intro q
        apply (tag_two_iff _).1
        rw [law]
        exact s2
    · right
      apply exchanging A B C r hr ht
      · intro q
        apply (tag_one_iff _).1
        rw [law]
        exact s0
      · intro q
        apply (tag_two_iff _).1
        rw [law]
        exact s1
      · intro q
        apply (tag_zero_iff _).1
        rw [law]
        exact s2
    · right
      apply exchanging A B C (r ∘ r)
      · intro a q
        simp only [Function.comp_apply, hr]
      · intro q
        simp only [Function.comp_apply, ht]
      · intro q
        apply (tag_one_iff _).1
        change tag (r (r (.inl q))) = 1
        rw [law, law]
        change σ (σ 0) = 1
        rw [s0, s2]
      · intro q
        apply (tag_two_iff _).1
        change tag (r (r (.inr (.inl q)))) = 2
        rw [law, law]
        change σ (σ 1) = 2
        rw [s1, s0]
      · intro q
        apply (tag_zero_iff _).1
        change tag (r (r (.inr (.inr q)))) = 0
        rw [law, law]
        change σ (σ 2) = 0
        rw [s2, s1]
  · rintro (⟨h0, h1, h2⟩ | ⟨hdab, hdbc, ⟨b, hb⟩, ⟨c, hc⟩⟩)
    · obtain ⟨f, hf, fs⟩ := (A.root_criterion 3).2 h0
      obtain ⟨g, hg, gs⟩ := (B.root_criterion 3).2 h1
      obtain ⟨k, hk, ks⟩ := (C.root_criterion 3).2 h2
      refine ⟨Sum.map f (Sum.map g k), ?_, ?_⟩
      · intro a q
        rcases q with q | q | q
        · exact congrArg Sum.inl (hf a q)
        · exact congrArg (fun z => Sum.inr (Sum.inl z)) (hg a q)
        · exact congrArg (fun z => Sum.inr (Sum.inr z)) (hk a q)
      · funext q
        rcases q with q | q | q
        · exact congrArg Sum.inl (congrFun fs q)
        · exact congrArg (fun z => Sum.inr (Sum.inl z)) (congrFun gs q)
        · exact congrArg (fun z => Sum.inr (Sum.inr z)) (congrFun ks q)
    · have hca : (b * c)⁻¹ * A.holonomy = C.holonomy * (b * c)⁻¹ := by
        apply conjugacy_inverse
        calc
          (b * c) * C.holonomy = b * (c * C.holonomy) := mul_assoc _ _ _
          _ = b * (B.holonomy * c) := by rw [hc]
          _ = A.holonomy * (b * c) := by rw [← mul_assoc, hb, mul_assoc]
      let r : X ⊕ (Y ⊕ Z) → X ⊕ (Y ⊕ Z) := Sum.elim
        (fun q => .inr (.inl (transport A B b q)))
        (Sum.elim (fun q => .inr (.inr (transport B C c q)))
          (fun q => .inl (A.time (transport C A (b * c)⁻¹ q))))
      refine ⟨r, ?_, ?_⟩
      · intro a q
        rcases q with q | q | q
        · exact congrArg (fun z => Sum.inr (Sum.inl z))
            (transport_deck A B hdab b hb a q)
        · exact congrArg (fun z => Sum.inr (Sum.inr z))
            (transport_deck B C hdbc c hc a q)
        · obtain ⟨t, z, rfl⟩ := C.covers q
          change Sum.inl _ = Sum.inl _
          congr 1
          rw [C.deck_point, transport_point C A (hdab.trans hdbc).symm _ hca,
            A.time_point, transport_point C A (hdab.trans hdbc).symm _ hca,
            A.time_point, A.deck_point, mul_assoc]
      · funext q
        rcases q with q | q | q
        · obtain ⟨t, z, rfl⟩ := A.covers q
          change Sum.inl (A.time (transport C A (b * c)⁻¹
            (transport B C c (transport A B b (A.point t z))))) = _
          rw [transport_point A B hdab b hb, transport_point B C hdbc c hc,
            transport_point C A (hdab.trans hdbc).symm _ hca]
          simp [mul_inv_rev, mul_assoc, jointTime]
        · obtain ⟨t, z, rfl⟩ := B.covers q
          change Sum.inr (Sum.inl (transport A B b (A.time
            (transport C A (b * c)⁻¹ (transport B C c (B.point t z)))))) = _
          rw [transport_point B C hdbc c hc,
            transport_point C A (hdab.trans hdbc).symm _ hca, A.time_point,
            transport_point A B hdab b hb]
          simp [mul_inv_rev, mul_assoc, jointTime, B.time_point]
        · obtain ⟨t, z, rfl⟩ := C.covers q
          change Sum.inr (Sum.inr (transport B C c (transport A B b (A.time
            (transport C A (b * c)⁻¹ (C.point t z)))))) = _
          rw [transport_point C A (hdab.trans hdbc).symm _ hca, A.time_point,
            transport_point A B hdab b hb, transport_point B C hdbc c hc]
          simp [mul_inv_rev, mul_assoc, jointTime, C.time_point]

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ThreeOrbitCubeRootCharts
