/- GID: D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/HoneycombOddCylinderCoordination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Coordination sequences of odd-width honeycomb cylinders. -/

/-
admission_basis: open-problem-resolution (#27218; Proved)
escape_witness: odd-period strip normalization and the shell-card formulas feed result.
Direct frozen dependencies:
D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.potential
D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.geodesic
D5/S3/StatisticalMechanics/HoneycombCylinderCoordination.plane_distance
D5/S3/StatisticalMechanics/TeaCoordinationSequence.residual
name: proof_shape=bind-only; consumers=oddShift_zero, oddShift_add, translationSetoid, oddShift_adj, projectHom, normal, band_minimum
name: proof_shape=bind-only; consumers=evenShellEquiv, oddShellEquiv, finite_shell, even_card, odd_card
name: proof_shape=content; consumers=result
result: proof_shape=content; consumers=Reg.family
-/

import D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
import D5.S3.StatisticalMechanics.TeaCoordinationSequence

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.HoneycombOddCylinderCoordination

open D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
open PowerSeries

private def oddShift (n : ℕ) (k : ℤ) (v : Vertex) : Vertex :=
  (v.1, v.2.1 + ((n : ℤ) + 1) * k, v.2.2 + (n : ℤ) * k)

private lemma oddShift_zero (n : ℕ) (v : Vertex) : oddShift n 0 v = v := by
  rcases v with ⟨b, i, j⟩
  simp [oddShift]

private lemma oddShift_add (n : ℕ) (k l : ℤ) (v : Vertex) :
    oddShift n l (oddShift n k v) = oddShift n (k+l) v := by
  simp [oddShift, mul_add, add_assoc]

def translationSetoid (n : ℕ) : Setoid Vertex where
  r u v := ∃ k : ℤ, oddShift n k u = v
  iseqv := ⟨fun u => ⟨0, oddShift_zero n u⟩, by
    rintro u v ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    rw [oddShift_add]
    simpa using oddShift_zero n u, by
    rintro u v w ⟨k, rfl⟩ ⟨l, rfl⟩
    exact ⟨k+l, (oddShift_add n k l u).symm⟩⟩

abbrev Cylinder (n : ℕ) := Quotient (translationSetoid n)

def cylinderGraph (n : ℕ) : SimpleGraph (Cylinder n) :=
  honeycombGraph.map (Quotient.mk (translationSetoid n))

def origin (n : ℕ) : Cylinder n := Quotient.mk _ (false, 0, 0)

def c (n m : ℕ) : ℕ := Nat.card {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m}

private lemma oddShift_adj (n : ℕ) (k : ℤ) {u v : Vertex}
    (h : honeycombGraph.Adj u v) :
    honeycombGraph.Adj (oddShift n k u) (oddShift n k v) := by
  change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) at h ⊢
  rcases h with ⟨hu, hv, he⟩ | ⟨hv, hu, he⟩
  · left
    refine ⟨hu, hv, ?_⟩
    dsimp [oddShift]
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by rw [h₁], by rw [h₂]⟩
    · exact Or.inr (Or.inl ⟨by rw [h₁]; ring, by rw [h₂]⟩)
    · exact Or.inr (Or.inr ⟨by rw [h₁], by rw [h₂]; ring⟩)
  · right
    refine ⟨hv, hu, ?_⟩
    dsimp [oddShift]
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨by rw [h₁], by rw [h₂]⟩
    · exact Or.inr (Or.inl ⟨by rw [h₁]; ring, by rw [h₂]⟩)
    · exact Or.inr (Or.inr ⟨by rw [h₁], by rw [h₂]; ring⟩)

private def projectHom (n : ℕ) : honeycombGraph →g cylinderGraph n :=
  SimpleGraph.Hom.map (Quotient.mk (translationSetoid n)) honeycombGraph (by
    intro u v h he
    obtain ⟨k, hk⟩ := Quotient.exact he
    have hc := congrArg Prod.fst hk
    change u.1 = v.1 at hc
    rcases h with ⟨hu, hv, _⟩ | ⟨hv, hu, _⟩ <;> simp_all)

private lemma quotient_reachable (n : ℕ) (q : Cylinder n) :
    (cylinderGraph n).Reachable (origin n) q := by
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨p, _⟩ := geodesic v
    exact ⟨p.map (projectHom n)⟩

private lemma quotient_upper (n : ℕ) (v : Vertex) :
    (cylinderGraph n).dist (origin n) (Quotient.mk _ v) ≤ potential v := by
  obtain ⟨p, hp⟩ := geodesic v
  have h := SimpleGraph.dist_le (p.map (projectHom n))
  change (cylinderGraph n).dist (origin n) (Quotient.mk _ v) ≤ _ at h
  simpa only [SimpleGraph.Walk.length_map, hp] using h

private lemma lift_edge (n : ℕ) (v : Vertex) (q : Cylinder n)
    (h : (cylinderGraph n).Adj (Quotient.mk _ v) q) :
    ∃ w, honeycombGraph.Adj v w ∧ Quotient.mk (translationSetoid n) w = q := by
  obtain ⟨_, a, b, hab, ha, hb⟩ := h
  obtain ⟨k, hk⟩ := Quotient.exact ha
  refine ⟨oddShift n k b, ?_, ?_⟩
  · simpa only [hk] using oddShift_adj n k hab
  · have he : (Quotient.mk (translationSetoid n) b : Cylinder n) =
        Quotient.mk _ (oddShift n k b) := Quotient.sound ⟨k, rfl⟩
    exact he.symm.trans hb

private lemma lift_walk {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (π : V → W)
    (hlift : ∀ v q, H.Adj (π v) q → ∃ w, G.Adj v w ∧ π w = q)
    {q r : W} (p : H.Walk q r) (v : V) (hv : π v = q) :
    ∃ w, π w = r ∧ ∃ p' : G.Walk v w, p'.length = p.length := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => exact ⟨v, hv, .nil, rfl⟩
  | @Hconcat q s r p hadj ih =>
    obtain ⟨z, hz, p', hp'⟩ := ih
    obtain ⟨w, hw, he⟩ := hlift z r (hz ▸ hadj)
    exact ⟨w, he, p'.concat hw, by simp only [SimpleGraph.Walk.length_concat, hp']⟩

private lemma quotient_minimum {W : Type} (H : SimpleGraph W)
    (π : honeycombGraph →g H) (hsurj : Function.Surjective π)
    (hlift : ∀ v q, H.Adj (π v) q → ∃ w, honeycombGraph.Adj v w ∧ π w = q)
    (q : W) :
    ∃ v, π v = q ∧ potential v = H.dist (π (false, 0, 0)) q := by
  obtain ⟨u, rfl⟩ := hsurj q
  obtain ⟨pu, _⟩ := geodesic u
  have hr : H.Reachable (π (false, 0, 0)) (π u) := ⟨pu.map π⟩
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨v, hv, p', hp'⟩ := lift_walk honeycombGraph H π hlift p (false, 0, 0) rfl
  refine ⟨v, hv, le_antisymm ?_ ?_⟩
  · rw [← plane_distance]
    exact (SimpleGraph.dist_le p').trans_eq (hp'.trans hp)
  · obtain ⟨pv, hpv⟩ := geodesic v
    have hb := SimpleGraph.dist_le (pv.map π)
    simpa only [SimpleGraph.Walk.length_map, hpv, hv] using hb

private def lower (n : ℕ) (b : Bool) : ℤ := if b then -(n : ℤ)-1 else -(n : ℤ)

private def inBand (n : ℕ) (v : Vertex) : Prop :=
  lower n v.1 ≤ v.2.1 + v.2.2 ∧ v.2.1 + v.2.2 < lower n v.1 + (2*n+1 : ℤ)

private def normal (n : ℕ) (v : Vertex) : Vertex :=
  oddShift n (-((v.2.1 + v.2.2 - lower n v.1) / (2*(n : ℤ)+1))) v

private lemma normal_class (n : ℕ) (v : Vertex) :
    (Quotient.mk (translationSetoid n) (normal n v) : Cylinder n) = Quotient.mk _ v := by
  apply Eq.symm
  apply Quotient.sound
  exact ⟨_, rfl⟩

private lemma normal_band (n : ℕ) (v : Vertex) : inBand n (normal n v) := by
  have hp : (0 : ℤ) < 2*(n : ℤ)+1 := by omega
  have h₀ := Int.emod_nonneg (v.2.1 + v.2.2 - lower n v.1) (by omega : (2*(n : ℤ)+1) ≠ 0)
  have h₁ := Int.emod_lt_of_pos (v.2.1 + v.2.2 - lower n v.1) hp
  have hd := Int.emod_add_mul_ediv (v.2.1 + v.2.2 - lower n v.1) (2*(n : ℤ)+1)
  have hs : (normal n v).2.1 + (normal n v).2.2 = lower n v.1 +
      (v.2.1 + v.2.2 - lower n v.1) % (2*(n : ℤ)+1) := by
    dsimp [normal, oddShift]
    nlinarith [hd]
  change lower n v.1 ≤ _ ∧ _ < lower n v.1 + (2*n+1 : ℤ)
  rw [hs]
  omega

private lemma band_unique (n : ℕ) {u v : Vertex}
    (hu : inBand n u) (hv : inBand n v)
    (he : (Quotient.mk (translationSetoid n) u : Cylinder n) = Quotient.mk _ v) : u = v := by
  obtain ⟨k, rfl⟩ := Quotient.exact he
  have hp : (0 : ℤ) < 2*(n : ℤ)+1 := by omega
  have hk : k = 0 := by
    dsimp [inBand, oddShift] at hu hv
    ring_nf at hu hv
    by_cases h₀ : 0 < k
    · have hd : 2*(n : ℤ)+1 ≤ (2*(n : ℤ)+1)*k := by nlinarith
      nlinarith [hd]
    · by_cases h₁ : k < 0
      · have hd : (2*(n : ℤ)+1)*k ≤ -(2*(n : ℤ)+1) := by nlinarith
        nlinarith [hd]
      · omega
  simp [hk, oddShift_zero]

private lemma band_minimum (n : ℕ) (v : Vertex) (hv : inBand n v) (k : ℤ) :
    potential v ≤ potential (oddShift n k v) := by
  have hp : (0 : ℤ) < 2*(n : ℤ)+1 := by omega
  by_cases hk : k = 0
  · simp only [hk, oddShift_zero, le_refl]
  rcases v with ⟨b, i, j⟩
  by_cases hk' : 0 < k
  · have hd₁ : (n : ℤ) ≤ (n : ℤ)*k := by nlinarith
    have hd₂ : (n : ℤ)+1 ≤ ((n : ℤ)+1)*k := by nlinarith
    cases b <;> dsimp [inBand, lower] at hv <;>
      dsimp [potential, oddShift, TeaCoordinationSequence.residual] <;> omega
  · have hkneg : k ≤ -1 := by omega
    have hd₁ : (n : ℤ)*k ≤ -(n : ℤ) := by nlinarith
    have hd₂ : ((n : ℤ)+1)*k ≤ -((n : ℤ)+1) := by nlinarith
    cases b <;> dsimp [inBand, lower] at hv <;>
      dsimp [potential, oddShift, TeaCoordinationSequence.residual] <;> omega

private abbrev Rep (n : ℕ) := {v : Vertex // inBand n v}

private def repEquiv (n : ℕ) : Cylinder n ≃ Rep n where
  toFun := Quotient.lift (fun v => ⟨normal n v, normal_band n v⟩) (by
    intro u v h
    apply Subtype.ext
    exact band_unique n (normal_band n u) (normal_band n v)
      ((normal_class n u).trans ((Quotient.sound h).trans (normal_class n v).symm)))
  invFun v := Quotient.mk _ v.1
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h v => exact normal_class n v
  right_inv v := Subtype.ext (band_unique n (normal_band n v.1) v.2 (normal_class n v.1))

private lemma rep_distance (n : ℕ) (v : Rep n) :
    (cylinderGraph n).dist (origin n) (Quotient.mk _ v.1) = potential v.1 := by
  obtain ⟨w, hw, hp⟩ := quotient_minimum (cylinderGraph n) (projectHom n) Quotient.mk_surjective
    (lift_edge n) (Quotient.mk _ v.1)
  obtain ⟨k, hk⟩ := Quotient.exact hw.symm
  apply le_antisymm (quotient_upper n v.1)
  rw [← hp, ← hk]
  exact band_minimum n v.1 v.2 k

private def shellEquiv (n m : ℕ) :
    {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m} ≃
      {v : Rep n // potential v.1 = m} :=
  ((repEquiv n).symm.subtypeEquiv (fun v => by
    change potential v.1 = m ↔ (cylinderGraph n).dist (origin n) (Quotient.mk _ v.1) = m
    rw [rep_distance n])).symm

private def evenShellEquiv (n k : ℕ) :
    {v : Rep n // potential v.1 = 2*k} ≃
      Σ s : Set.Icc (-(n : ℤ)) n, AFiber s.1 k where
  toFun v := by
    have hc : v.1.1.1 = false := by
      have h := v.2
      cases hb : v.1.1.1 <;> simp [potential, hb] at h ⊢; omega
    refine ⟨⟨v.1.1.2.1 + v.1.1.2.2, ?_⟩, ⟨v.1.1.2.1, ?_⟩⟩
    · have h := v.1.2
      dsimp [inBand, lower] at h
      rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      constructor <;> omega
    · have h := v.2
      have hr : 0 ≤ (TeaCoordinationSequence.residual v.1.1.2.1 v.1.1.2.2 0 0) := le_max_left _ _
      dsimp only [potential] at h
      rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have he : v.1.1.2.1 + v.1.1.2.2 - v.1.1.2.1 = v.1.1.2.2 := by omega
      dsimp only; rw [he]; omega
  invFun s :=
    ⟨⟨(false, s.2.1, s.1.1-s.2.1), by
      have hl := s.1.2.1
      have hu := s.1.2.2
      dsimp [inBand, lower]; constructor <;> omega⟩, by
        have h := s.2.2
        dsimp [potential]
        omega⟩
  left_inv v := by
    rcases v with ⟨⟨⟨b,i,j⟩,hv⟩,hp⟩
    cases b
    · apply Subtype.ext
      apply Subtype.ext
      change (false, i, i+j-i) = (false, i, j)
      congr 2; omega
    · dsimp [potential] at hp; omega
  right_inv s := by
    rcases s with ⟨⟨s,hs⟩,⟨i,hi⟩⟩
    apply Sigma.ext
    · apply Subtype.ext; dsimp; omega
    · refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr rfl
      dsimp only
      rw [show i+(s-i) = s by omega]

private def oddShellEquiv (n k : ℕ) :
    {v : Rep n // potential v.1 = 2*k+1} ≃
      Σ s : Set.Icc (-(n : ℤ)-1) (n-1), BFiber s.1 k where
  toFun v := by
    have hc : v.1.1.1 = true := by
      have h := v.2
      cases hb : v.1.1.1 <;> simp [potential, hb] at h ⊢; omega
    refine ⟨⟨v.1.1.2.1 + v.1.1.2.2, ?_⟩, ⟨v.1.1.2.1, ?_⟩⟩
    · have h := v.1.2
      dsimp [inBand, lower] at h
      rw [hc] at h
      simp only [↓reduceIte] at h
      constructor <;> omega
    · have h := v.2
      have hr : 0 ≤ (TeaCoordinationSequence.residual v.1.1.2.1 v.1.1.2.2 0 1) := le_max_left _ _
      dsimp only [potential] at h
      rw [hc] at h
      simp only [↓reduceIte] at h
      have he : v.1.1.2.1 + v.1.1.2.2 - v.1.1.2.1 = v.1.1.2.2 := by omega
      dsimp only; rw [he]; omega
  invFun s :=
    ⟨⟨(true, s.2.1, s.1.1-s.2.1), by
      have hl := s.1.2.1
      have hu := s.1.2.2
      dsimp [inBand, lower]; constructor <;> omega⟩, by
        have h := s.2.2
        dsimp [potential]
        omega⟩
  left_inv v := by
    rcases v with ⟨⟨⟨b,i,j⟩,hv⟩,hp⟩
    cases b
    · dsimp [potential] at hp; omega
    · apply Subtype.ext
      apply Subtype.ext
      change (true, i, i+j-i) = (true, i, j)
      congr 2; omega
  right_inv s := by
    rcases s with ⟨⟨s,hs⟩,⟨i,hi⟩⟩
    apply Sigma.ext
    · apply Subtype.ext; dsimp; omega
    · refine (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr rfl
      dsimp only
      rw [show i+(s-i) = s by omega]

private lemma finite_shell (n m : ℕ) :
    Finite {v : Cylinder n // (cylinderGraph n).dist (origin n) v = m} := by
  by_cases hm : m % 2 = 0
  · have he : m = 2*(m/2) := by omega
    rw [he]
    exact Finite.of_equiv _ ((shellEquiv n _).trans (evenShellEquiv n _)).symm
  · have he : m = 2*(m/2)+1 := by omega
    rw [he]
    exact Finite.of_equiv _ ((shellEquiv n _).trans (oddShellEquiv n _)).symm

private lemma even_card {n : ℕ} (k : ℕ) (hk : 0 < k) :
    c n (2*k) = if k < n then 6*k else if k = n then 6*n else 4*n+2 := by
  classical
  rw [c, Nat.card_congr ((shellEquiv n _).trans (evenShellEquiv n k)), Nat.card_sigma]
  rw [← Finset.sum_subtype (Finset.Icc (-(n : ℤ)) n) (by simp)
    (fun s => Nat.card (AFiber s k))]
  simp_rw [a_fiber_card _ k hk, Finset.sum_add_distrib]
  have hpred (s : ℤ) : (-(k : ℤ) < s ∧ s < k) ↔
      (1-(k : ℤ) ≤ s ∧ s ≤ k-1) := by omega
  simp_rw [hpred]
  rw [interval_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  split_ifs <;> omega

private lemma odd_card (n k : ℕ) :
    c n (2*k+1) = if k < n then 6*k+3 else if k = n then 5*n+2 else 4*n+2 := by
  classical
  rw [c, Nat.card_congr ((shellEquiv n _).trans (oddShellEquiv n k)), Nat.card_sigma]
  rw [← Finset.sum_subtype (Finset.Icc (-(n : ℤ)-1) (n-1)) (by simp)
    (fun s => Nat.card (BFiber s k))]
  simp_rw [b_fiber_card, Finset.sum_add_distrib]
  have hpred (s : ℤ) : (-(k : ℤ) ≤ s ∧ s < k) ↔
      (-(k : ℤ) ≤ s ∧ s ≤ k-1) := by omega
  simp_rw [hpred]
  rw [interval_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  split_ifs <;> omega

private lemma zero_card (n : ℕ) : c n 0 = 1 := by
  let S := {v : Cylinder n // (cylinderGraph n).dist (origin n) v = 0}
  let : Finite S := finite_shell n 0
  let : Unique S := {
    default := ⟨origin n, SimpleGraph.dist_self⟩
    uniq := by
      rintro ⟨v,hv⟩
      apply Subtype.ext
      exact ((quotient_reachable n v).dist_eq_zero_iff.mp hv).symm }
  let : Fintype S := Fintype.ofFinite S
  change Nat.card S = 1
  rw [Nat.card_eq_fintype_card, Fintype.card_unique]

private lemma count_formula (n m : ℕ) :
    (c n m : ℤ) = if m = 0 then 1 else if m < 2*n+1 then 3*(m : ℤ)
      else if m = 2*n+1 then 5*(n : ℤ)+2 else 4*(n : ℤ)+2 := by
  by_cases hz : m = 0
  · subst m; simp [zero_card n]
  by_cases hm : m % 2 = 0
  · have he : m = 2*(m/2) := by omega
    rw [he, even_card (m/2) (by omega)]
    split_ifs <;>
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> omega
  · have he : m = 2*(m/2)+1 := by omega
    rw [he, odd_card]
    split_ifs
    all_goals simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    all_goals first | contradiction | omega

set_option maxHeartbeats 2000000 in
/-- The registered identity for every odd cylinder width, with denominators cleared. -/
theorem result : ∀ n : ℕ,
    (1 - X)^2 * (PowerSeries.mk fun m => (c n m : ℤ)) =
      (1 - X) * (1 + 2*X - C ((n : ℤ)-2)*X^(2*n+1) - C (n : ℤ)*X^(2*n+2)) +
        3*X^2 - 3*X^(2*n+1) := by
  intro n
  let S : PowerSeries ℤ := PowerSeries.mk fun m => (c n m : ℤ)
  have hs : S - 2*(X^1*S) + X^2*S =
      1 + X + X^2 - C ((n : ℤ)+1)*X^(2*n+1) - 2*X^(2*n+2) +
        C (n : ℤ)*X^(2*n+3) := by
    ext m
    simp only [map_add (coeff m), map_sub (coeff m), coeff_ofNat_mul, coeff_X_pow_mul', S, coeff_mk,
      coeff_one, coeff_X, coeff_X_pow, coeff_C_mul]
    simp_rw [count_formula]
    by_cases hn0 : n = 0
    · subst n
      have hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m := by omega
      rcases hm with rfl | rfl | rfl | hm <;> simp (disch := omega); omega
    have hn' : 0 < n := by omega
    by_cases hm : m < 3
    · have hc : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hc with rfl | rfl | rfl <;> simp (disch := omega) <;> omega
    by_cases h₀ : m < 2*n+1
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
    · by_cases h₁ : m = 2*n+1
      · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
      · by_cases h₂ : m = 2*n+2
        · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
        · by_cases h₃ : m = 2*n+3
          · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
          · simp (disch := omega) only [ite_eq_left, ite_eq_right]; omega
  have h₁ : (X : PowerSeries ℤ)^(2*n+2) = X^(2*n+1)*X := by rw [pow_succ]
  have h₂ : (X : PowerSeries ℤ)^(2*n+3) = X^(2*n+1)*X^2 := by
    rw [← pow_add]
  change (1-X)^2*S = _
  calc
    _ = S - 2*(X^1*S) + X^2*S := by ring
    _ = 1 + X + X^2 - C ((n : ℤ)+1)*X^(2*n+1) - 2*X^(2*n+2) +
        C (n : ℤ)*X^(2*n+3) := hs
    _ = (1 - X) * (1 + 2*X - C ((n : ℤ)-2)*X^(2*n+1) - C (n : ℤ)*X^(2*n+2)) +
        3*X^2 - 3*X^(2*n+1) := by
      simp only [map_add, map_sub, map_natCast, map_one, map_ofNat, h₁, h₂]
      ring

end D5.S3.StatisticalMechanics.HoneycombOddCylinderCoordination
