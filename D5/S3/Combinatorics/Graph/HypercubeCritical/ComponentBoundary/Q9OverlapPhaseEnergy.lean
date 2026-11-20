/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Seven-direction energy bound for a phase of two balanced cubic cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! A phase of the intersection has a separate set of exit vertices in each parent.
The norm of its signed indicator under the seven retained flips pays for the
squared internal degrees and both sets of exit incidences. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OverlapPhaseEnergy

open scoped Classical BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply IsSwitching switchingVector)
open BalancedCubeGirth (gamma_anticommute)
open BalancedCubeComponentBoundary (directions regular_directions)
open private directions_card mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private switching_sq from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private gamma_square from D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
open private huangMatrix huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/-- The vertices where the two switching functions have relative sign `ε`. -/
def phase (A B : Finset (Q 9)) (σ τ : Q 9 → ℝ) (ε : ℝ) : Finset (Q 9) :=
  (A ∩ B).filter fun x => σ x = ε * τ x

/-- The degree sum in the cube graph induced on `L`. -/
def degreeSum (L : Finset (Q 9)) : ℕ :=
  ∑ x ∈ L, (directions L x).card

/-- The number of vertices of degree `j` in the cube graph induced on `L`. -/
def degreeCount (L : Finset (Q 9)) (j : ℕ) : ℕ :=
  (L.filter fun x => (directions L x).card = j).card

private def retainedFlips (a b : Fin 9) : Finset (Fin 9) :=
  Finset.univ \ {a, b}

private def restrictedOperator {n : ℕ} (s : Finset (Fin n)) (z : Q n → ℝ) : Q n → ℝ :=
  ∑ i ∈ s, gamma i z

private theorem restrictedOperator_square {n : ℕ} (s : Finset (Fin n)) (z : Q n → ℝ) :
    restrictedOperator s (restrictedOperator s z) = (s.card : ℝ) • z := by
  unfold restrictedOperator
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    simp only [map_add, Finset.sum_add_distrib, gamma_square]
    rw [ih, map_sum]
    have hanti : (∑ j ∈ s, gamma a (gamma j z)) =
        -(∑ j ∈ s, gamma j (gamma a z)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj => gamma_anticommute (fun h : a = j => ha (h.symm ▸ hj)) z
    rw [hanti]
    abel

private theorem restrictedOperator_symm {n : ℕ} (s : Finset (Fin n)) (z w : Q n → ℝ) :
    (∑ x, z x * restrictedOperator s w x) = ∑ x, restrictedOperator s z x * w x := by
  simp only [restrictedOperator, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let equiv : Q n ≃ Q n :=
    (show Function.Involutive (fun x : Q n => flip x i) from
      fun x => BalancedCriticalSpectrum.flip_flip x i).toPerm _
  apply Fintype.sum_equiv equiv
  intro x
  change z x * gamma i w x = gamma i z (flip x i) * w (flip x i)
  rw [gamma_apply, gamma_apply, BalancedCriticalSpectrum.flip_flip, huangMatrix_symmetric (flip x i) x]
  ring

private theorem indicator_energy {n : ℕ} {P L : Finset (Q n)} {σ : Q n → ℝ}
    (hs : IsSwitching P σ) (hL : L ⊆ P) (s : Finset (Fin n)) :
    (∑ x, restrictedOperator s (switchingVector L σ) x ^ 2) = (s.card : ℝ) * L.card := by
  let z := switchingVector L σ
  change (∑ x, restrictedOperator s z x ^ 2) = _
  simp only [pow_two]
  rw [← restrictedOperator_symm s z (restrictedOperator s z), restrictedOperator_square]
  have hp (x : Q n) : z x * ((s.card : ℝ) • z) x = if x ∈ L then (s.card : ℝ) else 0 := by
    by_cases hx : x ∈ L
    · have hunit := switching_sq hs (hL hx)
      simp only [z, switchingVector, hx, ite_true, Pi.smul_apply, smul_eq_mul]
      calc
        σ x * ((s.card : ℝ) * σ x) = (s.card : ℝ) * σ x ^ 2 := by ring
        _ = _ := by rw [hunit, mul_one]
    · simp [z, switchingVector, hx]
  simp_rw [hp]
  simp [mul_comm]

private theorem phase_closed {A B : Finset (Q 9)} {σ τ : Q 9 → ℝ} {ε : ℝ}
    (hσ : IsSwitching A σ) (hτ : IsSwitching B τ) {x y : Q 9}
    (hx : x ∈ phase A B σ τ ε) (hy : y ∈ A ∩ B) (hxy : (hypercube 9).Adj x y) :
    y ∈ phase A B σ τ ε := by
  obtain ⟨hx', hrel⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx'
  obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
  have he := (hσ.2 x hxA y hyA hxy).symm.trans (hτ.2 x hxB y hyB hxy)
  have hτx := switching_sq hτ hxB
  have hσx := switching_sq hσ hxA
  refine Finset.mem_filter.mpr ⟨hy, ?_⟩
  calc
    σ y = σ x * (σ x * σ y) := by rw [← mul_assoc, ← pow_two, hσx, one_mul]
    _ = ε * τ y := by rw [he, hrel]; rw [← mul_assoc, mul_assoc ε, ← pow_two, hτx, mul_one]

private theorem restricted_directions {L P : Finset (Q 9)}
    {s : Finset (Fin 9)} (havoid : ∀ y ∈ L, directions P y ⊆ s) {x : Q 9} (hx : x ∈ P) :
    directions L x ⊆ s := by
  intro i hi
  have hy := (mem_directions L x i).mp hi
  apply havoid (flip x i) hy
  exact (mem_directions P (flip x i) i).mpr (by simpa using hx)

private theorem energy_at_parent {L P : Finset (Q 9)} {σ ρ : Q 9 → ℝ} {t : ℝ}
    (hLP : L ⊆ P) (hρ : IsSwitching P ρ) (ht : t ^ 2 = 1)
    (hrel : ∀ y ∈ L, σ y = t * ρ y) {s : Finset (Fin 9)}
    (havoid : ∀ y ∈ L, directions P y ⊆ s) {x : Q 9} (hx : x ∈ P) :
    restrictedOperator s (switchingVector L σ) x ^ 2 = ((directions L x).card : ℝ) ^ 2 := by
  have hsub := restricted_directions havoid hx
  have hterm (i : Fin 9) :
      gamma i (switchingVector L σ) x = if flip x i ∈ L then t * ρ x else 0 := by
    rw [gamma_apply]
    by_cases hi : flip x i ∈ L
    · rw [ite_eq_left hi, hρ.2 x hx _ (hLP hi) (flip_adj x i)]
      simp only [switchingVector, hi, ite_true, hrel _ hi]
      calc
        ρ x * ρ (flip x i) * (t * ρ (flip x i)) =
            (t * ρ x) * ρ (flip x i) ^ 2 := by ring
        _ = _ := by rw [switching_sq hρ (hLP hi), mul_one]
    · simp [switchingVector, hi]
  have hf : s.filter (fun i => flip x i ∈ L) = directions L x := by
    ext i
    rw [Finset.mem_filter, mem_directions]
    exact ⟨And.right, fun hi => ⟨hsub ((mem_directions L x i).mpr hi), hi⟩⟩
  have hop : restrictedOperator s (switchingVector L σ) x =
      (t * ρ x) * (directions L x).card := by
    simp only [restrictedOperator, Finset.sum_apply, hterm]
    rw [← Finset.sum_filter, hf]
    simp [mul_comm]
  rw [hop, mul_pow, mul_pow, ht, switching_sq hρ hx, one_mul, one_mul]

private theorem exit_incidence (L E : Finset (Q 9)) :
    (∑ x ∈ E, (directions L x).card) = ∑ x ∈ L, (directions E x).card := by
  simp only [directions_card, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [show (hypercube 9).Adj y x ↔ (hypercube 9).Adj x y from ⟨fun h => h.symm, fun h => h.symm⟩]

private theorem exit_degree {L P E : Finset (Q 9)}
    (hr : ((hypercube 9).induce (P : Set (Q 9))).IsRegularOfDegree 3)
    (hLP : L ⊆ P) (hEP : E ⊆ P) (hLE : Disjoint L E) {x : Q 9} (hx : x ∈ L)
    (hcover : ∀ i, flip x i ∈ P → flip x i ∈ L ∨ flip x i ∈ E) :
    (directions L x).card + (directions E x).card = 3 := by
  have hu : directions L x ∪ directions E x = directions P x := by
    ext i
    simp only [Finset.mem_union, mem_directions]
    exact ⟨fun h => h.elim (fun hl => hLP hl) (fun he => hEP he), hcover i⟩
  have hd : Disjoint (directions L x) (directions E x) := by
    simp only [Finset.disjoint_left, mem_directions]
    exact fun _ hl he => Finset.disjoint_left.mp hLE hl he
  rw [← Finset.card_union_of_disjoint hd, hu, regular_directions P hr (hLP hx)]

private theorem exit_energy {L E : Finset (Q 9)} {u : Q 9 → ℝ}
    (hu : ∀ x ∈ E, u x ^ 2 = ((directions L x).card : ℝ) ^ 2) :
    (∑ x ∈ L, ((directions E x).card : ℝ)) ≤ ∑ x ∈ E, u x ^ 2 := by
  have hcount := congrArg (fun n : ℕ => (n : ℝ)) (exit_incidence L E)
  simp only [Nat.cast_sum] at hcount
  rw [← hcount]
  apply Finset.sum_le_sum
  intro x hx
  rw [hu x hx]
  exact_mod_cast Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (directions L x).card

/-- For either relative-sign phase, the seven retained directions give
`3 * degreeSum + 6 * degreeCount 0 + 2 * degreeCount 1 ≤ 7 * card`. -/
theorem phase_energy_bound (A B : Finset (Q 9)) (σ τ : Q 9 → ℝ) (ε : ℝ)
    (hε : ε ^ 2 = 1) (a b : Fin 9) (hab : a ≠ b)
    (hA : ((hypercube 9).induce (A : Set (Q 9))).IsRegularOfDegree 3)
    (hB : ((hypercube 9).induce (B : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching A σ) (hτ : IsSwitching B τ)
    (havoidA : ∀ x ∈ phase A B σ τ ε, ∀ i ∈ ({a, b} : Finset (Fin 9)), flip x i ∉ A)
    (havoidB : ∀ x ∈ phase A B σ τ ε, ∀ i ∈ ({a, b} : Finset (Fin 9)), flip x i ∉ B) :
    let L := phase A B σ τ ε
    3 * degreeSum L + 6 * degreeCount L 0 + 2 * degreeCount L 1 ≤ 7 * L.card := by
  let L := phase A B σ τ ε
  let E := A \ B
  let F := B \ A
  let s := retainedFlips a b
  let u := restrictedOperator s (switchingVector L σ)
  have hLA : L ⊆ A := fun _ hx => (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  have hLB : L ⊆ B := fun _ hx => (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
  have hLE : Disjoint L E :=
    Finset.disjoint_left.mpr fun _ hx he => (Finset.mem_sdiff.mp he).2 (hLB hx)
  have hLF : Disjoint L F :=
    Finset.disjoint_left.mpr fun _ hx hf => (Finset.mem_sdiff.mp hf).2 (hLA hx)
  have hEF : Disjoint E F :=
    Finset.disjoint_left.mpr fun _ he hf => (Finset.mem_sdiff.mp hf).2 (Finset.mem_sdiff.mp he).1
  have hcoverA (x : Q 9) (hx : x ∈ L) (i : Fin 9) (hi : flip x i ∈ A) :
      flip x i ∈ L ∨ flip x i ∈ E := by
    by_cases hy : flip x i ∈ B
    · exact Or.inl (phase_closed hσ hτ hx (Finset.mem_inter.mpr ⟨hi, hy⟩) (flip_adj x i))
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hi, hy⟩)
  have hcoverB (x : Q 9) (hx : x ∈ L) (i : Fin 9) (hi : flip x i ∈ B) :
      flip x i ∈ L ∨ flip x i ∈ F := by
    by_cases hy : flip x i ∈ A
    · exact Or.inl (phase_closed hσ hτ hx (Finset.mem_inter.mpr ⟨hy, hi⟩) (flip_adj x i))
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hi, hy⟩)
  have hdirA (x : Q 9) (hx : x ∈ L) : directions A x ⊆ s := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun habi =>
      havoidA x hx i habi ((mem_directions A x i).mp hi)⟩
  have hdirB (x : Q 9) (hx : x ∈ L) : directions B x ⊆ s := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun habi =>
      havoidB x hx i habi ((mem_directions B x i).mp hi)⟩
  have huA (x : Q 9) (hx : x ∈ A) :
      u x ^ 2 = ((directions L x).card : ℝ) ^ 2 :=
    energy_at_parent hLA hσ (t := 1) (by norm_num) (fun y _ => (one_mul (σ y)).symm) hdirA hx
  have huB (x : Q 9) (hx : x ∈ B) :
      u x ^ 2 = ((directions L x).card : ℝ) ^ 2 :=
    energy_at_parent hLB hτ hε (fun _ hy => (Finset.mem_filter.mp hy).2) hdirB hx
  have hEP : E ⊆ A := fun _ h => (Finset.mem_sdiff.mp h).1
  have hFP : F ⊆ B := fun _ h => (Finset.mem_sdiff.mp h).1
  have hs : s.card = 7 := by
    change ((Finset.univ : Finset (Fin 9)) \ {a, b}).card = 7
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hab]
  have htotal : (∑ x, u x ^ 2) = 7 * (L.card : ℝ) := by
    simpa [u, hs] using indicator_energy hσ hLA s
  have hregions :
      (∑ x ∈ L, u x ^ 2) + (∑ x ∈ E, u x ^ 2) + (∑ x ∈ F, u x ^ 2) ≤
        7 * (L.card : ℝ) := by
    rw [← Finset.sum_union hLE, ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hLF, hEF⟩)]
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => sq_nonneg (u x))
  have hlocal (x : Q 9) (hx : x ∈ L) :
      3 * ((directions L x).card : ℝ) +
        (if (directions L x).card = 0 then 6 else 0) +
        (if (directions L x).card = 1 then 2 else 0) =
      u x ^ 2 + (directions E x).card + (directions F x).card := by
    have ha := exit_degree hA hLA hEP hLE hx (hcoverA x hx)
    have hb := exit_degree hB hLB hFP hLF hx (hcoverB x hx)
    have haR : ((directions L x).card : ℝ) + (directions E x).card = 3 := by exact_mod_cast ha
    have hbR : ((directions L x).card : ℝ) + (directions F x).card = 3 := by exact_mod_cast hb
    have he : ((directions E x).card : ℝ) + (directions F x).card =
        6 - 2 * (directions L x).card := by linarith only [haR, hbR]
    rw [huA x (hLA hx), add_assoc _ ((directions E x).card : ℝ) ((directions F x).card : ℝ), he]
    have hd : (directions L x).card ≤ 3 := by omega
    interval_cases h : (directions L x).card <;> norm_num [h]
  change 3 * degreeSum L + 6 * degreeCount L 0 + 2 * degreeCount L 1 ≤ 7 * L.card
  suffices hreal :
      (3 : ℝ) * degreeSum L + 6 * degreeCount L 0 + 2 * degreeCount L 1 ≤ 7 * L.card by
    exact_mod_cast hreal
  have ht := Finset.sum_congr rfl hlocal
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at ht
  rw [← Finset.sum_filter, ← Finset.sum_filter] at ht
  simp only [Finset.sum_const, nsmul_eq_mul] at ht
  simp only [degreeSum, degreeCount, Nat.cast_sum]
  rw [mul_comm 6, mul_comm 2, ht]
  have hExitA := exit_energy (L := L) (E := E) (fun x hx => huA x (hEP hx))
  have hExitB := exit_energy (L := L) (E := F) (fun x hx => huB x (hFP hx))
  exact (add_le_add (add_le_add le_rfl hExitA) hExitB).trans hregions

/-- The translation that toggles the two indicated axes. -/
def twoAxisTranslate (a b : Fin 9) : Equiv.Perm (Q 9) :=
  (show Function.Involutive (fun x : Q 9 => flip (flip x a) b) from by
    intro x
    change flip (flip (flip (flip x a) b) a) b = x
    rw [flip_comm (flip x a) b a, BalancedCriticalSpectrum.flip_flip,
      BalancedCriticalSpectrum.flip_flip]).toPerm _

private theorem translate_flip (a b : Fin 9) (x : Q 9) (i : Fin 9) :
    twoAxisTranslate a b (flip x i) = flip (twoAxisTranslate a b x) i := by
  change flip (flip (flip x i) a) b = flip (flip (flip x a) b) i
  rw [flip_comm x i a, flip_comm (flip x a) i b]

private theorem translate_regular (a b : Fin 9) (D : Finset (Q 9))
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3) :
    ((hypercube 9).induce (D.map (twoAxisTranslate a b).toEmbedding : Set (Q 9))).IsRegularOfDegree
      3 := by
  let g := twoAxisTranslate a b
  intro y
  obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.2
  change g x = y.1 at hxy
  have hd : directions (D.map g.toEmbedding) (g x) = directions D x := by
    ext i
    rw [mem_directions, mem_directions, ← translate_flip a b x i, Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  rw [← selected_neighbor_card y.2]
  have hf : (hypercube 9).neighborFinset y.1 ∩ D.map g.toEmbedding =
      (D.map g.toEmbedding).filter (fun z => (hypercube 9).Adj y.1 z) := by
    ext z
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [hf, ← directions_card, ← hxy, hd, regular_directions D hD hx]

private theorem translate_switching (a b : Fin 9) {D : Finset (Q 9)} {τ : Q 9 → ℝ}
    (hτ : IsSwitching D τ) : ∃ τ', IsSwitching (D.map (twoAxisTranslate a b).toEmbedding) τ' := by
  let g := twoAxisTranslate a b
  obtain ⟨θ, hθ, hedge, _⟩ := HuangCubeCovariance.exists_signed_covariance g
    (Equiv.refl (Fin 9)) (translate_flip a b)
  refine ⟨fun x => θ (g.symm x) * τ (g.symm x), ?_, ?_⟩
  · intro x hx
    have hxD : g.symm x ∈ D := Finset.mem_map_equiv.mp hx
    rcases hθ (g.symm x) with h | h <;> rcases hτ.1 _ hxD with k | k <;> norm_num [h, k]
  · intro x hx y hy hxy
    have hxD := Finset.mem_map_equiv.mp hx
    have hyD := Finset.mem_map_equiv.mp hy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    let z := g.symm x
    have hzx : g z = x := g.apply_symm_apply x
    have hzy : g (flip z i) = flip x i := by rw [translate_flip a b, hzx]
    rw [← hzx] at hxD
    rw [← hzy] at hyD
    rw [Equiv.symm_apply_apply] at hxD hyD
    rw [← hzy, ← hzx]
    simp only [Equiv.symm_apply_apply]
    rw [hedge z i, hτ.2 z hxD (flip z i) hyD (flip_adj z i)]
    ring

/-- Two nonadjacent balanced cubic supports admit the phase bound after translating
the second support by any pair of distinct axes. -/
theorem translated_phase_energy_bound (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (a b : Fin 9) (hab : a ≠ b)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) :
    let D' := D.map (twoAxisTranslate a b).toEmbedding
    ∃ τ', IsSwitching D' τ' ∧ ∀ ε : ℝ, ε ^ 2 = 1 →
      let L := phase C D' σ τ' ε
      3 * degreeSum L + 6 * degreeCount L 0 + 2 * degreeCount L 1 ≤ 7 * L.card := by
  let g := twoAxisTranslate a b
  let D' := D.map g.toEmbedding
  have hmem (x : Q 9) : x ∈ D' ↔ g x ∈ D := Finset.mem_map_equiv
  have hleft (x : Q 9) : g (flip x a) = flip x b := by
    change flip (flip (flip x a) a) b = _
    rw [BalancedCriticalSpectrum.flip_flip]
  have hright (x : Q 9) : g (flip x b) = flip x a := by
    change flip (flip (flip x b) a) b = _
    rw [flip_comm x b a, BalancedCriticalSpectrum.flip_flip]
  obtain ⟨τ', hτ'⟩ := translate_switching a b hτ
  refine ⟨τ', hτ', fun ε hε =>
    phase_energy_bound C D' σ τ' ε hε a b hab hC (translate_regular a b D hD) hσ hτ' ?_ ?_⟩
  · intro x hx i hi hflip
    have hxD := (hmem x).mp (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hsep _ hflip _ hxD (flip_adj (flip x _) b)
    · apply hsep _ hflip _ hxD
      change (hypercube 9).Adj (flip x i) (flip (flip x a) i)
      rw [flip_comm x a i]
      exact flip_adj _ _
  · intro x hx i hi hflip
    have hxC := (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    have hyD := (hmem _).mp hflip
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hsep _ hxC _ hyD (by rw [hleft]; exact flip_adj _ _)
    · exact hsep _ hxC _ hyD (by rw [hright]; exact flip_adj _ _)

#print axioms phase_energy_bound
#print axioms translated_phase_energy_bound

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OverlapPhaseEnergy
