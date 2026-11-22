/- GID: D5/S3/Geometry/KozakiKakeiPrimitive
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiPrimitive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two actual affine coefficients of the frieze level equation are relatively prime. -/
import D5.S3.Geometry.KozakiKakeiAffine

namespace D5.S3.Geometry.KozakiKakei
open MvPolynomial
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

def zeroEdge {m : ℕ} (hm : 2 ≤ m) : Fin m := ⟨0, by omega⟩

def nextCoord {m : ℕ} (hm : 2 ≤ m) : Rest (first hm) :=
  ⟨second hm, by intro h; have := congrArg Fin.val h; contradiction⟩

def lastCoord {m : ℕ} (hm : 2 ≤ m) : Rest (first hm) :=
  ⟨last hm, by intro h; have h' := congrArg Fin.val h; change 2*m-1=0 at h'; omega⟩

def middleCoord {m : ℕ} (hm : 2 ≤ m) : Rest (first hm) :=
  ⟨third hm, by intro h; have := congrArg Fin.val h; contradiction⟩

def oddRest {m : ℕ} (hm : 2 ≤ m) (i : {i : Fin m // i ≠ zeroEdge hm})
    (c : Bool) : Rest (first hm) :=
  ⟨oddVertex (i.val, c), (remainingVertex (oddMatching m) false i c).property⟩

def evenRest {m : ℕ} (hm : 2 ≤ m) (i : {i : Fin m // i ≠ zeroEdge hm})
    (c : Bool) : Rest (first hm) :=
  ⟨evenVertex (i.val, c), (remainingVertex (evenMatching m) false i c).property⟩

def U {m : ℕ} (hm : 2 ≤ m) : Coeff (first hm) :=
  ∏ i : {i : Fin m // i ≠ zeroEdge hm}, diff (oddRest hm i false) (oddRest hm i true)

def V {m : ℕ} (hm : 2 ≤ m) : Coeff (first hm) :=
  ∏ i : {i : Fin m // i ≠ zeroEdge hm}, diff (evenRest hm i false) (evenRest hm i true)

def A {m : ℕ} (hm : 2 ≤ m) : Coeff (first hm) := U hm - V hm

def B {m : ℕ} (hm : 2 ≤ m) : Coeff (first hm) :=
  X (lastCoord hm) * V hm - X (nextCoord hm) * U hm

theorem isolate_F {m : ℕ} (hm : 2 ≤ m) :
    isolate (first hm) (F m) = Polynomial.C (A hm) * Polynomial.X + Polynomial.C (B hm) := by
  have he : isolate (first hm) (matchingPolynomial (evenMatching m)) =
      Polynomial.C (-V hm) * Polynomial.X + Polynomial.C (X (lastCoord hm) * V hm) :=
    matching_isolate_left (evenMatching m) (zeroEdge hm)
  have ho : isolate (first hm) (matchingPolynomial (oddMatching m)) =
      Polynomial.C (-U hm) * Polynomial.X + Polynomial.C (X (nextCoord hm) * U hm) :=
    matching_isolate_left (oddMatching m) (zeroEdge hm)
  rw [F, map_sub, he, ho, A, B, map_sub, map_sub, map_neg, map_neg]
  ring

private theorem tailEdge_pos {m : ℕ} {hm : 2 ≤ m}
    (i : {i : Fin m // i ≠ zeroEdge hm}) : i.val.val ≠ 0 := by
  intro h
  exact i.property (Fin.ext h)

private theorem eval_U {m : ℕ} (hm : 2 ≤ m) (t : Rest (first hm) → ℂ) :
    eval t (U hm) = ∏ i : {i : Fin m // i ≠ zeroEdge hm},
      (t (oddRest hm i true) - t (oddRest hm i false)) := by
  simp [U, map_prod, diff]

private theorem eval_V {m : ℕ} (hm : 2 ≤ m) (t : Rest (first hm) → ℂ) :
    eval t (V hm) = ∏ i : {i : Fin m // i ≠ zeroEdge hm},
      (t (evenRest hm i true) - t (evenRest hm i false)) := by
  simp [V, map_prod, diff]

private def oneEdge {m : ℕ} (hm : 2 ≤ m) : {i : Fin m // i ≠ zeroEdge hm} :=
  ⟨⟨1, by omega⟩, by
    intro h
    have h' := congrArg Fin.val h
    contradiction⟩

private theorem tail_four_unique (i : {i : Fin 2 // i ≠ zeroEdge (by decide)}) :
    i = oneEdge (show 2 ≤ 2 by decide) := by
  apply Subtype.ext
  apply Fin.ext
  have h := tailEdge_pos i
  have hi := i.val.isLt
  change i.val.val = 1
  omega

theorem signed_four_coefficient :
    A (show 2 ≤ 2 by decide) =
      X (lastCoord (show 2 ≤ 2 by decide)) + X (nextCoord (show 2 ≤ 2 by decide)) -
        2 * X (middleCoord (show 2 ≤ 2 by decide)) := by
  let hm : 2 ≤ 2 := le_rfl
  let e := oneEdge hm
  have hu : U hm = diff (oddRest hm e false) (oddRest hm e true) := by
    unfold U
    apply Finset.prod_eq_single e
    · intro j _ hj
      exact (hj (tail_four_unique j)).elim
    · simp
  have hv : V hm = diff (evenRest hm e false) (evenRest hm e true) := by
    unfold V
    apply Finset.prod_eq_single e
    · intro j _ hj
      exact (hj (tail_four_unique j)).elim
    · simp
  have ho₁ : oddRest hm e false = middleCoord hm := rfl
  have he₁ : evenRest hm e false = nextCoord hm := rfl
  have he₂ : evenRest hm e true = middleCoord hm := rfl
  change A hm = _
  rw [A, hu, hv, ho₁, show oddRest hm e true = lastCoord hm from rfl, he₁, he₂]
  unfold diff
  ring

private theorem disjoint_tail_edges {m : ℕ} (hm : 2 ≤ m)
    (i j : {i : Fin m // i ≠ zeroEdge hm}) :
    ¬ ((evenVertex (j.val, false) = oddVertex (i.val, false) ∧
        evenVertex (j.val, true) = oddVertex (i.val, true)) ∨
       (evenVertex (j.val, false) = oddVertex (i.val, true) ∧
        evenVertex (j.val, true) = oddVertex (i.val, false))) := by
  have hj := tailEdge_pos j
  have hi := tailEdge_pos i
  intro h
  rcases h with h | h
  · have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    simp [evenVertex, oddVertex, hj] at h₁ h₂
    omega
  · have h₁ := congrArg Fin.val h.1
    have h₂ := congrArg Fin.val h.2
    simp [evenVertex, oddVertex, hj] at h₁ h₂
    omega

private theorem tails_no_common_prime {m : ℕ} (hm : 2 ≤ m)
    {p : Coeff (first hm)} (hp : Prime p) (hU : p ∣ U hm) (hV : p ∣ V hm) : False := by
  unfold U at hU
  unfold V at hV
  obtain ⟨i, _, hi⟩ := (hp.dvd_finsetProd_iff _).mp hU
  obtain ⟨j, _, hj⟩ := (hp.dvd_finsetProd_iff _).mp hV
  have odd_ne : (oddMatching m) (i.val, false) ≠ (oddMatching m) (i.val, true) := by
    intro h
    have h' := congrArg Prod.snd ((oddMatching m).injective h)
    cases h'
  have even_ne : (evenMatching m) (j.val, false) ≠ (evenMatching m) (j.val, true) := by
    intro h
    have h' := congrArg Prod.snd ((evenMatching m).injective h)
    cases h'
  have hprime : Prime (diff (oddRest hm i false) (oddRest hm i true)) :=
    diff_prime (fun h => odd_ne (congrArg (fun x : Rest (first hm) => x.val) h))
  have hdiv := ((hp.associated_of_dvd hprime hi).dvd_dvd).2.trans hj
  apply diff_not_dvd_of_edges_ne (fun h => even_ne (congrArg (fun x : Rest (first hm) => x.val) h)) ?_ hdiv
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact disjoint_tail_edges hm i j
      (Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩)
  · exact disjoint_tail_edges hm i j
      (Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩)

private def collapsed {m : ℕ} {hm : 2 ≤ m} (i : Rest (first hm)) : ℂ :=
  ((if i.val.val = 2*m-1 then 1 else if i.val.val = 3 then 2 else i.val.val) : ℕ)

private theorem collapsed_neighbors {m : ℕ} (hm : 2 ≤ m) :
    collapsed (nextCoord hm) = collapsed (lastCoord hm) := by
  have hn : 1 ≠ 2*m-1 := by omega
  simp [collapsed, nextCoord, lastCoord, second, last, hn]

private theorem collapse_large {m : ℕ} (hm : 2 ≤ m) (hlarge : 4 ≤ m) :
    eval collapsed (A hm) ≠ 0 := by
  have hU : eval collapsed (U hm) = 0 := by
    rw [eval_U]
    refine Finset.prod_eq_zero_iff.mpr ⟨oneEdge hm, Finset.mem_univ _, ?_⟩
    have h₂ : 2 ≠ 2*m-1 := by omega
    have h₃ : 3 ≠ 2*m-1 := by omega
    simp [collapsed, oddRest, oneEdge, oddVertex, h₂, h₃]
  have hV : eval collapsed (V hm) ≠ 0 := by
    rw [eval_V]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr ?_
    have hi := i.val.isLt
    have hi0 := tailEdge_pos i
    have hr : 2 * i.val.val ≠ 2*m-1 := by omega
    have hl : 2 * i.val.val - 1 ≠ 2*m-1 := by omega
    have hh : 2 * i.val.val ≠ 3 := by omega
    unfold collapsed
    apply Nat.cast_injective.ne
    have hlVal : (evenRest hm i false).val.val = 2 * i.val.val - 1 := by
      simp [evenRest, evenVertex, hi0]
    have hrVal : (evenRest hm i true).val.val = 2 * i.val.val := by
      simp [evenRest, evenVertex, hi0]
    rw [hlVal, hrVal, ite_eq_right hr, ite_eq_right hh, ite_eq_right hl]
    split <;> omega
  simp [A, hU, hV]

private theorem collapse_small : eval collapsed (A (show 2 ≤ 2 by decide)) ≠ 0 := by
  rw [signed_four_coefficient]
  norm_num [collapsed, nextCoord, lastCoord, middleCoord, second, last, third]

theorem primitive_coefficients {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3) :
    A hm ≠ 0 ∧ IsRelPrime (A hm) (B hm) := by
  have hspec : eval collapsed (A hm) ≠ 0 := by
    by_cases h2 : m = 2
    · subst m
      exact collapse_small
    · exact collapse_large hm (by omega)
  have hA : A hm ≠ 0 := by
    intro h
    exact hspec (by rw [h, map_zero])
  refine ⟨hA, (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hA).mpr ?_⟩
  intro p hpA hpB hp
  have h1 : B hm + X (nextCoord hm) * A hm = diff (nextCoord hm) (lastCoord hm) * V hm := by
    unfold A B diff
    ring
  have h2 : B hm + X (lastCoord hm) * A hm = diff (nextCoord hm) (lastCoord hm) * U hm := by
    unfold A B diff
    ring
  have hdV : p ∣ diff (nextCoord hm) (lastCoord hm) * V hm := by
    rw [← h1]
    exact dvd_add hpB (dvd_mul_of_dvd_right hpA _)
  have hdU : p ∣ diff (nextCoord hm) (lastCoord hm) * U hm := by
    rw [← h2]
    exact dvd_add hpB (dvd_mul_of_dvd_right hpA _)
  have hd : p ∣ diff (nextCoord hm) (lastCoord hm) := by
    rcases hp.dvd_mul.mp hdV with h | h
    · exact h
    · rcases hp.dvd_mul.mp hdU with h' | h'
      · exact h'
      · exact (tails_no_common_prime hm hp h' h).elim
  have hne : nextCoord hm ≠ lastCoord hm := by
    intro h
    have h' := congrArg (fun j : Rest (first hm) => j.val.val) h
    change 1 = 2*m-1 at h'
    omega
  have hdA := ((hp.associated_of_dvd (diff_prime hne) hd).dvd_dvd).2.trans hpA
  have he := map_dvd (eval collapsed) hdA
  rw [diff, map_sub, eval_X, eval_X, collapsed_neighbors hm, sub_self, zero_dvd_iff] at he
  exact hspec he

theorem A_not_unit {m : ℕ} (hm : 2 ≤ m) : ¬ IsUnit (A hm) := by
  intro h
  have hu := h.map (eval (fun _ => 0))
  have hU : eval (fun _ => 0) (U hm) = 0 := by
    rw [eval_U]
    exact Finset.prod_eq_zero_iff.mpr ⟨oneEdge hm, Finset.mem_univ _, sub_self _⟩
  have hV : eval (fun _ => 0) (V hm) = 0 := by
    rw [eval_V]
    exact Finset.prod_eq_zero_iff.mpr ⟨oneEdge hm, Finset.mem_univ _, sub_self _⟩
  rw [A, map_sub, hU, hV, sub_self] at hu
  exact not_isUnit_zero hu

end
end D5.S3.Geometry.KozakiKakei
