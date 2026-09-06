/- GID: D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Covers of dense product graphs refute every positive domination constant. -/

import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.AnnorCoverRefutation

open GraphCoverDomination

abbrev Vertex (r m : Nat) := Fin (r + 1) → Fin (m + 1)

/-- The categorical product of `r+1` copies of the complete graph on `m+1` vertices. -/
def productGraph (r m : Nat) : SimpleGraph (Vertex r m) where
  Adj v w := forall i, v i ≠ w i
  symm := ⟨fun _ _ h i => (h i).symm⟩
  loopless := ⟨fun _ h => h 0 rfl⟩

instance (r m : Nat) : DecidableRel (productGraph r m).Adj :=
  fun v w => inferInstanceAs (Decidable (forall i, v i ≠ w i))

theorem productGraph_regular (r m : Nat) :
    (productGraph r m).IsRegularOfDegree (m ^ (r + 1)) := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let e : (productGraph r m).neighborSet v ≃
      (forall i : Fin (r + 1), {x : Fin (m + 1) // v i ≠ x}) :=
    { toFun := fun w i => ⟨w.1 i, w.2 i⟩
      invFun := fun w => ⟨fun i => (w i).1, fun i => (w i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_pi]
  have hcard (i : Fin (r + 1)) :
      Fintype.card {x : Fin (m + 1) // v i ≠ x} = m := by
    rw [Fintype.card_subtype_compl (fun x => v i = x), Fintype.card_subtype_eq']
    simp
  simp_rw [hcard]
  simp

theorem productGraph_connected (r m : Nat) (hm : 2 ≤ m) :
    (productGraph r m).Connected := by
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨fun _ => 0, ?_⟩
  intro w
  have chooseValue (i : Fin (r + 1)) : ∃ x : Fin (m + 1), x ≠ 0 ∧ x ≠ w i := by
    have hcard : ({0, w i} : Finset (Fin (m + 1))).card <
        (Finset.univ : Finset (Fin (m + 1))).card := by
      have h := Finset.card_insert_le (0 : Fin (m + 1)) {w i}
      simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at *
      omega
    obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨x, by simpa using hx⟩
  choose u hu using chooseValue
  exact (show (productGraph r m).Adj (fun _ => 0) u from
    fun i => (hu i).1.symm).reachable.trans
    (show (productGraph r m).Adj u w from fun i => (hu i).2).reachable

theorem small_set_not_dominating {r m : Nat} (hm : r ≤ m)
    (D : Finset (Vertex r m)) (hD : D.card < r + 1) :
    ¬ (productGraph r m).IsDominating D := by
  classical
  let free : Fin (r + 1) := ⟨D.card, hD⟩
  let used : Finset (Fin (m + 1)) := D.image (fun w => w free)
  have hused : used.card < (Finset.univ : Finset (Fin (m + 1))).card := by
    have hi : used.card ≤ D.card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  let e := D.equivFin
  let v : Vertex r m := fun i =>
    if hi : i.val < D.card then (e.symm ⟨i.val, hi⟩).val i else b
  have hvfree : v free = b := by simp [v, free]
  have hvD : v ∉ D := by
    intro hv
    apply hb
    exact Finset.mem_image.mpr ⟨v, hv, hvfree⟩
  intro hdom
  rcases hdom v with hv | ⟨w, hw, hadj⟩
  · exact hvD hv
  · let j : Fin (r + 1) := ⟨(e ⟨w, hw⟩).val, (e ⟨w, hw⟩).isLt.trans hD⟩
    have hj : j.val < D.card := (e ⟨w, hw⟩).isLt
    have hvalue : v j = w j := by
      simp only [v, dif_pos hj]
      have heq : (⟨j.val, hj⟩ : Fin D.card) = e ⟨w, hw⟩ := rfl
      rw [heq, e.symm_apply_apply]
    exact hadj j hvalue

theorem productGraph_domination_lower (r m : Nat) (hm : r ≤ m) :
    r + 1 ≤ (productGraph r m).dominationNumber := by
  obtain ⟨D, hdom, hcard⟩ :=
    SimpleGraph.exists_isNDominatingSet_dominationNumber (productGraph r m)
  by_contra h
  have hD : D.card < r + 1 := by omega
  exact small_set_not_dominating hm D hD hdom

/-- Bernoulli's inequality gives a uniform density bound for the chosen family. -/
theorem productGraph_density (r : Nat) :
    (2 * (r + 1) + 1) ^ (r + 1) ≤ 2 * (2 * (r + 1)) ^ (r + 1) := by
  have hn : (0 : ℝ) < (r + 1 : Nat) := by positivity
  let M : ℝ := 2 * (r + 1 : Nat) + 1
  have hM : 1 < M := by dsimp [M]; linarith
  have hfrac : (1 : ℝ) / M < 1 := (div_lt_one (by linarith)).2 hM
  have hb := one_add_mul_le_pow (a := -((1 : ℝ) / M)) (by linarith) (r + 1)
  have hlower : (1 : ℝ) / 2 ≤ 1 + (r + 1 : Nat) * -((1 : ℝ) / M) := by
    apply (mul_le_mul_iff_left₀ (show 0 < M by linarith)).mp
    field_simp [ne_of_gt (show 0 < M by linarith)]
    dsimp [M]
    nlinarith
  have heq : 1 + -((1 : ℝ) / M) = (2 * (r + 1 : Nat)) / M := by
    apply (eq_div_iff (ne_of_gt (show 0 < M by linarith))).2
    field_simp
    dsimp [M]
    ring
  rw [heq, div_pow] at hb
  have hpos : 0 < M ^ (r + 1) := pow_pos (by linarith) _
  have hhalf := (le_div_iff₀ hpos).1 (hlower.trans hb)
  have hresult : M ^ (r + 1) ≤ 2 * (2 * (r + 1 : Nat)) ^ (r + 1) := by linarith
  dsimp [M] at hresult
  exact_mod_cast hresult

/-- Every proposed positive constant fails, even for connected nonempty bases. -/
theorem exists_cover_violation (c : ℝ) (hc : 0 < c) :
    ∃ (V W : Type) (_ : Fintype V) (_ : Fintype W)
      (F : SimpleGraph V) (G : SimpleGraph W) (p : W → V) (k : Nat),
      F.Connected ∧ 0 < k ∧ IsCover G F p k ∧
        (G.dominationNumber : ℝ) < c * k * F.dominationNumber := by
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / c)
  let m := 2 * (r + 1)
  let d := m ^ (r + 1)
  let F := productGraph r m
  obtain ⟨G, hcover, hdom⟩ := regular_cover_small_domination F (productGraph_regular r m)
  refine ⟨Vertex r m, Vertex r m × Option (Fin d), inferInstance, inferInstance,
    F, G, Prod.fst, d + 1, productGraph_connected r m (by dsimp [m]; omega),
    Nat.succ_pos _, hcover, ?_⟩
  have hbase : r + 1 ≤ F.dominationNumber :=
    productGraph_domination_lower r m (by dsimp [m]; omega)
  have horder : Fintype.card (Vertex r m) = (m + 1) ^ (r + 1) := by
    simp [Vertex]
  rw [horder] at hdom
  have hdensity : (m + 1) ^ (r + 1) ≤ 2 * d := productGraph_density r
  have hcr : 2 < c * (r + 1 : Nat) := by
    have h := (div_lt_iff₀ hc).mp hr
    push_cast
    nlinarith
  have hcg : 2 < c * F.dominationNumber :=
    hcr.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast hbase) hc.le)
  have hk : (0 : ℝ) < (d + 1 : Nat) := by positivity
  calc
    (G.dominationNumber : ℝ) ≤ ((m + 1) ^ (r + 1) : Nat) := by exact_mod_cast hdom
    _ ≤ 2 * (d : ℝ) := by exact_mod_cast hdensity
    _ ≤ 2 * (d + 1 : Nat) := by push_cast; linarith
    _ < c * (d + 1 : Nat) * F.dominationNumber := by
      nlinarith [mul_lt_mul_of_pos_right hcg hk]

/-- The negation of the universal assertion in Annor's Conjecture 14. -/
theorem annor_conjecture14_false :
    ¬ ∃ c : ℝ, 0 < c ∧
      forall (V W : Type) [Fintype V] [Fintype W]
        (F : SimpleGraph V) (G : SimpleGraph W) (p : W → V) (k : Nat),
        0 < k → IsCover G F p k →
          c * k * F.dominationNumber ≤ (G.dominationNumber : ℝ) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨V, W, fv, fw, F, G, p, k, _, hk, hcover, hlt⟩ := exists_cover_violation c hc
  let := fv
  let := fw
  exact (not_lt_of_ge (hbound V W F G p k hk hcover)) hlt

example : Nonempty (Vertex 1 4) := ⟨fun _ => 0⟩

example : ∃ (V W : Type) (_ : Fintype V) (_ : Fintype W)
    (F : SimpleGraph V) (G : SimpleGraph W) (p : W → V) (k : Nat),
    F.Connected ∧ 0 < k ∧ IsCover G F p k ∧
      (G.dominationNumber : ℝ) < (3 / 5 : ℝ) * k * F.dominationNumber :=
  exists_cover_violation (3 / 5) (by norm_num)

#print axioms exists_cover_violation
#print axioms annor_conjecture14_false
#print axioms productGraph_regular
#print axioms productGraph_connected
#print axioms productGraph_domination_lower
#print axioms productGraph_density

end D5.S3.ConceptDynamics.GraphColoring.AnnorCoverRefutation
