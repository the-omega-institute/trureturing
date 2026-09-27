/- GID: D5/S3/Observer/Hankel/FiniteSampleRankAmbiguity
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/FiniteSampleRankAmbiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite unary samples admit distinct minimal rational realization dimensions. -/

import D5.S3.Observer.Hankel.SequenceHankelRealization

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity

open Module
open D5.S3.Observer.Hankel.HankelMinimalStateDimension
open D5.S3.Observer.Hankel.SequenceHankelRealization

/-- A sample through length N, including a nonzero one-by-one Hankel block,
cannot distinguish minimal linear dimensions 1 and N+3. Unary words are lists
of Unit; their responses are the scalar Markov maps at their lengths. -/
theorem finite_sample_rank_ambiguity (N : ℕ) :
    ∃ f g : FiniteLinearRealization ℚ ℚ ℚ,
      FiniteDimensional ℚ (tailSpace f.behavior) ∧
      FiniteDimensional ℚ (tailSpace g.behavior) ∧
      (∀ w : List Unit, w.length ≤ N → f.behavior w.length = g.behavior w.length) ∧
      f.behavior 0 1 = 1 ∧ g.behavior 0 1 = 1 ∧
      dataHankel f.behavior 1 1 ≠ 0 ∧ dataHankel g.behavior 1 1 ≠ 0 ∧
      f.stateDimension = 1 ∧ g.stateDimension = N + 3 ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = f.behavior → f.stateDimension ≤ r.stateDimension) ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = g.behavior → g.stateDimension ≤ r.stateDimension) := by
  classical
  let f : ℕ → (ℚ →ₗ[ℚ] ℚ) := fun _ => LinearMap.id
  let g : ℕ → (ℚ →ₗ[ℚ] ℚ) := fun n =>
    (1 + if n = N + 1 then 1 else 0 : ℚ) • LinearMap.id
  let c : ℕ → ℚ := fun _ => 1
  let pulse : Fin (N + 2) → ℕ → ℚ := fun k n => if n = k.val then 1 else 0
  have hf : tailSpace f = ℚ ∙ c := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨j, u⟩, rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨u, by ext n; simp [f, c, dataTail]⟩
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      have heq : dataTail f 0 1 = c := by ext n; simp [f, c, dataTail]
      exact heq ▸ (tailState f 0 1).property
  have hcf : c ≠ 0 := by intro h; have := congrFun h 0; norm_num [c] at this
  have hfrank : finrank ℚ (tailSpace f) = 1 := by
    rw [hf]
    exact finrank_span_singleton hcf
  have hfinitef : FiniteDimensional ℚ (tailSpace f) := by
    rw [hf]
    infer_instance
  have hc : c ∈ tailSpace g := by
    have heq : dataTail g (N + 2) 1 = c := by
      ext n
      have h : n + (N + 2) ≠ N + 1 := by omega
      simp [dataTail, g, c, h]
    exact heq ▸ (tailState g (N + 2) 1).property
  have hp : ∀ k, pulse k ∈ tailSpace g := by
    intro k
    have heq : dataTail g (N + 1 - k.val) 1 - c = pulse k := by
      ext n
      have h : n + (N + 1 - k.val) = N + 1 ↔ n = k.val := by omega
      simp [dataTail, g, c, pulse, h]
    exact heq ▸ (tailSpace g).sub_mem (tailState g _ 1).property hc
  let E : (ℚ × (Fin (N + 2) → ℚ)) →ₗ[ℚ] (ℕ → ℚ) :=
    { toFun := fun x n => x.1 + if h : n < N + 2 then x.2 ⟨n, h⟩ else 0
      map_add' := by intros; ext n; dsimp; split_ifs <;> ring
      map_smul' := by intros; ext n; dsimp; split_ifs <;> ring }
  have hEinj : Function.Injective E := by
    intro x y hxy
    have hfst : x.1 = y.1 := by
      have h := congrFun hxy (N + 2)
      simpa [E] using h
    apply Prod.ext hfst
    funext k
    have h := congrFun hxy k.val
    simpa [E, k.isLt, hfst] using h
  have hgrange : tailSpace g = LinearMap.range E := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨j, u⟩, rfl⟩
      refine ⟨(u, fun k => if k.val + j = N + 1 then u else 0), ?_⟩
      ext n
      change u + (if h : n < N + 2 then
        (if n + j = N + 1 then u else 0) else 0) =
        (1 + if n + j = N + 1 then 1 else 0 : ℚ) * u
      by_cases hn : n < N + 2
      · simp only [dif_pos hn]
        split_ifs <;> ring
      · have hnj : n + j ≠ N + 1 := by omega
        simp [hn, hnj]
    · rintro _ ⟨x, rfl⟩
      have heq : E x = x.1 • c + ∑ k : Fin (N + 2), x.2 k • pulse k := by
        ext n
        simp only [E, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, c, mul_one, Finset.sum_apply, pulse]
        by_cases hn : n < N + 2
        · rw [dif_pos hn]
          congr 1
          have he : ∀ k : Fin (N + 2), n = k.val ↔ (⟨n, hn⟩ : Fin (N + 2)) = k :=
            fun k => ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
          simp [he]
        · rw [dif_neg hn]
          have hne : ∀ k : Fin (N + 2), n ≠ k.val := fun k h => hn (h ▸ k.isLt)
          simp [hne]
      rw [heq]
      exact (tailSpace g).add_mem ((tailSpace g).smul_mem _ hc)
        (Submodule.sum_mem _ fun k _ => (tailSpace g).smul_mem _ (hp k))
  have hfiniteg : FiniteDimensional ℚ (tailSpace g) := by
    rw [hgrange]
    infer_instance
  have hgrank : finrank ℚ (tailSpace g) = N + 3 := by
    rw [hgrange, LinearMap.finrank_range_of_inj hEinj, Module.finrank_prod]
    simp
    omega
  let := hfinitef
  let := hfiniteg
  let F := realizationFromSequence f
  let G := realizationFromSequence g
  obtain ⟨hF, hFd, hFmin⟩ := realizationFromSequence_is_minimal f
  obtain ⟨hG, hGd, hGmin⟩ := realizationFromSequence_is_minimal g
  have h0g : g 0 1 = 1 := by simp [g]
  have hblock : ∀ m : ℕ → (ℚ →ₗ[ℚ] ℚ), m 0 1 = 1 → dataHankel m 1 1 ≠ 0 := by
    intro m hm hzero
    have hz := congrFun (LinearMap.congr_fun hzero (fun _ => 1)) (0 : Fin 1)
    simp [dataHankel, LinearMap.lsum_apply, hm] at hz
  refine ⟨F, G, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finite_tailSpace_of_realization F.behavior F rfl
  · exact finite_tailSpace_of_realization G.behavior G rfl
  · intro w hw
    change (realizationFromSequence f).behavior _ = (realizationFromSequence g).behavior _
    rw [hF, hG]
    have hn : w.length ≠ N + 1 := by omega
    simp [f, g, hn]
  · simpa only [F, hF] using (show f 0 1 = 1 from rfl)
  · simpa only [G, hG] using h0g
  · simpa only [F, hF] using hblock f rfl
  · simpa only [G, hG] using hblock g h0g
  · exact hFd.trans hfrank
  · exact hGd.trans hgrank
  · intro r hr
    exact hFmin r (hr.trans hF)
  · intro r hr
    exact hGmin r (hr.trans hG)

#print axioms finite_sample_rank_ambiguity

end D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
