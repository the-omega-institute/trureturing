import GRH.Lib.General.Analysis.OstrowskiTaussky
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Compact subgroups of l-adic units (1 mod 4) are procyclic. -/

open PadicInt Filter Subgroup ZMod Nat Units

/-- A continuous κ from a compact group to ℤ_ℓ^×, with values ≡ 1 mod 4 if ℓ = 2, has procyclic
image: for some γ, every open subgroup containing γ and ker κ is the whole group. -/
lemma exists_procyclic_generator {ℓ Γ} [Fact (Prime ℓ)] [Group Γ] [TopologicalSpace Γ] [CompactSpace
  Γ] [ContinuousMul Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ) (h₂ : ∀ g, 4 ∣ (κ g).1 - 1) :
  ∃ γ, ∀ S ≥ κ.ker, S.IsOpen → γ ∈ S → ∀ g, g ∈ S := by
  obtain ⟨μ, C, c, E⟩ : ∃ μ, (∀ k, IsCyclic ((Units.map (toZModPow (k + 2)).1).comp μ).range) ∧
      Continuous μ ∧ μ.ker ≤ κ.ker := by
    obtain h | rfl := (em' _).imp (isCyclic_units_of_prime_pow ℓ Fact.out) id
    use κ, inferInstance
    use κ ^ 2, fun k ↦ isCyclic_of_le (H' := zpowers (unitOfCoprime 5 (by bound))) (by
      simpa [LE.le] using fun _ ↦ sq_mem_of_index_two (Nat.mul_left_cancel card_pos ((card_mul_index
        _).trans (by norm_num [↓card_zpowers, ← orderOf_units, orderOf_five, ↓totient_prime_pow,
        pow_succ]))) _), hκ.pow 2, fun g h ↦ val_eq_one.1 (by
      grind [@pow_p_dvd_int_iff 2 _ 2 (-2), sq_eq_one_iff.1 congr($h.1)])
  choose γ _ h using (Set.exists_subtype_range_iff.1 <| C · |>.exists_monoid_generator)
  exact (isCompact_univ (by simp : atTop.map γ ≤ _)).imp fun δ d S s o a g ↦ comap_map_eq_self
    (E.trans s) ▸ (c.isClosedMap _ (S.isClosed_of_isOpen o)).mem_of_frequently_of_tendsto (.mono
    (d.2.frequently (o.mem_nhds a)) fun k ↦ (⟨_, pow_mem · _, rfl⟩))
    (isOpenEmbedding_val.tendsto_nhds_iff.2 (tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm (fun k ↦
    (norm_le_pow_iff_mem_span_pow _ (k + 2)).2 (by simpa [← ker_toZModPow] using! congr($(h k ⟨_, g,
    rfl⟩).1.1))) (by simp [↓← norm_p_pow, -norm_p, tendsto_add_atTop_iff_nat]))))
