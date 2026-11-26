import GRH.Lib.DiscreteSeries.Bruhat.FloorGroups
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Poincaré series along a Bessel subgroup with unfolding, and unipotent strong
approximation. Here the series is built from a Bessel function cut off by a weight for the
arithmetic unipotent group. The sum of absolute values is uniformly bounded, and the pairing with a
form unfolds to an integral over the group. Source: A. Borel, Introduction to automorphic forms,
Proc. Sympos. Pure Math. 9 (1966) (Poincaré series); V. Platonov, A. Rapinchuk, Algebraic groups and
number theory (1994) §7.1; for the set-up, W. T. Gan, B. Gross, D. Prasad, Astérisque 346 (2012).

This file: Bessel subgroup S=UH of a unitary group: normality, factorisation, additive simple-root
character. -/
seal Finset.univ Finset.sum Finset.prod

variable {R : Type} [CommRing R] [StarRing R] {𝔰 : Shape} {T : 𝔰.Form R} {h u : T.G}

/-- The subgroup 𝖧 of the unitary group of the whole space fixing every e_j, every e*_j and z;
it is U(X₀) when z is orthogonal to X₀. -/
noncomputable abbrev Shape.Form.besselH := T.GT 𝔰.n

/-- The Bessel subgroup 𝖲: the elements of the unitary group that are unitriangular on the frame
(e₁, …, e_ϱ, z); it contains the unipotent group 𝖴 and the group 𝖧. -/
noncomputable abbrev Shape.Form.besselS := T.unitriGroup 𝔰.n

export Shape.Form (besselH besselS)

instance [h : IsHermUnit T] : IsHermUnit T.splitGram :=
  ⟨by simp [splitGram, h.1], .of_mul_eq_one _ (splitGram_mul h.2.mul_val_inv)⟩

attribute [local simp] FI.level entrywise

omit [StarRing R] in
lemma frameImage_mul_of_mem_agreeWithOneOn {g} (h : g ∈ agreeWithOneOn (fun _ j ↦ floorOf j < 𝔰.n)
  R) x : frameImage (x * g.1) = @frameImage _ 𝔰 x := by simp_all [Fin.forall_fin_succ']

variable (s : T.G) {Q g}

lemma frameMatrix_mul_besselH : h ∈ besselH → frameMatrix (s * h) = frameMatrix s :=
  (congr($(frameImage_mul_of_mem_agreeWithOneOn · s) ∘ _))

lemma besselU0_sup_besselH_le_besselS : T.besselU0 ⊔ besselH ≤ besselS :=
  sup_le (fun _ ↦ (mem_unitriGroup_of_mem_besselU ·.1)) fun _ ↦ mem_unitriGroup_of_mem_floorGroup

lemma besselS_le_normalizer_besselU : T.besselS ≤ .normalizer T.besselU :=
  Subgroup.le_normalizer_iff.2 fun s h _ ↦ (conj_mem_unitriangular ((parabolic _).2 (x :=
  s) fun _ ↦ by have := (unitriGroup_dual_row h (a := ·) (by lia))
                simp_all [mem_unitriGroup]; grind) ·.out)

/-- For s in the unitary group, the sum σ(s) of the entries just above the diagonal of the block
of s on the frame indices e₁,…,e_ϱ,z. -/
def simpleRootSum := ∑ a, s.1 (𝔰.besselFrame (.castSucc a)) (𝔰.besselFrame a.succ)

lemma simpleRootSum_mul (a : h ∈ besselS) (b : u ∈ besselS) : simpleRootSum (h * u) =
  simpleRootSum h + simpleRootSum u := (Finset.sum_congr rfl fun i _ ↦ (Fintype.sum_eq_add
  (𝔰.besselFrame i.succ) (𝔰.besselFrame i.castSucc) (by grind [level_besselFrame]) (by grind
  [Matrix.one_apply_ne])).trans (by grind [@Matrix.one_apply_eq _ R])).trans Finset.sum_add_distrib

lemma inv_mul_simpleRootSum_mem (k : u ∈ unitaryLevel Q g _) : g⁻¹ * simpleRootSum u ∈ Q :=
  (Finset.mul_sum ..).substr (sum_mem fun a ↦ by
    simpa [besselFrame_injective.ne, ne_of_lt, ← besselFrame_castSucc] using!
      k.2 (.inl a) (𝔰.besselFrame a.succ))

lemma simpleRootSum_eq_zero_of_mem_besselH (hh : h ∈ besselH) : simpleRootSum h = 0 :=
  Finset.sum_eq_zero (by grind [Matrix.one_apply_ne])

lemma besselH_apply_eq_or (hu : u ∈ besselU) (hh : h ∈ besselH) : ∀ i j, h.1 i j = (u * h).1 i j ∨
  h.1 i j = (1 : Matrix ..) i j := by simp [floorGroup_apply hh, apply_inr_of_mem_besselU hu]

lemma mem_unitaryLevel_of_besselU_mul (hu : u ∈ besselU) (hh : h ∈ besselH) :
  u * h ∈ unitaryLevel Q g _ → h ∈ unitaryLevel Q g _ := by
  obtain ⟨⟩ := besselH_apply_eq_or hu hh, besselH_apply_eq_or ((besselS_le_normalizer_besselU
    (mem_unitriGroup_of_mem_floorGroup (inv_mem hh)) _).1 (inv_mem hu)) (inv_mem hh)
  simp_all [unitaryLevel, mem_intGL, IsIntMatrix, -Sum.forall]
  grind [one_mem, zero_mem, smul_zero, sub_self]
