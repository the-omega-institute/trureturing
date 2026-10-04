/- GID: D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dissipative independence-polynomial roots lie in the open upper half-plane. -/

/-
proof_shape: result: content
escape_witness: clique_partition proves the finite-clique deletion identity by induction;
multiplier constructs r with 0 < r.im and P_U(z^2) = z P_(U\K)(z^2) r by
strong induction on U for z.im < 0; roots_upper uses this construction to exclude
lower-half-plane roots, and separates real and imaginary parts to exclude real roots.
Each private theorem has content after inlining the same-module dependencies:
clique_partition (clique induction), multiplier (domain induction and simpliciality
inheritance by claw exclusion), roots_upper (the multiplier on its live path).
SimplicialOn is a predicate definition, not a proof-valued definition.
EvenHoleFree is retained in claim but is not used in the proof.
Information-escape registration is paused under CLAUDE.md §3.9.
admission_basis: open-problem-resolution (#12755; Proved)
Direct frozen dependencies:
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion
  statement_id: sha256:8014b9cde4f69ed8e5049e30e505073622cbf5d96e9707ac8cda86d3aa47ff93
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.map_partition
  statement_id: sha256:50dc1b9d5c9895e569c8ccbec377dfbd97817d167f3e236dbb2e4f9b4a4b1956
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations
  statement_id: sha256:7db22ad633fa73946f2bfaf142d0a64a4cfa39147b167168fbaa55a96a0bb603
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_empty
  statement_id: sha256:06571c644c6e7502aeae7ae8a201816d0261248ce104afe06f667348404bd9d8
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.closedComplement
  statement_id: sha256:e270ce35c81d210cbcb24f6fb7923d43106c13ccc937c90507374c35b7171ebc
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_delete
  statement_id: sha256:d0d9cf36e5df58a4783be571fc397b28096071f033369968be6fc312ce41bf2f
D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition
  statement_id: sha256:a978cd092c8db8937d082810c0664bafbb15f0000a8f364e681df43cafff4d10
-/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false

open scoped BigOperators
open Polynomial
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.Quantum.SpinChains.DissipativeFreeFermionRootLocation

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Absence of an induced claw: three distinct, mutually nonadjacent leaves. -/
def ClawFree : Prop :=
  ∀ v a b c : α, a ≠ b → a ≠ c → b ≠ c →
    G.Adj v a → G.Adj v b → G.Adj v c →
    ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → False

/-- No induced cyclic graph on an even number of at least four vertices. -/
def EvenHoleFree : Prop :=
  ∀ m : ℕ, 4 ≤ m → Even m → ∀ f : Fin m → α, Function.Injective f →
    ¬ (∀ i j : Fin m, G.Adj (f i) (f j) ↔
      ((i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val))

/-- The paper's clique and closed-neighborhood condition. -/
def Simplicial (K : Finset α) : Prop :=
  G.IsClique (K : Set α) ∧
    ∀ j ∈ K, G.IsClique ((insert j (G.neighborFinset j) \ K : Finset α) : Set α)

/-- Equation (7), using the frozen independent-configuration partition. -/
noncomputable def P (U : Finset α) (b : α → ℝ) : ℝ[X] :=
  partition G U (fun j => -(C (b j ^ 2)) * X)

/-- Equation (16), with the plus sign. -/
noncomputable def Pt (K : Finset α) (b : α → ℝ) (γ : ℝ) : ℂ[X] :=
  ((P G Finset.univ b).map Complex.ofRealHom).comp (X ^ 2) +
    C (Complex.I * (γ : ℂ)) * X *
      (((P G (Finset.univ \ K) b).map Complex.ofRealHom).comp (X ^ 2))

def claim : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n)) (b : Fin n → ℝ) (γ : ℝ),
    ClawFree G → EvenHoleFree G → Simplicial G K → 0 < γ →
    (∀ x : ℂ, ¬ ((P G Finset.univ b).aeval x = 0 ∧
      (P G (Finset.univ \ K) b).aeval x = 0)) →
    ∀ u : ℂ, (Pt G K b γ).eval u = 0 → 0 < u.im

/-- Simpliciality relative to a finite induced vertex domain. -/
private def SimplicialOn (U K : Finset α) : Prop :=
  G.IsClique (K : Set α) ∧
    ∀ j ∈ K, G.IsClique (((U.filter (G.Adj j)) \ K : Finset α) : Set α)

omit [Fintype α] in
private theorem clique_partition {R : Type*} [CommSemiring R]
    (U K : Finset α) (hKU : K ⊆ U) (hK : G.IsClique (K : Set α)) (w : α → R) :
    partition G U w = partition G (U \ K) w +
      ∑ j ∈ K, w j * partition G ((U \ K).filter (fun v => ¬ G.Adj j v)) w := by
  induction K using Finset.induction_on generalizing U with
  | empty => simp
  | @insert j K hj ih =>
    have hjU : j ∈ U := hKU (Finset.mem_insert_self j K)
    have hsub : K ⊆ U.erase j := by
      intro k hk
      exact Finset.mem_erase.mpr ⟨fun he => hj (he ▸ hk),
        hKU (Finset.mem_insert_of_mem hk)⟩
    have hk : G.IsClique (K : Set α) := by
      intro a ha c hc hac
      exact hK (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hc) hac
    have hdel : (U.erase j) \ K = U \ insert j K := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    have hc : closedComplement G U j =
        (U \ insert j K).filter (fun v => ¬ G.Adj j v) := by
      ext v
      simp only [closedComplement, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hvj, hvU⟩, hnv⟩
        refine ⟨⟨hvU, ?_⟩, hnv⟩
        rintro (rfl | hvK)
        · exact hvj rfl
        · exact hnv (hK (Finset.mem_insert_self j K)
            (Finset.mem_insert_of_mem hvK) hvj.symm)
      · rintro ⟨⟨hvU, hn⟩, hnv⟩
        exact ⟨⟨fun he => hn (Or.inl he), hvU⟩, hnv⟩
    rw [partition_delete G U j hjU w, ih (U.erase j) hsub hk,
      hdel, hc, Finset.sum_insert hj]
    ac_rfl

omit [Fintype α] in
private theorem multiplier (b : α → ℝ) (z : ℂ) (hz : z.im < 0)
    (hcf : ClawFree G) (U K : Finset α) (hKU : K ⊆ U)
    (hs : SimplicialOn G U K) :
    ∃ r : ℂ, 0 < r.im ∧ (P G U b).aeval (z ^ 2) =
      z * (P G (U \ K) b).aeval (z ^ 2) * r := by
  classical
  have hzinv : 0 < z⁻¹.im := by
    have hne : z ≠ 0 := by
      intro he
      simp [he] at hz
    rw [Complex.inv_im]
    exact div_pos (neg_pos.mpr hz) (Complex.normSq_pos.mpr hne)
  have hweighted (w : ℝ) (hw : 0 ≤ w) (r : ℂ)
      (hr : 0 < r.im) : ((w : ℂ) / r).im ≤ 0 := by
    rw [div_eq_mul_inv, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [Complex.inv_im]
    exact mul_nonpos_of_nonneg_of_nonpos hw
      (div_nonpos_of_nonpos_of_nonneg (le_of_lt (neg_neg_of_pos hr))
        (Complex.normSq_nonneg r))
  have hpeval (U : Finset α) (b : α → ℝ) (x : ℂ) :
      (P G U b).aeval x =
        partition G U (fun j => -((b j ^ 2 : ℝ) : ℂ) * x) := by
    unfold P
    change (Polynomial.aeval x).toRingHom _ = _
    rw [map_partition]
    congr 1
    funext j
    change (Polynomial.aeval x) (-C (b j ^ 2) * X) = _
    simp
  have hclique (U K : Finset α) (hKU : K ⊆ U)
      (hK : G.IsClique (K : Set α)) (b : α → ℝ) (x : ℂ) :
      (P G U b).aeval x = (P G (U \ K) b).aeval x -
        x * ∑ j ∈ K, ((b j ^ 2 : ℝ) : ℂ) *
          (P G ((U \ K).filter (fun v => ¬ G.Adj j v)) b).aeval x := by
    simp_rw [hpeval]
    rw [clique_partition G U K hKU hK]
    simp only [Finset.mul_sum, sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hinherit (U K : Finset α) (hcf : ClawFree G)
      (hs : SimplicialOn G U K) (j : α) (hj : j ∈ K) :
      SimplicialOn G (U \ K) ((U \ K).filter (G.Adj j)) := by
    refine ⟨?_, ?_⟩
    · intro a ha c hc hac
      apply hs.2 j hj ?_ ?_ hac
      · simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff,
          and_assoc, and_left_comm, and_comm] using ha
      · simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff,
          and_assoc, and_left_comm, and_comm] using hc
    · intro v hv a ha c hc hac
      simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter] at hv ha hc
      by_contra hnac
      have hja : ¬ G.Adj j a := fun hadj => ha.2 ⟨ha.1.1, hadj⟩
      have hjc : ¬ G.Adj j c := fun hadj => hc.2 ⟨hc.1.1, hadj⟩
      have hneja : j ≠ a := fun he => ha.1.1.2 (he ▸ hj)
      have hnejc : j ≠ c := fun he => hc.1.1.2 (he ▸ hj)
      exact hcf v j a c hneja hnejc hac (G.adj_symm hv.2) ha.1.2 hc.1.2
        hja hjc hnac
  have hzne : z ≠ 0 := by
    intro he
    simp [he] at hz
  revert K
  refine Finset.strongInductionOn U (fun U ih => ?_)
  intro K hKU hs
  by_cases hke : K = ∅
  · subst K
    refine ⟨z⁻¹, hzinv, ?_⟩
    simp only [Finset.sdiff_empty]
    rw [mul_right_comm z, mul_inv_cancel₀ hzne, one_mul]
  · have hH : U \ K ⊂ U :=
      Finset.sdiff_ssubset hKU (Finset.nonempty_iff_ne_empty.mpr hke)
    have hrec : ∀ j : α, ∃ r : ℂ, 0 < r.im ∧
        (j ∈ K → (P G (U \ K) b).aeval (z ^ 2) =
          z * (P G ((U \ K) \ ((U \ K).filter (G.Adj j))) b).aeval (z ^ 2) * r) := by
      intro j
      by_cases hj : j ∈ K
      · obtain ⟨r, hr, he⟩ := ih (U \ K) hH ((U \ K).filter (G.Adj j))
          (Finset.filter_subset _ _) (hinherit U K hcf hs j hj)
        exact ⟨r, hr, fun _ => he⟩
      · exact ⟨Complex.I, by simp, fun h => False.elim (hj h)⟩
    choose r hr he using hrec
    have he' (j : α) (hj : j ∈ K) :
        (P G (U \ K) b).aeval (z ^ 2) =
          z * (P G ((U \ K).filter (fun v => ¬ G.Adj j v)) b).aeval (z ^ 2) * r j := by
      have hsets : (U \ K) \ ((U \ K).filter (G.Adj j)) =
          (U \ K).filter (fun v => ¬ G.Adj j v) := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        tauto
      simpa only [hsets] using he j hj
    have hrne (j : α) : r j ≠ 0 := by
      intro heq
      have := hr j
      simp [heq] at this
    refine ⟨z⁻¹ - ∑ j ∈ K, ((b j ^ 2 : ℝ) : ℂ) / r j, ?_, ?_⟩
    · rw [Complex.sub_im, Complex.im_sum]
      have hn : ∑ j ∈ K, (((b j ^ 2 : ℝ) : ℂ) / r j).im ≤ 0 := by
        apply Finset.sum_nonpos
        intro j hj
        exact hweighted (b j ^ 2) (sq_nonneg _) (r j) (hr j)
      linarith [hzinv]
    · rw [hclique U K hKU hs.1]
      have hsum : z ^ 2 * (∑ j ∈ K, ((b j ^ 2 : ℝ) : ℂ) *
          (P G ((U \ K).filter (fun v => ¬ G.Adj j v)) b).aeval (z ^ 2)) =
          (z * (P G (U \ K) b).aeval (z ^ 2)) *
            (∑ j ∈ K, ((b j ^ 2 : ℝ) : ℂ) / r j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [he' j hj]
        rw [div_eq_mul_inv]
        calc
          _ = (z * (z * (P G ((U \ K).filter (fun v => ¬ G.Adj j v)) b).aeval
              (z ^ 2)) * ((b j ^ 2 : ℝ) : ℂ)) * (r j * (r j)⁻¹) := by
            rw [mul_inv_cancel₀ (hrne j), mul_one]
            ring
          _ = _ := by ring
      rw [hsum]
      have hzmul : z * (P G (U \ K) b).aeval (z ^ 2) * z⁻¹ =
          (P G (U \ K) b).aeval (z ^ 2) := by
        rw [mul_right_comm z, mul_inv_cancel₀ hzne, one_mul]
      rw [mul_sub, hzmul]

private theorem roots_upper (K : Finset α) (b : α → ℝ) (γ : ℝ)
    (hcf : ClawFree G) (hs : SimplicialOn G Finset.univ K) (hg : 0 < γ)
    (hcommon : ∀ x : ℂ, ¬ ((P G Finset.univ b).aeval x = 0 ∧
      (P G (Finset.univ \ K) b).aeval x = 0))
    (z : ℂ) (hroot : (Pt G K b γ).eval z = 0) : 0 < z.im := by
  have hpeval (U : Finset α) (b : α → ℝ) (x : ℂ) :
      (P G U b).aeval x =
        partition G U (fun j => -((b j ^ 2 : ℝ) : ℂ) * x) := by
    unfold P
    change (Polynomial.aeval x).toRingHom _ = _
    rw [map_partition]
    congr 1
    funext j
    change (Polynomial.aeval x) (-C (b j ^ 2) * X) = _
    simp
  have hpt (K : Finset α) (b : α → ℝ) (γ : ℝ) (z : ℂ) :
      (Pt G K b γ).eval z = (P G Finset.univ b).aeval (z ^ 2) +
        (Complex.I * (γ : ℂ)) * z * (P G (Finset.univ \ K) b).aeval (z ^ 2) := by
    simp only [Pt, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_map, Polynomial.aeval_def]
    rfl
  have hreal (U : Finset α) (b : α → ℝ) (x : ℝ) :
      (P G U b).aeval (x : ℂ) = (((P G U b).eval x : ℝ) : ℂ) := by
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval x (P G U b)
  have hzero (U : Finset α) (b : α → ℝ) :
      (P G U b).aeval (0 : ℂ) = 1 := by
    rw [hpeval]
    simp only [mul_zero]
    have hzero : ∀ V : Finset α, partition G V (fun _ => (0 : ℂ)) = 1 := by
      intro V
      induction V using Finset.induction_on with
      | empty => exact partition_empty G _
      | @insert j V hj ih =>
        rw [partition_delete G (insert j V) j (Finset.mem_insert_self j V),
          Finset.erase_insert hj, ih]
        simp
    exact hzero U
  have hzne : z ≠ 0 := by
    intro he
    subst z
    rw [hpt] at hroot
    simp [hzero] at hroot
  by_contra hn
  have hle : z.im ≤ 0 := le_of_not_gt hn
  rcases lt_or_eq_of_le hle with hz | hz
  · obtain ⟨r, hr, hP⟩ := multiplier G b z hz hcf Finset.univ K
      (Finset.subset_univ K) hs
    have hrγ : r + Complex.I * (γ : ℂ) ≠ 0 := by
      intro he
      have him := congrArg Complex.im he
      simp only [Complex.add_im, Complex.I_mul_im, Complex.ofReal_re,
        Complex.zero_im] at him
      linarith
    have hfactor : z * (P G (Finset.univ \ K) b).aeval (z ^ 2) *
        (r + Complex.I * (γ : ℂ)) = 0 := by
      calc
        _ = (Pt G K b γ).eval z := by rw [hpt, hP]; ring
        _ = 0 := hroot
    have hH : (P G (Finset.univ \ K) b).aeval (z ^ 2) = 0 := by
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hrγ)).resolve_left hzne
    exact hcommon (z ^ 2) ⟨by rw [hP, hH]; simp, hH⟩
  · have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hz
    have hzre : z.re ≠ 0 := by
      intro he
      apply hzne
      simpa [he] using hzreal
    have hsq : z ^ 2 = ((z.re ^ 2 : ℝ) : ℂ) := by
      rw [hzreal, Complex.ofReal_pow]
      simp
    have he := hroot
    rw [hpt, hsq, hreal, hreal, hzreal] at he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    simp [Complex.mul_re, Complex.mul_im] at hre him
    have hH : (P G (Finset.univ \ K) b).eval (z.re ^ 2) = 0 := by
      exact him.resolve_left (fun h => h.elim (ne_of_gt hg) hzre)
    apply hcommon (z ^ 2)
    rw [hsq, hreal, hreal]
    simp only [hre, hH, Complex.ofReal_zero, and_self]


theorem result : claim := by
  intro n G _ K b γ hcf _ hs hg hcommon z hroot
  have hson : SimplicialOn G Finset.univ K := by
    refine ⟨hs.1, ?_⟩
    intro j hj a ha c hc hac
    apply hs.2 j hj ?_ ?_ hac
    · simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (by simpa using ha.1), ha.2⟩
    · simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (by simpa using hc.1), hc.2⟩
  exact roots_upper G K b γ hcf hson hg hcommon z hroot

#print axioms result

end D5.S3.Quantum.SpinChains.DissipativeFreeFermionRootLocation
