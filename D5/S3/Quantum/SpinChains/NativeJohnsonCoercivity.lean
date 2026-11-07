/- GID: D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/NativeJohnsonCoercivity
   mirror-E: none(waiver:kernel-checked-native-coercivity)
   anchors: []
   utility: none
   digest: Counting-average coercivity for coefficient-one fixed-rank lowering. -/
import D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
noncomputable section
open scoped BigOperators InnerProductSpace
open D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
set_option maxHeartbeats 800000

/-- A finite primitive decomposition at every rank and site count. -/
private theorem fixed_rank_decomposition (N r : ℕ) (f : Space N) (hf : f ∈ rankSpace N r) :
    ∃ v : ℕ → Space N, (∀ t, t ≤ r → v t ∈ primitive N t) ∧
      f = ∑ t ∈ Finset.range (r + 1), (U N ^ (r - t)) (v t) := by
  classical
  induction r generalizing f with
  | zero =>
    refine ⟨fun _ => f, ?_, ?_⟩
    · intro t ht
      have ht0 : t = 0 := by omega
      subst t
      rw [primitive_zero_eq]
      exact hf
    · simp
  | succ r ih =>
    have hs : f ∈ (rankSpace N r).map (U N) ⊔ primitive N (r + 1) := by
      rw [rank_split]
      exact hf
    obtain ⟨a, ⟨w, hw, hwa⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hs
    subst a
    obtain ⟨v, hv, he⟩ := ih w hw
    refine ⟨fun t => if t = r + 1 then b else v t, ?_, ?_⟩
    · intro t ht
      dsimp only
      split_ifs with h
      · subst t; exact hb
      · exact hv t (by omega)
    · rw [Finset.sum_range_succ]
      simp only [ite_true, Nat.sub_self, pow_zero, Module.End.one_apply]
      rw [← hab, he, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      have htr : t ≤ r := by have := Finset.mem_range.mp ht; omega
      rw [ite_eq_right (by omega), show r + 1 - t = (r - t) + 1 by omega,
        pow_succ', Module.End.mul_apply]

/-- The original recurrence gives the actual UL action, without parity. -/
private theorem string_UL {N t : ℕ} {v : Space N} (hv : v ∈ primitive N t) (q : ℕ) :
    U N (L N ((U N ^ q) v)) =
      ((q : ℂ) * ((N : ℂ) - 2 * t - q + 1)) • ((U N ^ q) v) := by
  cases q with
  | zero => simp [show L N v = 0 from hv.2]
  | succ q =>
    rw [primitive_recurrence hv q, map_smul]
    simp only [pow_succ', Module.End.mul_apply]
    congr 1
    push_cast
    ring

private theorem string_defect_eigenvalue {N r t : ℕ} (htr : t ≤ r)
    {v : Space N} (hv : v ∈ primitive N t) :
    (((r : ℂ) * ((N : ℂ) - r + 1)) • (U N ^ (r - t)) v -
      U N (L N ((U N ^ (r - t)) v))) =
        ((t : ℂ) * ((N : ℂ) + 1 - t)) • ((U N ^ (r - t)) v) := by
  rw [string_UL hv, ← sub_smul, Nat.cast_sub htr]
  congr 1
  ring

private theorem string_cutoff {N r t : ℕ} (htr : t ≤ r) (hhigh : N - r < t)
    (hr : r ≤ N) {v : Space N} (hv : v ∈ primitive N t) :
    (U N ^ (r - t)) v = 0 := by
  by_cases hz : v = 0
  · simp [hz]
  have ht := primitive_degree hv hz
  have he := primitive_endpoint ht hv
  rw [show r - t = (r - t - (N - 2 * t + 1)) + (N - 2 * t + 1) by omega,
    pow_add, Module.End.mul_apply, he, map_zero]

private theorem component_orthogonal {N r t u : ℕ} {v w : Space N}
    (hv : v ∈ primitive N t) (hw : w ∈ primitive N u) (htu : t ≠ u) :
    inner ℂ ((U N ^ (r - t)) v) ((U N ^ (r - u)) w) = 0 :=
  inner_power_orthogonal hv hw (primitive_orthogonal hv hw htu) _ _

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
/-- A finite orthogonal sum identity, used only by the exact spectral check. -/
private theorem inner_orthogonal_sum {N : ℕ} (s : Finset ℕ) (z : ℕ → Space N)
    (a : ℕ → ℂ) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (z i) (z j) = 0) :
    inner ℂ (∑ i ∈ s, z i) (∑ i ∈ s, a i • z i) =
      ∑ i ∈ s, a i * inner ℂ (z i) (z i) := by
  classical
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right]
  · intro j hj hji
    rw [inner_smul_right, ho i hi j hj (Ne.symm hji), mul_zero]
  · exact fun h => (h hi).elim

private theorem spectral_coercivity (N r : ℕ) (hr : r ≤ N) (f : Space N)
    (hf : f ∈ rankSpace N r) :
    ∃ v : ℕ → Space N,
      (∀ t, t ≤ r → v t ∈ primitive N t) ∧
      f = ∑ t ∈ Finset.range (r + 1), (U N ^ (r - t)) (v t) ∧
      (∀ t, t ≤ r → N - r < t → (U N ^ (r - t)) (v t) = 0) ∧
      (N : ℝ) * ‖f - (U N ^ r) (v 0)‖ ^ 2 ≤
        (inner ℂ f (((r : ℂ) * ((N : ℂ) - r + 1)) • f - U N (L N f))).re := by
  classical
  obtain ⟨v, hv, he⟩ := fixed_rank_decomposition N r f hf
  refine ⟨v, hv, he, ?_, ?_⟩
  · intro t ht hh
    exact string_cutoff ht hh hr (hv t ht)
  · let z : ℕ → Space N := fun t => (U N ^ (r - t)) (v t)
    let a : ℕ → ℂ := fun t => (t : ℂ) * ((N : ℂ) + 1 - t)
    let s := Finset.range (r + 1)
    have hmem {t : ℕ} (ht : t ∈ s) : t ≤ r := by
      dsimp [s] at ht
      exact Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    have ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (z i) (z j) = 0 := by
      intro i hi j hj hij
      exact component_orthogonal (hv i (hmem hi)) (hv j (hmem hj)) hij
    have hD : ((r : ℂ) * ((N : ℂ) - r + 1)) • f - U N (L N f) =
        ∑ t ∈ s, a t • z t := by
      rw [he, Finset.smul_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      exact string_defect_eigenvalue (hmem ht) (hv t (hmem ht))
    have henergy : (inner ℂ f (((r : ℂ) * ((N : ℂ) - r + 1)) • f -
        U N (L N f))).re = ∑ t ∈ s, ((t : ℝ) * ((N : ℝ) + 1 - t)) * ‖z t‖ ^ 2 := by
      rw [hD, he, inner_orthogonal_sum s z a ho, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [inner_self_eq_norm_sq_to_K]
      simp [a, pow_two, Complex.mul_re, RCLike.ofReal_re, RCLike.ofReal_im]
    have hres : f - (U N ^ r) (v 0) = ∑ t ∈ s.erase 0, z t := by
      have h0 : 0 ∈ s := by simp [s]
      have hh := Finset.sum_erase_add s z h0
      rw [he]
      change (∑ t ∈ s, z t) - z 0 = _
      rw [← hh]
      abel
    have hnorm : ‖f - (U N ^ r) (v 0)‖ ^ 2 = ∑ t ∈ s.erase 0, ‖z t‖ ^ 2 := by
      rw [hres]
      have horth := inner_orthogonal_sum (s.erase 0) z (fun _ => 1)
        (fun i hi j hj hij => ho i (Finset.mem_of_mem_erase hi) j
          (Finset.mem_of_mem_erase hj) hij)
      simp only [one_smul, one_mul] at horth
      rw [inner_self_eq_norm_sq_to_K] at horth
      have hh := congrArg Complex.re horth
      simpa [inner_self_eq_norm_sq_to_K, Complex.re_sum, pow_two, Complex.mul_re, RCLike.ofReal_re, RCLike.ofReal_im] using hh
    rw [henergy, hnorm, Finset.mul_sum]
    have hzero : ((0 : ℝ) * ((N : ℝ) + 1 - 0)) * ‖z 0‖ ^ 2 = 0 := by ring
    rw [← Finset.sum_erase_add _ _ (show 0 ∈ s by simp [s])]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_le_sum
    intro t ht
    have hts := Finset.mem_of_mem_erase ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    by_cases hhigh : N - r < t
    · have hz : z t = 0 := string_cutoff (hmem hts) hhigh hr (hv t (hmem hts))
      simp [hz]
    · have htN : t ≤ N := by have := hmem hts; omega
      have htr : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
      have htNr : (t : ℝ) ≤ N := by exact_mod_cast htN
      have hg : (N : ℝ) ≤ (t : ℝ) * ((N : ℝ) + 1 - t) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr htr) (sub_nonneg.mpr htNr)]
      exact mul_le_mul_of_nonneg_right hg (sq_nonneg _)

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation
open D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
set_option maxHeartbeats 800000
abbrev Rank (N r : ℕ) := {A : Finset (Fin N) // A.card = r}
abbrev PreviousRank (N r : ℕ) := {T : Finset (Fin N) // T.card + 1 = r}
abbrev Layer (N r : ℕ) := EuclideanSpace ℂ (Rank N r)
abbrev PreviousLayer (N r : ℕ) := EuclideanSpace ℂ (PreviousRank N r)

private def embed (N r : ℕ) (f : Layer N r) : Space N :=
  WithLp.toLp 2 (fun x => if h : occupancy x = r then
    f (rankConfigurationEquiv N r ⟨x,h⟩) else 0)

private theorem embed_rank (N r : ℕ) (f : Layer N r) : embed N r f ∈ rankSpace N r := by
  intro x hx
  simp [embed, hx]

def lower (N r : ℕ) : Layer N r →ₗ[ℂ] PreviousLayer N r where
  toFun f := WithLp.toLp 2 fun T => ∑ i : Fin N,
    if hi : i ∈ T.val then 0 else
      f ⟨insert i T.val, by rw [Finset.card_insert_of_notMem hi]; exact T.property⟩
  map_add' f g := by
    ext T
    simp only [PiLp.add_apply, PiLp.toLp_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  map_smul' c f := by ext T; simp [Finset.mul_sum]

def average (N r : ℕ) (f : Layer N r) : Layer N r :=
  WithLp.toLp 2 fun _ => (Fintype.card (Rank N r) : ℂ)⁻¹ * ∑ A, f A

def defect (N r : ℕ) : Module.End ℂ (Layer N r) :=
  ((r : ℂ) * ((N : ℂ) - r + 1)) • 1 - (lower N r).adjoint.comp (lower N r)

private theorem native_energy (N r : ℕ) (f : Layer N r) :
    (inner ℂ f (defect N r f)).re =
      ((r : ℝ) * ((N : ℝ) - r + 1)) * ‖f‖ ^ 2 - ‖lower N r f‖ ^ 2 := by
  simp only [defect, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.comp_apply, inner_sub_right, inner_smul_right]
  rw [(lower N r).adjoint_inner_right f (lower N r f)]
  simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

private theorem embed_inner (N r : ℕ) (f g : Layer N r) :
    inner ℂ (embed N r f) (embed N r g) = inner ℂ f g := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Configuration N => occupancy x = r)]
  have hz : (∑ x : {x : Configuration N // ¬ occupancy x = r},
      inner ℂ (embed N r f x.val) (embed N r g x.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [embed, x.property]
  rw [hz, add_zero]
  rw [← (rankConfigurationEquiv N r).sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  simp [embed, x.property]

private theorem embed_norm (N r : ℕ) (f : Layer N r) : ‖embed N r f‖ = ‖f‖ := by
  have h := congrArg Complex.re (embed_inner N r f f)
  simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] at h
  nlinarith [norm_nonneg (embed N r f), norm_nonneg f]

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

private theorem layer_card (N r : ℕ) : Fintype.card (Rank N r) = N.choose r := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

/-- The exact primitive vacuum is the all-one bit configuration. -/
private def vacuum (N : ℕ) : Configuration N := fun _ => 1

private theorem occupancy_vacuum (N : ℕ) : occupancy (vacuum N) = 0 := by
  simp [occupancy, vacuum]

private theorem rank_zero_configuration (N : ℕ) (x : Configuration N) (hx : occupancy x = 0) :
    x = vacuum N := by
  apply (configurationEquiv N).injective
  change occupiedSet x = occupiedSet (vacuum N)
  have hcard : (occupiedSet x).card = 0 := (occupiedSet_card x).trans hx
  rw [Finset.card_eq_zero.mp hcard]
  simp [occupiedSet, vacuum]

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
private lemma site_action {N : ℕ} (i : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Space N) (x : Configuration N) :
    (site N i A *ᵥ v.ofLp) x = ∑ a : Fin 2, A (x i) a * v (Function.update x i a) := by
  classical
  let e := Equiv.funSplitAt i (Fin 2)
  have he (a : Fin 2) : e.symm (a, fun j => x j.val) = Function.update x i a := by
    funext j
    by_cases hj : j = i <;> simp [e, Equiv.funSplitAt_symm_apply, hj]
  have hk (a : Fin 2) (z : {j : Fin N // j ≠ i} → Fin 2) :
      site N i A x (e.symm (a, z)) =
        A (x i) a * (if (fun j : {j : Fin N // j ≠ i} => x j.val) = z then 1 else 0) := by
    rw [site_entry, Finset.prod_boole]
    congr 1
    · simp [e, Equiv.funSplitAt_symm_apply]
    · congr 1
      apply propext
      constructor
      · intro h
        funext j
        have hj := h j.val (by simp [j.property])
        simpa [e, Equiv.funSplitAt_symm_apply, j.property] using hj
      · intro h j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hh := congrFun h ⟨j, hji⟩
        simpa [e, Equiv.funSplitAt_symm_apply, hji] using hh
  change (∑ y : Configuration N, site N i A x y * v y) = _
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, hk, ite_mul, mul_ite, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]

private lemma U_apply (N : ℕ) (v : Space N) (x : Configuration N) :
    U N v x = ∑ i : Fin N, if x i = 0 then v (Function.update x i 1) else 0 := by
  change ((∑ i : Fin N, site N i sigmaPlus) *ᵥ v.ofLp) x = _
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, site_action, Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro i _
  generalize x i = a
  fin_cases a <;> simp [sigmaPlus]

private lemma L_apply (N : ℕ) (v : Space N) (x : Configuration N) :
    L N v x = ∑ i : Fin N, if x i = 1 then v (Function.update x i 0) else 0 := by
  change ((∑ i : Fin N, site N i sigmaMinus) *ᵥ v.ofLp) x = _
  rw [Matrix.sum_mulVec]
  simp only [Finset.sum_apply, site_action, Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro i _
  generalize x i = a
  fin_cases a <;> simp [sigmaMinus]

private lemma occupied_update_one {N : ℕ} (x : Configuration N) (i : Fin N) :
    occupiedSet (Function.update x i 1) = (occupiedSet x).erase i := by
  ext j
  by_cases h : j = i <;> simp [occupiedSet, h, Function.update_of_ne]

private lemma occupied_update_zero {N : ℕ} (x : Configuration N) (i : Fin N) :
    occupiedSet (Function.update x i 0) = insert i (occupiedSet x) := by
  ext j
  by_cases h : j = i <;> simp [occupiedSet, h, Function.update_of_ne]

private lemma occupancy_update_one {N : ℕ} (x : Configuration N) (i : Fin N) (hi : x i = 0) :
    occupancy (Function.update x i 1) + 1 = occupancy x := by
  rw [← occupiedSet_card, occupied_update_one, Finset.card_erase_of_mem]
  · rw [occupiedSet_card]
    have : 0 < occupancy x := by
      rw [← occupiedSet_card]
      exact Finset.card_pos.mpr ⟨i, by simp [occupiedSet, hi]⟩
    omega
  · simp [occupiedSet, hi]

private lemma occupancy_update_zero {N : ℕ} (x : Configuration N) (i : Fin N) (hi : x i = 1) :
    occupancy (Function.update x i 0) = occupancy x + 1 := by
  rw [← occupiedSet_card, occupied_update_zero, Finset.card_insert_of_notMem]
  · rw [occupiedSet_card]
  · simp [occupiedSet, hi]

/-- The rank-r constant, supported on the actual r-occupancy configurations. -/
private def constantRank (N r : ℕ) (c : ℂ) : Space N :=
  WithLp.toLp 2 fun x => if occupancy x = r then c else 0

private lemma U_constantRank (N r : ℕ) (c : ℂ) :
    U N (constantRank N r c) = constantRank N (r+1) (((r : ℂ)+1)*c) := by
  ext x
  rw [U_apply]
  by_cases hx : occupancy x = r+1
  · have hterms : ∀ i : Fin N,
        (if x i = 0 then constantRank N r c (Function.update x i 1) else 0) =
          if x i = 0 then c else 0 := by
      intro i
      split_ifs with hi
      · have hu := occupancy_update_one x i hi
        simp [constantRank, show occupancy (Function.update x i 1) = r by omega]
      · rfl
    simp only [hterms]
    have hs : (∑ i : Fin N, if x i = 0 then c else 0) = (occupancy x : ℂ)*c := by
      unfold occupancy
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hs]
    simp [constantRank, hx]
  · have hterms : ∀ i : Fin N,
        (if x i = 0 then constantRank N r c (Function.update x i 1) else 0) = 0 := by
      intro i
      split_ifs with hi
      · have hu := occupancy_update_one x i hi
        simp [constantRank, show occupancy (Function.update x i 1) ≠ r by omega]
      · rfl
    simp only [hterms, Finset.sum_const_zero]
    simp [constantRank, hx]

private lemma vacuum_factorial (N r : ℕ) (v : Space N) (hv : v ∈ primitive N 0) :
    (U N ^ r) v = constantRank N r ((r.factorial : ℂ) * v (vacuum N)) := by
  have h0 : v = constantRank N 0 (v (vacuum N)) := by
    ext x
    by_cases hx : occupancy x = 0
    · have he := rank_zero_configuration N x hx
      subst x
      simp [constantRank, occupancy_vacuum]
    · simp [constantRank, hx, (show ∀ x, occupancy x ≠ 0 → v x = 0 from hv.1) x hx]
  induction r with
  | zero => simpa using h0
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, U_constantRank]
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

private def previousConfigurationEquiv (N r : ℕ) :
    {x : Configuration N // occupancy x + 1 = r} ≃ PreviousRank N r where
  toFun x := ⟨occupiedSet x.val, by rw [occupiedSet_card]; exact x.property⟩
  invFun T := ⟨(configurationEquiv N).symm T.val, by
    rw [← occupiedSet_card]
    change ((configurationEquiv N) ((configurationEquiv N).symm T.val)).card + 1 = r
    simpa using T.property⟩
  left_inv x := by apply Subtype.ext; exact (configurationEquiv N).left_inv x
  right_inv T := by apply Subtype.ext; exact (configurationEquiv N).right_inv T

private def previousEmbed (N r : ℕ) (f : PreviousLayer N r) : Space N :=
  WithLp.toLp 2 fun x => if h : occupancy x + 1 = r then
    f (previousConfigurationEquiv N r ⟨x,h⟩) else 0

private lemma previousEmbed_inner (N r : ℕ) (f g : PreviousLayer N r) :
    inner ℂ (previousEmbed N r f) (previousEmbed N r g) = inner ℂ f g := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Configuration N => occupancy x + 1 = r)]
  have hz : (∑ x : {x : Configuration N // ¬ occupancy x + 1 = r},
      inner ℂ (previousEmbed N r f x.val) (previousEmbed N r g x.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [previousEmbed, x.property]
  rw [hz, add_zero, ← (previousConfigurationEquiv N r).sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  simp [previousEmbed, x.property]

private lemma previousEmbed_norm (N r : ℕ) (f : PreviousLayer N r) :
    ‖previousEmbed N r f‖ = ‖f‖ := by
  have h := congrArg Complex.re (previousEmbed_inner N r f f)
  simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] at h
  nlinarith [norm_nonneg (previousEmbed N r f), norm_nonneg f]

private lemma lower_intertwines (N r : ℕ) (f : Layer N r) :
    L N (embed N r f) = previousEmbed N r (lower N r f) := by
  classical
  ext x
  rw [L_apply]
  by_cases hx : occupancy x + 1 = r
  · simp only [previousEmbed, PiLp.toLp_apply, dif_pos hx, lower]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i = 1
    · have hnot : i ∉ occupiedSet x := by simp [occupiedSet, hi]
      have hnew : occupancy (Function.update x i 0) = r := by
        rw [occupancy_update_zero x i hi, hx]
      simp only [if_pos hi, embed, PiLp.toLp_apply, dif_pos hnew,
        previousConfigurationEquiv, Equiv.coe_fn_mk, hnot, ↓reduceDIte]
      exact congrArg (fun A : Rank N r => f A) (by
        apply Subtype.ext
        exact occupied_update_zero x i)
    · have hzero : x i = 0 := by omega
      have hmem : i ∈ occupiedSet x := by simp [occupiedSet, hzero]
      simp [hi, previousConfigurationEquiv, hmem]
  · simp only [previousEmbed, PiLp.toLp_apply, dif_neg hx]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · have hnew : occupancy (Function.update x i 0) ≠ r := by
        rw [occupancy_update_zero x i hi]
        exact hx
      simp [embed, hnew]
    · rfl

private lemma embed_sub (N r : ℕ) (f g : Layer N r) :
    embed N r (f-g) = embed N r f - embed N r g := by
  ext x
  by_cases hx : occupancy x = r <;> simp [embed, hx]

private lemma embed_constant (N r : ℕ) (c : ℂ) :
    embed N r (WithLp.toLp 2 fun _ => c) = constantRank N r c := by
  ext x
  by_cases hx : occupancy x = r <;> simp [embed, constantRank, hx]

private lemma primitive_vacuum (N : ℕ) : constantRank N 0 1 ∈ primitive N 0 := by
  rw [primitive_zero_eq]
  intro x hx
  simp [constantRank, hx]

private lemma vacuum_factorial_one (N r : ℕ) :
    (U N ^ r) (constantRank N 0 1) = constantRank N r (r.factorial : ℂ) := by
  simpa [constantRank, occupancy_vacuum] using
    vacuum_factorial N r (constantRank N 0 1) (primitive_vacuum N)

private lemma inner_constantRank (N r : ℕ) (f : Layer N r) (c : ℂ) :
    inner ℂ (constantRank N r c) (embed N r f) = starRingEnd ℂ c * ∑ A, f A := by
  rw [← embed_constant, embed_inner, PiLp.inner_apply]
  simp only [PiLp.toLp_apply, RCLike.inner_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

namespace D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

private lemma zero_component_average (N r : ℕ) (hr : r ≤ N) (f : Layer N r)
    (v : ℕ → Space N) (hv : ∀ t, t ≤ r → v t ∈ primitive N t)
    (he : embed N r f = ∑ t ∈ Finset.range (r+1), (U N ^ (r-t)) (v t)) :
    (U N ^ r) (v 0) = embed N r (average N r f) := by
  classical
  let c : ℂ := (r.factorial : ℂ) * v 0 (vacuum N)
  let g : Layer N r := WithLp.toLp 2 fun _ => c
  have hz : (U N ^ r) (v 0) = embed N r g := by
    rw [vacuum_factorial N r (v 0) (hv 0 (Nat.zero_le _))]
    exact (embed_constant N r c).symm
  have ho : inner ℂ ((U N ^ r) (constantRank N 0 1))
      (embed N r f - (U N ^ r) (v 0)) = 0 := by
    rw [inner_sub_right, he, inner_sum]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t ht ht0
      exact inner_power_orthogonal (primitive_vacuum N) (hv t (by
        have := Finset.mem_range.mp ht; omega))
        (primitive_orthogonal (primitive_vacuum N) (hv t (by
          have := Finset.mem_range.mp ht; omega)) (Ne.symm ht0)) _ _
    · simp
  rw [vacuum_factorial_one, hz, ← embed_sub, inner_constantRank] at ho
  have hfac : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hsum : ∑ A, (f-g) A = 0 := by
    simpa using (mul_eq_zero.mp ho).resolve_left (by simpa using hfac)
  have hc : (Fintype.card (Rank N r) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, layer_card]
    exact Nat.ne_of_gt (Nat.choose_pos hr)
  have hmean : (Fintype.card (Rank N r) : ℂ)⁻¹ * ∑ A, f A = c := by
    simp only [PiLp.sub_apply, g, PiLp.toLp_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have heq := sub_eq_zero.mp hsum
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hz]
  congr 1
  ext A
  exact hmean.symm

private lemma boolean_native_energy (N r : ℕ) (f : Layer N r) :
    (inner ℂ (embed N r f)
      (((r : ℂ) * ((N : ℂ)-r+1)) • embed N r f - U N (L N (embed N r f)))).re =
      (inner ℂ f (defect N r f)).re := by
  have hadj : (U N).adjoint = L N := by
    -- The concrete adjoint is already proved by the original frozen module.
    exact adjoint_U N
  rw [inner_sub_right, inner_smul_right,
    ← (U N).adjoint_inner_left (L N (embed N r f)) (embed N r f)]
  rw [hadj, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    lower_intertwines, previousEmbed_norm, embed_norm, native_energy]
  simp [pow_two, Complex.mul_re]

/-- Exact native coefficient-one Johnson coercivity, including odd N and both endpoints. -/
theorem result (N r : ℕ) (hr : r ≤ N) (f : Layer N r) :
    (N : ℝ) * ‖f-average N r f‖^2 ≤ (inner ℂ f (defect N r f)).re := by
  obtain ⟨v,hv,he,hcut,hgap⟩ := spectral_coercivity N r hr (embed N r f) (embed_rank N r f)
  rw [zero_component_average N r hr f v hv he, ← embed_sub, embed_norm,
    boolean_native_energy] at hgap
  exact hgap

end D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity

#print axioms D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity.result
