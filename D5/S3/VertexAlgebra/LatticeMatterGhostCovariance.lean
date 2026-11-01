/- GID: D5/S3/VertexAlgebra/LatticeMatterGhostCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeMatterGhostCovariance
   mirror-E: none(waiver:algebraic-matter-ghost-covariance)
   anchors: []
   utility: none
   digest: Finite shifted cancellation gives the matter coupling rank anomaly. -/

import D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

/-! Finite translation of original operator actions leaves the matter central anomaly. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic
open private above_upper tensor_tail from D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeMatterGhostCovariance

/-- The shifted family whose two weighted sums cancel in covariance. -/
def paired (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (r k : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map (sugawaraMode D H k) (BcGhostFock.c (r-k))

private theorem paired_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) (x : State D) :
    Function.HasFiniteSupport (fun k : ℤ => paired D H r k x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨A, hA, hw⟩ := BcGhostOccupationRadius.exists_radius w
    apply (Set.finite_Icc (r-(A : ℤ)) (upper D H v)).subset
    intro k hk
    by_contra hn
    have ht : k < r-(A : ℤ) ∨ upper D H v < k := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hn
    apply hk
    simp only [paired, TensorProduct.map_tmul]
    rcases ht with ht | ht
    · rw [(BcGhostOccupationRadius.high_modes hA hw (r-k) (by omega)).2,
        TensorProduct.tmul_zero]
    · rw [above_upper D H v k ht, TensorProduct.zero_tmul]
  | add x y hx hy =>
    apply (hx.union hy).subset
    intro k hk
    by_contra hn
    have hx0 : paired D H r k x = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hy0 : paired D H r k y = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    apply hk
    change paired D H r k (x+y) = 0
    rw [map_add, hx0, hy0, add_zero]

/-- A finite-support translation proved by a bijection of the actual finite captures. -/
private theorem finite_shift {E : Type*} [AddCommGroup E] (f : ℤ → E)
    (hf : Function.HasFiniteSupport f) (r : ℤ) :
    (∑ᶠ m : ℤ, f (m+r)) = ∑ᶠ k : ℤ, f k := by
  classical
  let s := hf.toFinset
  let t := s.image (fun k => k-r)
  have hleft : Function.support (fun m : ℤ => f (m+r)) ⊆ (t : Set ℤ) := by
    intro m hm
    apply Finset.mem_image.mpr
    refine ⟨m+r, ?_, by omega⟩
    simpa [s] using hm
  have hright : Function.support f ⊆ (s : Set ℤ) := by
    intro k hk
    simpa [s] using hk
  rw [finsum_eq_sum_of_support_subset _ hleft,
    finsum_eq_sum_of_support_subset _ hright]
  apply Finset.sum_bij (fun m _ => m+r)
  · intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    simpa using hk
  · intro m hm n hn he
    omega
  · intro k hk
    refine ⟨k-r, Finset.mem_image.mpr ⟨k, hk, rfl⟩, by omega⟩
  · intro m hm
    rfl

private theorem weighted_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) (x : State D)
    (a : ℤ → ℂ) : Function.HasFiniteSupport (fun k : ℤ => a k • paired D H r k x) := by
  apply (paired_finite D H r x).subset
  intro k hk hn
  apply hk
  change a k • paired D H r k x = 0
  change paired D H r k x = 0 at hn
  rw [hn, smul_zero]

private theorem matter_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m r : ℤ) :
    summand D H m * matterMode D H r - matterMode D H r * summand D H m =
      ((m-r : ℤ) : ℂ) • paired D H r (m+r) +
        (if m+r = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) • ghostC D (-m) := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun
    (LatticeSugawaraVirasoro.sugawaraMode_virasoro D H hHG hGH m r) v
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  simp only [summand, matterMode, paired, ghostC, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, show r-(m+r) = -m by omega]
  rw [← TensorProduct.sub_tmul, h, TensorProduct.add_tmul]
  rfl

private theorem ghost_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m r : ℤ) :
    summand D H m * ghostVirasoro D r - ghostVirasoro D r * summand D H m =
      ((2*r-m : ℤ) : ℂ) • paired D H r m := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c r (-m)) w
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at h
  have hr : BcGhostFock.c (-m) (BcGhostVirasoro.L r w) -
      BcGhostVirasoro.L r (BcGhostFock.c (-m) w) =
        ((2*r-m : ℤ) : ℂ) • BcGhostFock.c (r-m) w := by
    calc
      _ = -(BcGhostVirasoro.L r (BcGhostFock.c (-m) w) -
        BcGhostFock.c (-m) (BcGhostVirasoro.L r w)) := by abel
      _ = _ := by
        rw [h, ← neg_smul]
        congr 1; push_cast; ring
  simp only [summand, ghostVirasoro, paired, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, hr, TensorProduct.tmul_smul]

private theorem central_sum (D : LatticeData) (r : ℤ) (x : State D) :
    (∑ᶠ m : ℤ, (if m+r = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
      ghostC D (-m) x) =
      (-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r x := by
  rw [finsum_eq_single _ (-r) (fun m hm => by
    simp [show m+r ≠ 0 by omega])]
  simp only [neg_add_cancel, ite_true, neg_neg, Int.cast_neg]
  congr 1
  ring

private theorem capture_interval (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D) (w : Fock)
    (A : ℕ) (hA : 2 ≤ A) (hw : BcGhostOccupationRadius.Radius A w)
    (lo hi : ℤ) (hlo : lo ≤ -(A : ℤ)) (hhi : upper D H v ≤ hi) :
    Function.support (fun m : ℤ => summand D H m (v ⊗ₜ[ℂ] w)) ⊆
      (Finset.Icc lo hi : Set ℤ) := by
  intro m hm
  by_contra hn
  have ht : m < lo ∨ hi < m := by
    simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn
  exact hm (tensor_tail D H v w A hA hw m (by omega))

/-- Original-operator covariance, with precisely the negative rank anomaly. -/
theorem covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (r : ℤ) :
    T D H * (matterMode D H r + ghostVirasoro D r) -
      (matterMode D H r + ghostVirasoro D r) * T D H =
        (-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r := by
  classical
  apply TensorProduct.ext'
  intro v w
  let x : State D := v ⊗ₜ[ℂ] w
  obtain ⟨A, hA, hwA⟩ := BcGhostOccupationRadius.exists_radius w
  let U := upper D H v
  let V := upper D H (sugawaraMode D H r v)
  let d : ℕ := (-r).toNat
  let lo : ℤ := min (-((A+d : ℕ) : ℤ)) (-r)
  let hi : ℤ := max V (U+(d : ℤ))
  let I := Finset.Icc lo hi
  let J := Finset.Icc (r-(A : ℤ)) U
  have hU : 0 ≤ U := le_max_left _ _
  have hd : 0 ≤ (d : ℤ) := Int.natCast_nonneg _
  have hcap : Function.support (fun m : ℤ => summand D H m x) ⊆ (I : Set ℤ) :=
    capture_interval D H v w A hA hwA lo hi (by dsimp [lo]; omega)
      (by dsimp [hi]; omega)
  have hcapM : Function.support (fun m : ℤ => summand D H m (matterMode D H r x)) ⊆
      (I : Set ℤ) := by
    simpa only [x, matterMode, TensorProduct.map_tmul, LinearMap.id_apply] using
      capture_interval D H (sugawaraMode D H r v) w A hA hwA lo hi
        (by dsimp [lo]; omega) (le_max_left _ _)
  have hcapG : Function.support (fun m : ℤ => summand D H m (ghostVirasoro D r x)) ⊆
      (I : Set ℤ) := by
    simpa only [x, ghostVirasoro, TensorProduct.map_tmul, LinearMap.id_apply] using
      capture_interval D H v (BcGhostVirasoro.L r w) (A+d) (by omega)
        (BcGhostOccupationRadius.virasoro_radius hA hwA r) lo hi
        (min_le_left _ _) (by dsimp [hi]; omega)
  have hx : Function.HasFiniteSupport (fun m : ℤ => summand D H m x) :=
    I.finite_toSet.subset hcap
  have hM : Function.HasFiniteSupport (fun m : ℤ => summand D H m (matterMode D H r x)) :=
    I.finite_toSet.subset hcapM
  have hG : Function.HasFiniteSupport (fun m : ℤ => summand D H m (ghostVirasoro D r x)) :=
    I.finite_toSet.subset hcapG
  have hMx := hx.fun_comp (map_zero (matterMode D H r))
  have hGx := hx.fun_comp (map_zero (ghostVirasoro D r))
  have hdr : -r ≤ (d : ℤ) := by dsimp [d]; omega
  have hJI : J ⊆ I := by
    intro k hk
    obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_Icc.mpr
    dsimp [lo, hi]
    constructor <;> omega
  have hJshift : ∀ k ∈ J, k-r ∈ I := by
    intro k hk
    obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_Icc.mpr
    dsimp [lo, hi]
    constructor <;> omega
  have hcentral : -r ∈ I := by
    apply Finset.mem_Icc.mpr
    dsimp [lo, hi]
    constructor <;> omega
  have hpairedJ : Function.support (fun k : ℤ => paired D H r k x) ⊆ (J : Set ℤ) := by
    intro k hk
    by_contra hn
    have ht : k < r-(A : ℤ) ∨ U < k := by
      simpa only [Finset.mem_coe, J, Finset.mem_Icc, not_and_or, not_le] using hn
    apply hk
    simp only [x, paired, TensorProduct.map_tmul]
    rcases ht with ht | ht
    · rw [(BcGhostOccupationRadius.high_modes hA hwA (r-k) (by omega)).2,
        TensorProduct.tmul_zero]
    · rw [above_upper D H v k ht, TensorProduct.zero_tmul]
  have hc : Function.HasFiniteSupport (fun m : ℤ =>
      (if m+r = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) • ghostC D (-m) x) := by
    apply I.finite_toSet.subset
    intro m hm
    have he : m = -r := by
      by_contra hn
      exact hm (by simp [show m+r ≠ 0 by omega])
    simpa only [he, Finset.mem_coe] using hcentral
  have hw : Function.HasFiniteSupport (fun k : ℤ =>
      ((k-2*r : ℤ) : ℂ) • paired D H r k x) := by
    apply I.finite_toSet.subset
    intro k hk
    apply hJI (hpairedJ ?_)
    intro hz
    change paired D H r k x = 0 at hz
    apply hk
    change ((k-2*r : ℤ) : ℂ) • paired D H r k x = 0
    rw [hz, smul_zero]
  have hshift : Function.HasFiniteSupport (fun m : ℤ =>
      ((m-r : ℤ) : ℂ) • paired D H r (m+r) x) := by
    apply I.finite_toSet.subset
    intro m hm
    have hk : m+r ∈ J := hpairedJ (by
      intro hz
      change paired D H r (m+r) x = 0 at hz
      apply hm
      change ((m-r : ℤ) : ℂ) • paired D H r (m+r) x = 0
      rw [hz, smul_zero])
    have hmem := hJshift (m+r) hk
    have he : m+r-r = m := by omega
    rw [he] at hmem
    exact Finset.mem_coe.mpr hmem
  have hmatter : T D H (matterMode D H r x) - matterMode D H r (T D H x) =
      (∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired D H r k x) +
        (-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r x := by
    change (∑ᶠ m : ℤ, summand D H m (matterMode D H r x)) -
      matterMode D H r (∑ᶠ m : ℤ, summand D H m x) = _
    rw [map_finsum (matterMode D H r) hx, ← finsum_sub_distrib hM hMx]
    calc
      _ = ∑ᶠ m : ℤ, (((m-r : ℤ) : ℂ) • paired D H r (m+r) x +
          (if m+r = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
            ghostC D (-m) x) := by
        apply finsum_congr
        intro m
        exact LinearMap.congr_fun (matter_commutator D H hHG hGH m r) x
      _ = _ := by
        rw [finsum_add_distrib hshift hc, central_sum D r x]
        congr 1
        calc
          _ = ∑ᶠ m : ℤ, ((m+r-2*r : ℤ) : ℂ) • paired D H r (m+r) x := by
            apply finsum_congr
            intro m
            congr 2 <;> omega
          _ = _ := finite_shift _ hw r
  have hghost : T D H (ghostVirasoro D r x) - ghostVirasoro D r (T D H x) =
      ∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired D H r k x := by
    change (∑ᶠ m : ℤ, summand D H m (ghostVirasoro D r x)) -
      ghostVirasoro D r (∑ᶠ m : ℤ, summand D H m x) = _
    rw [map_finsum (ghostVirasoro D r) hx, ← finsum_sub_distrib hG hGx]
    apply finsum_congr
    intro m
    exact LinearMap.congr_fun (ghost_commutator D H m r) x
  have hcancel : (∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired D H r k x) +
      (∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired D H r k x) = 0 := by
    rw [← finsum_add_distrib hw (weighted_finite D H r x (fun k => ((2*r-k : ℤ) : ℂ)))]
    trans ∑ᶠ _k : ℤ, (0 : State D)
    · apply finsum_congr
      intro k
      rw [← add_smul]
      have hz : ((k-2*r : ℤ) : ℂ) + ((2*r-k : ℤ) : ℂ) = 0 := by push_cast; ring
      rw [hz, zero_smul]
    · simp
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add]
  calc
    _ = (T D H (matterMode D H r x) - matterMode D H r (T D H x)) +
        (T D H (ghostVirasoro D r x) - ghostVirasoro D r (T D H x)) := by abel
    _ = _ := by
      rw [hmatter, hghost]
      calc
        _ = ((∑ᶠ k : ℤ, ((k-2*r : ℤ) : ℂ) • paired D H r k x) +
            (∑ᶠ k : ℤ, ((2*r-k : ℤ) : ℂ) • paired D H r k x)) +
            (-((D.rank : ℂ)/12*((r : ℂ)^3-r))) • ghostC D r x := by abel
        _ = _ := by rw [hcancel, zero_add]

end D5.S3.VertexAlgebra.LatticeMatterGhostCovariance
