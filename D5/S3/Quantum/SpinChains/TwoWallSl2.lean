/- GID: D5/S3/Quantum/SpinChains/TwoWallSl2
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/TwoWallSl2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two binary arcs of a marked cyclic word carry a translation invariant sl₂ action. -/

import D5.S3.Quantum.SpinChains.TwoWallMarked
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.DFinsupp

open scoped BigOperators TensorProduct

namespace D5.S3.Quantum.SpinChains.TwoWallSl2

open TwoWallWords TwoWallMarked BinaryBinBaseChange HypereclecticNonShortening
open Sl2WeightFiltration
open D5.S1.Words.ParityCode.OddTopWeight (ones)

variable (K : Type*) [Field K]

private def bitsSwap {m : ℕ} (i j : Fin m) (w : Fin m → Bool) : Fin m → Bool :=
  fun k => w (Equiv.swap i j k)

private theorem bitsSwap_ones {m : ℕ} (i j : Fin m) (w : Fin m → Bool) :
    ones (bitsSwap i j w) = ones w :=
  Equiv.sum_comp (Equiv.swap i j) (fun k => if w k then 1 else 0)

private theorem bitsSwap_twice {m : ℕ} (i j : Fin m) (w : Fin m → Bool) :
    bitsSwap i j (bitsSwap i j w) = w := by
  funext k
  simp [bitsSwap]

private theorem localH_delta {m : ℕ} (i j : Fin m) (w : Fin m → Bool) :
    localH i j (Pi.single w 1) =
      if w i = true ∧ w j = false then Pi.single (bitsSwap i j w) 1 else 0 := by
  classical
  ext y
  have swap_eq : bitsSwap i j y = w ↔ y = bitsSwap i j w := by
    constructor
    · intro h
      rw [← h, bitsSwap_twice]
    · intro h
      rw [h, bitsSwap_twice]
  change (if y i = false ∧ y j = true then
    (Pi.single w (1 : ℚ) : (Fin m → Bool) → ℚ) (bitsSwap i j y) else 0) = _
  by_cases h : y = bitsSwap i j w
  · subst y
    split_ifs <;> simp_all [bitsSwap, bitsSwap_twice]
  · have hn : bitsSwap i j y ≠ w := fun he => h (swap_eq.mp he)
    split_ifs <;> simp_all

private def leftSite {m : ℕ} (j : Fin (m - 1)) : Fin m := ⟨j, by omega⟩
private def rightSite {m : ℕ} (j : Fin (m - 1)) : Fin m := ⟨j.val + 1, by omega⟩

private def swapBin {m : ℕ} (j : Fin (m - 1)) (w : Fin m → Bool) : Fin m → Bool :=
  bitsSwap (leftSite j) (rightSite j) w

private def leftMove {a b : ℕ} (c : Coordinates a b) (j : Fin (c.m - 1)) :
    Coordinates a b :=
  { c with u := swapBin j c.u
           filling := by rw [swapBin, bitsSwap_ones]; exact c.filling }

private def rightMove {a b : ℕ} (c : Coordinates a b) (j : Fin (c.n - 1)) :
    Coordinates a b :=
  { c with v := swapBin j c.v
           filling := by rw [swapBin, bitsSwap_ones]; exact c.filling }

private abbrev lowers {m : ℕ} (w : Fin m → Bool) (j : Fin (m - 1)) : Prop :=
  w (leftSite j) = true ∧ w (rightSite j) = false

private abbrev raises {m : ℕ} (w : Fin m → Bool) (j : Fin (m - 1)) : Prop :=
  w (leftSite j) = false ∧ w (rightSite j) = true

private def raisingCoefficient (m : ℕ) (j : Fin (m - 1)) : ℚ :=
  ((j.val + 1 : ℕ) : ℚ) * ((m : ℚ) - (j.val + 1 : ℕ))

private theorem Hbin_delta (m : ℕ) (w : Fin m → Bool) :
    Hbin m (Pi.single w 1) =
      ∑ j : Fin (m - 1), if lowers w j then Pi.single (swapBin j w) 1 else 0 := by
  classical
  simp only [Hbin, LinearMap.sum_apply, localH_delta]
  rfl

private theorem Rbin_delta (m : ℕ) (w : Fin m → Bool) :
    Rbin m (Pi.single w 1) =
      ∑ j : Fin (m - 1), if raises w j then
        raisingCoefficient m j • Pi.single (swapBin j w) 1 else 0 := by
  classical
  simp only [Rbin, LinearMap.sum_apply, LinearMap.smul_apply, localR, localH_delta]
  apply Finset.sum_congr rfl
  intro j _
  simp only [raises, swapBin, raisingCoefficient, leftSite, rightSite]
  rw [show bitsSwap (⟨j.val + 1, by omega⟩ : Fin m) ⟨j.val, by omega⟩ w =
    bitsSwap ⟨j.val, by omega⟩ ⟨j.val + 1, by omega⟩ w by
      exact congrArg (fun e : Equiv.Perm (Fin m) => w ∘ e) (Equiv.swap_comm _ _)]
  split_ifs <;> simp_all [and_comm]

private abbrev CoordinateSpace (a b : ℕ) := Coordinates a b →₀ K

private noncomputable def coordinateH (a b : ℕ) : Module.End K (CoordinateSpace K a b) :=
  Finsupp.linearCombination K (fun c =>
    ((weight c.u : K) + (weight c.v : K)) • Finsupp.single c 1)

private noncomputable def coordinateE (a b : ℕ) : Module.End K (CoordinateSpace K a b) := by
  classical
  exact Finsupp.linearCombination K (fun c =>
    (∑ j : Fin (c.m - 1), if raises c.u j then
      (raisingCoefficient c.m j : K) • Finsupp.single (leftMove c j) 1 else 0) +
    (∑ j : Fin (c.n - 1), if raises c.v j then
      (raisingCoefficient c.n j : K) • Finsupp.single (rightMove c j) 1 else 0))

private noncomputable def coordinateF (a b : ℕ) : Module.End K (CoordinateSpace K a b) := by
  classical
  exact Finsupp.linearCombination K (fun c =>
    (∑ j : Fin (c.m - 1), if lowers c.u j then
      Finsupp.single (leftMove c j) 1 else 0) +
    (∑ j : Fin (c.n - 1), if lowers c.v j then
      Finsupp.single (rightMove c j) 1 else 0))

private abbrev Key (a b : ℕ) := Pos a b × ℕ × ℕ
private abbrev BinTensor (k : Key a b) :=
  ((Fin k.2.1 → Bool) → K) ⊗[K] ((Fin k.2.2 → Bool) → K)
private abbrev Ambient (a b : ℕ) := Π₀ k : Key a b, BinTensor K k
private abbrev RawLabel (a b : ℕ) :=
  Σ k : Key a b, (Fin k.2.1 → Bool) × (Fin k.2.2 → Bool)

private def rawLabel {a b : ℕ} (c : Coordinates a b) : RawLabel a b :=
  ⟨(c.p,c.m,c.n), c.u,c.v⟩

private theorem rawLabel_injective {a b : ℕ} :
    Function.Injective (@rawLabel a b) := by
  rintro ⟨p,m,n,u,v,hl,hf⟩ ⟨p',m',n',u',v',hl',hf'⟩ h
  have hk := congrArg Sigma.fst h
  change (p,m,n) = (p',m',n') at hk
  cases Prod.mk.inj hk with
  | intro hp hmn =>
    cases Prod.mk.inj hmn with
    | intro hm hn =>
      subst p'; subst m'; subst n'
      have huv : (u,v) = (u',v') := by exact eq_of_heq (Sigma.mk.inj h).2
      cases Prod.mk.inj huv with
      | intro hu hv => subst u'; subst v'; rfl

private noncomputable def ambientBasis (a b : ℕ) :
    Module.Basis (RawLabel a b) K (Ambient K a b) :=
  DFinsupp.basis (fun k =>
    (Pi.basisFun K (Fin k.2.1 → Bool)).tensorProduct (Pi.basisFun K (Fin k.2.2 → Bool)))

private noncomputable def embed (a b : ℕ) :
    CoordinateSpace K a b →ₗ[K] Ambient K a b :=
  (ambientBasis K a b).repr.symm.toLinearMap.comp (Finsupp.lmapDomain K K rawLabel)

private theorem embed_injective (a b : ℕ) : Function.Injective (embed K a b) :=
  (ambientBasis K a b).repr.symm.injective.comp (Finsupp.mapDomain_injective rawLabel_injective)

private theorem embed_single {a b : ℕ} (c : Coordinates a b) :
    embed K a b (Finsupp.single c 1) =
      DFinsupp.single (c.p,c.m,c.n) (Pi.single c.u 1 ⊗ₜ[K] Pi.single c.v 1) := by
  classical
  simp [embed, rawLabel, ambientBasis, DFinsupp.basis, Pi.basisFun_apply]

private noncomputable def ambientOp (a b : ℕ)
    (A : ∀ m n : ℕ, Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K))) :
    Module.End K (Ambient K a b) :=
  DFinsupp.mapRange.linearMap (fun k => A k.2.1 k.2.2)

private theorem ambientOp_single {a b : ℕ}
    (A : ∀ m n : ℕ, Module.End K (((Fin m → Bool) → K) ⊗[K] ((Fin n → Bool) → K)))
    (k : Key a b) (x : BinTensor K k) :
    ambientOp K a b A (DFinsupp.single k x) = DFinsupp.single k (A k.2.1 k.2.2 x) := by
  classical
  exact DFinsupp.mapRange_single (hf := fun k => (A k.2.1 k.2.2).map_zero)

variable [CharZero K]

omit [CharZero K] in
private theorem cast_delta {m : ℕ} (w : Fin m → Bool) :
    (fun u => ((Pi.single w (1 : ℚ) : (Fin m → Bool) → ℚ) u : K)) = Pi.single w 1 := by
  classical
  funext u
  by_cases h : u = w <;> simp [h]

private theorem cast_Hbin_delta (m : ℕ) (w : Fin m → Bool) :
    (fun u => (Hbin m (Pi.single w 1) u : K)) =
      ∑ j : Fin (m - 1), if lowers w j then Pi.single (swapBin j w) 1 else 0 := by
  classical
  rw [Hbin_delta]
  funext u
  simp only [Finset.sum_apply, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact congrFun (cast_delta K (swapBin j w)) u
  · simp

private theorem cast_Rbin_delta (m : ℕ) (w : Fin m → Bool) :
    (fun u => (Rbin m (Pi.single w 1) u : K)) =
      ∑ j : Fin (m - 1), if raises w j then
        (raisingCoefficient m j : K) • Pi.single (swapBin j w) 1 else 0 := by
  classical
  rw [Rbin_delta]
  funext u
  simp only [Finset.sum_apply, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simpa only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul] using
      congrArg (fun t : K => (raisingCoefficient m j : K) * t)
        (congrFun (cast_delta K (swapBin j w)) u)
  · simp

omit [CharZero K] in
private theorem dsingle_sum {a b : ℕ} (k : Key a b) {ι : Type*}
    (s : Finset ι) (f : ι → BinTensor K k) :
    DFinsupp.single k (Finset.sum s f) = Finset.sum s (fun i => DFinsupp.single k (f i)) :=
  map_sum (DFinsupp.lsingle k : BinTensor K k →ₗ[K] Ambient K a b) _ _

private theorem embed_h (a b : ℕ) :
    (embed K a b).comp (coordinateH K a b) =
      (ambientOp K a b (twoWeight K)).comp (embed K a b) := by
  apply (Finsupp.basisSingleOne : Module.Basis (Coordinates a b) K _).ext
  intro c
  change embed K a b (coordinateH K a b (Finsupp.single c 1)) = _
  simp only [coordinateH, Finsupp.linearCombination_single, one_smul, map_smul,
    LinearMap.comp_apply, Finsupp.coe_basisSingleOne, embed_single,
    ambientOp_single, (two_bin_action K c.m c.n).2 c.u c.v |>.1, DFinsupp.single_smul]

private theorem embed_e (a b : ℕ) :
    (embed K a b).comp (coordinateE K a b) =
      (ambientOp K a b (twoRaising K)).comp (embed K a b) := by
  classical
  apply (Finsupp.basisSingleOne : Module.Basis (Coordinates a b) K _).ext
  intro c
  change embed K a b (coordinateE K a b (Finsupp.single c 1)) = _
  simp only [coordinateE, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    LinearMap.comp_apply, Finsupp.coe_basisSingleOne, embed_single, ambientOp_single,
    (two_bin_action K c.m c.n).2 c.u c.v |>.2.1, cast_Rbin_delta,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, DFinsupp.single_add,
    dsingle_sum K (a := a) (b := b)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs
  all_goals first
    | (rw [map_smul, embed_single];
       simp [leftMove, rightMove, TensorProduct.smul_tmul,
         TensorProduct.tmul_smul, DFinsupp.single_smul]; rfl)
    | simp

private theorem embed_f (a b : ℕ) :
    (embed K a b).comp (coordinateF K a b) =
      (ambientOp K a b (twoLowering K)).comp (embed K a b) := by
  classical
  apply (Finsupp.basisSingleOne : Module.Basis (Coordinates a b) K _).ext
  intro c
  change embed K a b (coordinateF K a b (Finsupp.single c 1)) = _
  simp only [coordinateF, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    LinearMap.comp_apply, Finsupp.coe_basisSingleOne, embed_single, ambientOp_single,
    (two_bin_action K c.m c.n).2 c.u c.v |>.2.2, cast_Hbin_delta,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, DFinsupp.single_add,
    dsingle_sum K (a := a) (b := b)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs <;> simp [embed_single, leftMove, rightMove]

private theorem ambient_relations (a b : ℕ) :
    Sl2Relations (ambientOp K a b (twoWeight K)) (ambientOp K a b (twoRaising K))
      (ambientOp K a b (twoLowering K)) := by
  constructor
  · apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro k
    exact congrArg (fun A => A (x k)) (two_bin_action K k.2.1 k.2.2).1.ef
  · apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro k
    exact congrArg (fun A => A (x k)) (two_bin_action K k.2.1 k.2.2).1.he
  · apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro k
    exact congrArg (fun A => A (x k)) (two_bin_action K k.2.1 k.2.2).1.hf

private theorem coordinate_relations (a b : ℕ) :
    Sl2Relations (coordinateH K a b) (coordinateE K a b) (coordinateF K a b) := by
  have ih (x) := congrArg (fun A => A x) (embed_h K a b)
  dsimp only [LinearMap.comp_apply] at ih
  have ie (x) := congrArg (fun A => A x) (embed_e K a b)
  dsimp only [LinearMap.comp_apply] at ie
  have iff (x) := congrArg (fun A => A x) (embed_f K a b)
  dsimp only [LinearMap.comp_apply] at iff
  have aa := ambient_relations K a b
  constructor
  · apply LinearMap.ext
    intro x
    apply embed_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
    simp only [ie, iff, ih]
    exact LinearMap.congr_fun aa.ef (embed K a b x)
  · apply LinearMap.ext
    intro x
    apply embed_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul]
    simp only [ih, ie]
    exact LinearMap.congr_fun aa.he (embed K a b x)
  · apply LinearMap.ext
    intro x
    apply embed_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul]
    simp only [ih, iff]
    exact LinearMap.congr_fun aa.hf (embed K a b x)

omit [CharZero K] in
private noncomputable def coordinateLinear (a b : ℕ) :
    CoordinateSpace K a b ≃ₗ[K] MarkedSpace K a b :=
  Finsupp.lcongr (coordinateEquiv a b) (LinearEquiv.refl K K)

omit [CharZero K] in
/-- The diagonal sum of the two bin weights on the marked cover. -/
noncomputable def markedH (a b : ℕ) : Module.End K (MarkedSpace K a b) :=
  (coordinateLinear K a b).conjRingEquiv (coordinateH K a b)

omit [CharZero K] in
/-- The sum of the two bin raising actions on the marked cover. -/
noncomputable def markedE (a b : ℕ) : Module.End K (MarkedSpace K a b) :=
  (coordinateLinear K a b).conjRingEquiv (coordinateE K a b)

omit [CharZero K] in
/-- The sum of the two bin lowering actions on the marked cover. -/
noncomputable def markedF (a b : ℕ) : Module.End K (MarkedSpace K a b) :=
  (coordinateLinear K a b).conjRingEquiv (coordinateF K a b)

omit [CharZero K] in
private theorem conjugate_relations {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {h e f : Module.End K V} (T : V ≃ₗ[K] W) (a : Sl2Relations h e f) :
    Sl2Relations (T.conjRingEquiv h) (T.conjRingEquiv e) (T.conjRingEquiv f) := by
  constructor
  · simpa only [map_sub, map_mul] using congrArg T.conjRingEquiv a.ef
  · simpa only [map_sub, map_mul, two_smul, map_add] using congrArg T.conjRingEquiv a.he
  · simpa only [map_sub, map_mul, neg_smul, two_smul, map_neg, map_add] using
      congrArg T.conjRingEquiv a.hf

/-- The marked action satisfies the three sl₂ commutator relations. -/
theorem marked_relations (a b : ℕ) :
    Sl2Relations (markedH K a b) (markedE K a b) (markedF K a b) :=
  conjugate_relations K (coordinateLinear K a b) (coordinate_relations K a b)

#print axioms marked_relations

end D5.S3.Quantum.SpinChains.TwoWallSl2
