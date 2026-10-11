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

omit [CharZero K] in
private theorem commute_basis {a b : ℕ} (A B : Module.End K (CoordinateSpace K a b))
    (hh : ∀ c, A (B (Finsupp.single c 1)) = B (A (Finsupp.single c 1))) :
    Commute A B := by
  change A * B = B * A
  apply (Finsupp.basisSingleOne : Module.Basis (Coordinates a b) K _).ext
  exact hh

omit [CharZero K] in
private theorem swap_h (a b : ℕ) :
    Commute (Finsupp.lmapDomain K K coordinateSwap) (coordinateH K a b) := by
  apply commute_basis K
  intro c
  simp [coordinateH, coordinateSwap, add_comm, Finsupp.mapDomain_add]

omit [CharZero K] in
private theorem swap_e (a b : ℕ) :
    Commute (Finsupp.lmapDomain K K coordinateSwap) (coordinateE K a b) := by
  classical
  apply commute_basis K
  intro c
  simp only [coordinateE, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs <;> simp_all [coordinateSwap, leftMove, rightMove]

omit [CharZero K] in
private theorem swap_f (a b : ℕ) :
    Commute (Finsupp.lmapDomain K K coordinateSwap) (coordinateF K a b) := by
  classical
  apply commute_basis K
  intro c
  simp only [coordinateF, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs <;> simp_all [coordinateSwap, leftMove, rightMove]

omit [CharZero K] in
private theorem rotate_h {a b : ℕ} (t : Pos a b) :
    Commute (Finsupp.lmapDomain K K (coordinateRotate t)) (coordinateH K a b) := by
  apply commute_basis K
  intro c
  simp [coordinateH, coordinateRotate, Finsupp.mapDomain_add]

omit [CharZero K] in
private theorem rotate_e {a b : ℕ} (t : Pos a b) :
    Commute (Finsupp.lmapDomain K K (coordinateRotate t)) (coordinateE K a b) := by
  classical
  apply commute_basis K
  intro c
  simp only [coordinateE, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs <;> simp_all [coordinateRotate, leftMove, rightMove]

omit [CharZero K] in
private theorem rotate_f {a b : ℕ} (t : Pos a b) :
    Commute (Finsupp.lmapDomain K K (coordinateRotate t)) (coordinateF K a b) := by
  classical
  apply commute_basis K
  intro c
  simp only [coordinateF, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    split_ifs <;> simp_all [coordinateRotate, leftMove, rightMove]

omit [CharZero K] in
private theorem coordinateLinear_single {a b : ℕ} (c : Coordinates a b) :
    coordinateLinear K a b (Finsupp.single c 1) = markedDelta K (encode c) := by
  simp [coordinateLinear, Finsupp.lcongr_single, coordinateEquiv, markedDelta]

omit [CharZero K] in
private theorem conjugate_domain (a b : ℕ) (g : Coordinates a b → Coordinates a b)
    (G : MarkedWord a b → MarkedWord a b) (hh : ∀ c, encode (g c) = G (encode c)) :
    (coordinateLinear K a b).conjRingEquiv (Finsupp.lmapDomain K K g) =
      Finsupp.lmapDomain K K G := by
  apply (Finsupp.basisSingleOne : Module.Basis (MarkedWord a b) K _).ext
  intro x
  obtain ⟨c,rfl⟩ := (coordinateEquiv a b).surjective x
  change coordinateLinear K a b (Finsupp.lmapDomain K K g
    ((coordinateLinear K a b).symm (Finsupp.single (encode c) 1))) = _
  have hc : (coordinateLinear K a b).symm (Finsupp.single (encode c) 1) =
      Finsupp.single c 1 := by
    apply (coordinateLinear K a b).injective
    simp only [LinearEquiv.apply_symm_apply, coordinateLinear_single, markedDelta]
  rw [hc]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, coordinateLinear_single,
    markedDelta, Finsupp.coe_basisSingleOne, hh]
  rfl

omit [CharZero K] in
/-- Mark exchange and every cyclic translation commute with the marked action. -/
theorem marked_symmetries (a b : ℕ) :
    Commute (Jstar K a b) (markedH K a b) ∧
    Commute (Jstar K a b) (markedE K a b) ∧
    Commute (Jstar K a b) (markedF K a b) ∧
    ∀ t : Pos a b,
      Commute (markedTranslation K t) (markedH K a b) ∧
      Commute (markedTranslation K t) (markedE K a b) ∧
      Commute (markedTranslation K t) (markedF K a b) := by
  have hs : (coordinateLinear K a b).conjRingEquiv
      (Finsupp.lmapDomain K K coordinateSwap) = Jstar K a b :=
    conjugate_domain K a b coordinateSwap J (marked_coordinates a b).2.2.2.2.1
  have hr (t : Pos a b) : (coordinateLinear K a b).conjRingEquiv
      (Finsupp.lmapDomain K K (coordinateRotate t)) = markedTranslation K t :=
    conjugate_domain K a b (coordinateRotate t) (markedRotate t)
      ((marked_coordinates a b).2.2.2.2.2.2.2.1 t)
  refine ⟨?_, ?_, ?_, fun t => ⟨?_, ?_, ?_⟩⟩
  · change _ * markedH K a b = markedH K a b * _
    simpa only [map_mul, hs, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (swap_h K a b).eq
  · change _ * markedE K a b = markedE K a b * _
    simpa only [map_mul, hs, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (swap_e K a b).eq
  · change _ * markedF K a b = markedF K a b * _
    simpa only [map_mul, hs, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (swap_f K a b).eq
  · change _ * markedH K a b = markedH K a b * _
    simpa only [map_mul, hr, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (rotate_h K t).eq
  · change _ * markedE K a b = markedE K a b * _
    simpa only [map_mul, hr, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (rotate_e K t).eq
  · change _ * markedF K a b = markedF K a b * _
    simpa only [map_mul, hr, markedH, markedE, markedF] using
      congrArg (coordinateLinear K a b).conjRingEquiv (rotate_f K t).eq

#print axioms marked_relations
private noncomputable def descend (a b : ℕ) (A : Module.End K (MarkedSpace K a b)) :
    Module.End K (Space K a b) :=
  (2 : K)⁻¹ • (Q K a b).comp (A.comp (S K a b))

/-- The literal-word weight action obtained by forgetting the two marked lifts. -/
noncomputable def h (a b : ℕ) : Module.End K (Space K a b) :=
  descend K a b (markedH K a b)

/-- The literal-word raising action obtained from the marked cover. -/
noncomputable def e (a b : ℕ) : Module.End K (Space K a b) :=
  descend K a b (markedE K a b)

/-- The literal-word lowering action obtained from the marked cover. -/
noncomputable def f (a b : ℕ) : Module.End K (Space K a b) :=
  descend K a b (markedF K a b)

private theorem S_injective (a b : ℕ) : Function.Injective (S K a b) := by
  intro x y hh
  have he := congrArg (Q K a b) hh
  have hs := (marked_descent K a b).2.2.2.1
  have hx := LinearMap.congr_fun hs x
  have hy := LinearMap.congr_fun hs y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx hy
  rw [hx, hy] at he
  have hh := congrArg (fun z : Space K a b => (2 : K)⁻¹ • z) he
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul] using hh

omit [CharZero K] in
private theorem JS (a b : ℕ) (x : Space K a b) :
    Jstar K a b (S K a b x) = S K a b x := by
  have qs := (marked_descent K a b).2.2.2.1
  have sq := (marked_descent K a b).2.2.2.2.1
  have hqs := LinearMap.congr_fun qs x
  have hsq := LinearMap.congr_fun sq (S K a b x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.add_apply] at hqs hsq
  rw [hqs, map_smul, two_smul] at hsq
  exact (add_left_cancel hsq).symm

private theorem S_descend (a b : ℕ) (A : Module.End K (MarkedSpace K a b))
    (hh : Commute (Jstar K a b) A) (x : Space K a b) :
    S K a b (descend K a b A x) = A (S K a b x) := by
  have sq := LinearMap.congr_fun (marked_descent K a b).2.2.2.2.1 (A (S K a b x))
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at sq
  have hc := LinearMap.congr_fun hh.eq (S K a b x)
  change Jstar K a b (A (S K a b x)) = A (Jstar K a b (S K a b x)) at hc
  rw [JS] at hc
  simp only [descend, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
  rw [sq, hc]
  rw [← two_smul K (A (S K a b x))]
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul]

/-- The descended endomorphisms satisfy the sl₂ relations on literal cyclic words. -/
theorem literal_relations (a b : ℕ) : Sl2Relations (h K a b) (e K a b) (f K a b) := by
  have sy := marked_symmetries K a b
  have sh := S_descend K a b (markedH K a b) sy.1
  have se := S_descend K a b (markedE K a b) sy.2.1
  have sf := S_descend K a b (markedF K a b) sy.2.2.1
  have aa := marked_relations K a b
  constructor
  · apply LinearMap.ext
    intro x
    apply S_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h, e, f, sh, se, sf]
    exact LinearMap.congr_fun aa.ef (S K a b x)
  · apply LinearMap.ext
    intro x
    apply S_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_sub, map_smul, h, e, sh, se]
    exact LinearMap.congr_fun aa.he (S K a b x)
  · apply LinearMap.ext
    intro x
    apply S_injective K a b
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      map_sub, map_smul, h, f, sh, sf]
    exact LinearMap.congr_fun aa.hf (S K a b x)

private theorem descend_translation (a b : ℕ) (A : Module.End K (MarkedSpace K a b))
    (hj : Commute (Jstar K a b) A) (t : Pos a b)
    (ht : Commute (markedTranslation K t) A) :
    Commute (translation K t) (descend K a b A) := by
  change translation K t * descend K a b A = descend K a b A * translation K t
  apply LinearMap.ext
  intro x
  apply S_injective K a b
  have hs (y) := LinearMap.congr_fun ((marked_descent K a b).2.2.2.2.2.1 t) y
  dsimp only [LinearMap.comp_apply] at hs
  simp only [Module.End.mul_apply]
  rw [← hs, S_descend K a b A hj, S_descend K a b A hj, ← hs]
  exact LinearMap.congr_fun ht.eq (S K a b x)

/-- Every cyclic translation, and hence U, commutes with all three literal operators. -/
theorem literal_translation (a b : ℕ) :
    (∀ t : Pos a b, Commute (translation K t) (h K a b) ∧
      Commute (translation K t) (e K a b) ∧ Commute (translation K t) (f K a b)) ∧
    Commute (U K a b) (h K a b) ∧ Commute (U K a b) (e K a b) ∧
    Commute (U K a b) (f K a b) := by
  have sy := marked_symmetries K a b
  have all (t : Pos a b) : Commute (translation K t) (h K a b) ∧
      Commute (translation K t) (e K a b) ∧ Commute (translation K t) (f K a b) :=
    ⟨descend_translation K a b _ sy.1 t (sy.2.2.2 t).1,
      descend_translation K a b _ sy.2.1 t (sy.2.2.2 t).2.1,
      descend_translation K a b _ sy.2.2.1 t (sy.2.2.2 t).2.2⟩
  exact ⟨all, all 1⟩

#print axioms marked_relations
#print axioms marked_symmetries
#print axioms literal_relations
#print axioms literal_translation

end D5.S3.Quantum.SpinChains.TwoWallSl2
