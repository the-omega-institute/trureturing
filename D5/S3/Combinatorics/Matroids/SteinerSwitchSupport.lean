/- GID: D5/S3/Combinatorics/Matroids/SteinerSwitchSupport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSwitchSupport
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Binary subspaces determine simultaneous counts in one labelled triple system. -/

import D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
import D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount

/-! # Supports and counts of simultaneous Steiner switches -/

namespace D5.S3.Combinatorics.Matroids.SteinerSwitchSupport

open Module Submodule LinearMap Function Set
open D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
  (returnRow firstReturn realizesExactlyCompatibleReturns)
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
  (extensionMul extensionSteinerAndCentre)
open D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (labelledSwitchCount pointedNumbering squareFixed steinerSquarePeriod)
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap (Covered Uncovered)
open D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations (translate)
open D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch (pointDeletedFamily)
open D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches (SuccessfulStart)

private theorem vanishingPattern {K I V A : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    (rows : I → V) (vanishes : I → Prop) :
    (∃ f : V →ₗ[K] A, ∀ i, f (rows i) = 0 ↔ vanishes i) ↔
      ∃ H : Submodule K V, finrank K (V ⧸ H) ≤ finrank K A ∧
        ∀ i, rows i ∈ H ↔ vanishes i := by
  constructor
  · rintro ⟨f, h⟩
    refine ⟨ker f, ?_, h⟩
    rw [f.quotKerEquivRange.finrank_eq]
    exact Submodule.finrank_le (range f)
  · rintro ⟨H, hd, h⟩
    obtain ⟨f, hf⟩ := finrank_le_iff_exists_linearMap.mp hd
    refine ⟨f.comp H.mkQ, fun i => ?_⟩
    rw [LinearMap.comp_apply, ← f.map_zero, hf.eq_iff]
    change Submodule.Quotient.mk (p := H) (rows i) = 0 ↔ vanishes i
    exact (Submodule.Quotient.mk_eq_zero (p := H)).trans (h i)

private theorem steinerVanishingPattern {I L A : Type*} [Finite L] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A]
    (e : L) (p q rep : I → L) (G : I → SimpleGraph L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (edges : ∀ i u v, (G i).Adj u v ↔ p i * u = v ∨ q i * u = v)
    (vanishes : I → Prop) :
    (∃ labels : Set L → A, ∃ target : I → A,
      (∀ i, target i = 0 ↔ vanishes i) ∧
      letI := extensionMul e labels
      ∀ i x, (G i).Reachable (rep i) x → ∀ a : A,
        (fun y : L × A => (p i, 0) * ((q i, 0) * y))^[
          minimalPeriod (fun y => p i * (q i * y)) x] (x, a) = (x, a + target i)) ↔
      ∃ H : Submodule (ZMod 2) (Set L →₀ ZMod 2),
        finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A ∧
          ∀ i, returnRow e (p i) (q i) (rep i) ∈ H ↔ vanishes i := by
  classical
  letI : Fintype (Set L) := Fintype.ofFinite (Set L)
  let rows := fun i => returnRow e (p i) (q i) (rep i)
  rw [← vanishingPattern rows vanishes]
  constructor
  · rintro ⟨labels, target, hzero, hret⟩
    refine ⟨Finsupp.linearCombination (ZMod 2) labels, fun i => ?_⟩
    have heq : Finsupp.linearCombination (ZMod 2) labels (rows i) = target i := by
      have h := (firstReturn e labels (p i) (q i) (rep i) 0).symm.trans
        (hret i (rep i) SimpleGraph.Reachable.rfl 0)
      simpa only [rows, zero_add] using congrArg Prod.snd h
    rw [heq]
    exact hzero i
  · rintro ⟨f, hf⟩
    let target := fun i => f (rows i)
    have composition : Finsupp.linearCombination (ZMod 2) target =
        f.comp (Finsupp.linearCombination (ZMod 2) rows) :=
      Finsupp.linearCombination_linear_comp (ZMod 2) (v := rows) f
    have compatible c (hz : Finsupp.linearCombination (ZMod 2) rows c = 0) :
        Finsupp.linearCombination (ZMod 2) target c = 0 := by
      rw [composition, LinearMap.comp_apply, hz, map_zero]
    obtain ⟨labels, _, _, _, _, hret⟩ :=
      (realizesExactlyCompatibleReturns e p q rep G unit comm invol centreless edges target).mpr
        compatible
    exact ⟨labels, target, hf, hret⟩

private theorem patternAfterContraction {K I V A : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    (rows : I → V) (vanishes : I → Prop) :
    let Z := Submodule.span K (rows '' {i | vanishes i})
    (∃ f : V →ₗ[K] A, ∀ i, f (rows i) = 0 ↔ vanishes i) ↔
      ∃ H : Submodule K (V ⧸ Z), finrank K ((V ⧸ Z) ⧸ H) ≤ finrank K A ∧
        ∀ i, ¬ vanishes i → Z.mkQ (rows i) ∉ H := by
  let Z := Submodule.span K (rows '' {i | vanishes i})
  change _ ↔ ∃ H : Submodule K (V ⧸ Z), _ ∧
    ∀ i, ¬ vanishes i → Z.mkQ (rows i) ∉ H
  have hz (i : I) (hi : vanishes i) : Z.mkQ (rows i) = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := Z)).mpr
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  constructor
  · rintro ⟨f, hf⟩
    have factors : Z ≤ ker f := Submodule.span_le.mpr (by
      rintro _ ⟨i, hi, rfl⟩
      exact (hf i).mpr hi)
    have descends (i : I) : Z.liftQ f factors (Z.mkQ (rows i)) = 0 ↔ vanishes i := by
      change Z.liftQ f factors (Submodule.Quotient.mk (p := Z) (rows i)) = 0 ↔ vanishes i
      rw [Submodule.liftQ_apply]
      exact hf i
    obtain ⟨H, hd, hH⟩ := (vanishingPattern (fun i => Z.mkQ (rows i)) vanishes).mp
      ⟨Z.liftQ f factors, descends⟩
    exact ⟨H, hd, fun i hi hm => hi ((hH i).mp hm)⟩
  · rintro ⟨H, hd, hH⟩
    have pattern (i : I) : Z.mkQ (rows i) ∈ H ↔ vanishes i := by
      constructor
      · intro hi
        by_contra nv
        exact hH i nv hi
      · intro hi
        rw [hz i hi]
        exact H.zero_mem
    obtain ⟨f, hf⟩ := (vanishingPattern (fun i => Z.mkQ (rows i)) vanishes).mpr
      ⟨H, hd, pattern⟩
    exact ⟨f.comp Z.mkQ, hf⟩

/-- After the prescribed zero rows are factored out, the remaining rows avoid a subspace
of codimension at most the fibre dimension. -/
def HasAvoidingSubspace {K I V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (rows : I → V) (vanishes : I → Prop) (dimension : ℕ) : Prop :=
  let W := Submodule.span K (Set.range rows)
  let r : I → W := fun i => ⟨rows i, Submodule.subset_span (Set.mem_range_self i)⟩
  let Z := Submodule.span K (r '' {i | vanishes i})
  ∃ H : Submodule K (W ⧸ Z), finrank K ((W ⧸ Z) ⧸ H) ≤ dimension ∧
    ∀ i, ¬ vanishes i → Z.mkQ (r i) ∉ H

private theorem patternOnRowSpan {K I V A : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    (rows : I → V) (vanishes : I → Prop) :
    (∃ f : V →ₗ[K] A, ∀ i, f (rows i) = 0 ↔ vanishes i) ↔
      HasAvoidingSubspace (K := K) rows vanishes (finrank K A) := by
  let W := Submodule.span K (Set.range rows)
  let r : I → W := fun i => ⟨rows i, Submodule.subset_span (Set.mem_range_self i)⟩
  have restrict :
      (∃ f : V →ₗ[K] A, ∀ i, f (rows i) = 0 ↔ vanishes i) ↔
        ∃ g : W →ₗ[K] A, ∀ i, g (r i) = 0 ↔ vanishes i := by
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨f.comp W.subtype, hf⟩
    · rintro ⟨g, hg⟩
      obtain ⟨f, he⟩ := g.exists_extend
      refine ⟨f, fun i => ?_⟩
      have read := LinearMap.congr_fun he (r i)
      change f (rows i) = g (r i) at read
      rw [read]
      exact hg i
  exact restrict.trans (patternAfterContraction r vanishes)

/-- A zero-return pattern is possible precisely at the codimensions allowed by the fibre. -/
theorem realizesReturnSupport {I L A : Type*} [Finite L] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A]
    (e : L) (p q rep : I → L) (G : I → SimpleGraph L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (edges : ∀ i u v, (G i).Adj u v ↔ p i * u = v ∨ q i * u = v)
    (vanishes : I → Prop) :
    (∃ labels : Set L → A, ∃ target : I → A,
      (∀ i, target i = 0 ↔ vanishes i) ∧
      letI := extensionMul e labels
      ∀ i x, (G i).Reachable (rep i) x → ∀ a : A,
        (fun y : L × A => (p i, 0) * ((q i, 0) * y))^[
          minimalPeriod (fun y => p i * (q i * y)) x] (x, a) = (x, a + target i)) ↔
      HasAvoidingSubspace (K := ZMod 2) (fun i => returnRow e (p i) (q i) (rep i))
        vanishes (finrank (ZMod 2) A) := by
  classical
  let _ : Fintype (Set L) := Fintype.ofFinite (Set L)
  let rows := fun i => returnRow e (p i) (q i) (rep i)
  exact (steinerVanishingPattern e p q rep G unit comm invol centreless edges vanishes).trans
    ((vanishingPattern (A := A) rows vanishes).symm.trans
      (patternOnRowSpan (A := A) rows vanishes))

private theorem selectedByRow {L A : Type*} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e p q x : L) (labels : Set L → A) (a : A)
    (comm : ∀ u v : L, u * v = v * u)
    (invol : ∀ u v : L, u * (u * v) = v) (different : p ≠ q)
    (involExt : letI := extensionMul e labels
      ∀ u v : L × A, u * (u * v) = v) :
    letI := extensionMul e labels
    let g : L → L := fun z => p * (q * z)
    (q, 0) * ((p, 0) * (x, a)) ≠ (p, 0) * ((q, 0) * (x, a)) ↔
      g (g x) ≠ x ∨ Finsupp.linearCombination (ZMod 2) labels (returnRow e p q x) ≠ 0 := by
  letI := extensionMul e labels
  let g : L → L := fun z => p * (q * z)
  let P : L × A → L × A := fun y => (p, 0) * y
  let Q : L × A → L × A := fun y => (q, 0) * y
  let value := Finsupp.linearCombination (ZMod 2) labels (returnRow e p q x)
  change (¬ Q (P (x, a)) = P (Q (x, a))) ↔ g (g x) ≠ x ∨ value ≠ 0
  have hp : Involutive P := involExt (p, 0)
  have hq : Involutive Q := involExt (q, 0)
  rw [not_congr (squareFixed hp hq (x, a))]
  by_cases square : g (g x) = x
  · have hperiod : minimalPeriod g x = 2 := steinerSquarePeriod comm invol different square
    have fibre : (P ∘ Q)^[minimalPeriod g x] (x, a) = (x, a + value) :=
      firstReturn e labels p q x a
    rw [hperiod] at fibre
    rw [fibre]
    simp [square]
  · refine ⟨fun _ => Or.inl square, fun _ h => square ?_⟩
    exact congrArg Prod.fst h

private theorem labelsWithKernel {L A : Type*} [Finite L] [Finite A]
    [AddCommGroup A] [Module (ZMod 2) A]
    (H : Submodule (ZMod 2) (Set L →₀ ZMod 2))
    (dimension : finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A) :
    ∃ labels : Set L → A, ker (Finsupp.linearCombination (ZMod 2) labels) = H := by
  classical
  obtain ⟨g, injective⟩ := finrank_le_iff_exists_linearMap.mp dimension
  let f : (Set L →₀ ZMod 2) →ₗ[ZMod 2] A := g.comp H.mkQ
  let coefficients := Finsupp.lift A (ZMod 2) (Set L)
  let labels := coefficients.symm f
  have table : Finsupp.linearCombination (ZMod 2) labels = f := by
    apply LinearMap.ext
    intro row
    rw [Finsupp.linearCombination_apply, ← Finsupp.lift_apply]
    exact congrArg (fun map : (Set L →₀ ZMod 2) →ₗ[ZMod 2] A => map row)
      (coefficients.apply_symm_apply f)
  refine ⟨labels, table.symm ▸ ?_⟩
  ext row
  rw [mem_ker, show f row = g (H.mkQ row) from rfl, ← g.map_zero, injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero (p := H)

private theorem noncommutingCount {L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e p q : L) (labels : Set L → A) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (different : p ≠ q)
    (involExt : letI := extensionMul e labels
      ∀ x y : L × A, x * (x * y) = y) :
    letI := extensionMul e labels
    ({y : L × A | (q, 0) * ((p, 0) * y) ≠ (p, 0) * ((q, 0) * y)} : Set (L × A)).ncard =
      Nat.card A * ({x : L |
        let g := fun y : L => p * (q * y)
        g (g x) ≠ x ∨ returnRow e p q x ∉ ker (Finsupp.linearCombination (ZMod 2) labels)} : Set L).ncard := by
  letI := extensionMul e labels
  have fibres : ({y : L × A | (q, 0) * ((p, 0) * y) ≠
      (p, 0) * ((q, 0) * y)} : Set (L × A)) =
      ({x : L | let g := fun y : L => p * (q * y)
        g (g x) ≠ x ∨ returnRow e p q x ∉ ker (Finsupp.linearCombination (ZMod 2) labels)} : Set L) ×ˢ
        (Set.univ : Set A) := by
    ext ⟨x, a⟩
    simpa only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, mem_ker] using
      selectedByRow e p q x labels a comm invol different involExt
  rw [fibres, Set.ncard_prod, Set.ncard_univ, Nat.mul_comm]

/-- A common family of counts is realizable precisely by the fibre-sized subspace counts. -/
theorem commonSwitchCounts {J L A : Type*} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q : J → L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (different : ∀ i, p i ≠ q i) (counts : J → ℕ) :
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      Set.center (L × A) = {x | x.1 = e} ∧
      ∀ i, ({y : L × A | (q i, 0) * ((p i, 0) * y) ≠
        (p i, 0) * ((q i, 0) * y)} : Set (L × A)).ncard = counts i) ↔
      ∃ H : Submodule (ZMod 2) (Set L →₀ ZMod 2),
        finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A ∧
        ∀ i, Nat.card A * ({x : L |
          let g := fun y : L => p i * (q i * y)
          g (g x) ≠ x ∨ returnRow e (p i) (q i) x ∉ H} : Set L).ncard = counts i := by
  classical
  let _ : Fintype (Set L) := Fintype.ofFinite (Set L)
  let evaluate (labels : Set L → A) := Finsupp.linearCombination (ZMod 2) labels
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  have law (labels : Set L → A) :=
    extensionSteinerAndCentre e labels unit comm invol twice centreless
  have formula (labels : Set L → A) (i : J) :=
    noncommutingCount e (p i) (q i) labels comm invol (different i) (law labels).2.2.1
  constructor
  · rintro ⟨labels, _, realized⟩
    refine ⟨ker (evaluate labels), ?_, fun i => (formula labels i).symm.trans (realized i)⟩
    rw [(evaluate labels).quotKerEquivRange.finrank_eq]
    exact Submodule.finrank_le (range (evaluate labels))
  · rintro ⟨H, dimension, constrained⟩
    obtain ⟨labels, kernel⟩ := labelsWithKernel (A := A) H dimension
    refine ⟨labels, (law labels).2.2.2, fun i => ?_⟩
    rw [formula labels i, kernel]
    exact constrained i

/-- The same labelled triple system realizes every count in the chosen subspace profile. -/
theorem labelledCommonSwitchCounts {J L A : Type*}
    [Finite L] [Nontrivial L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q : J → L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (hp : ∀ j, p j ≠ e) (hq : ∀ j, q j ≠ e) (different : ∀ j, p j ≠ q j)
    (H : Submodule (ZMod 2) (Set L →₀ ZMod 2))
    (dimension : finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A) :
    ∃ (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      letI := extensionMul e labels
      label none = (e, 0) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      ker (Finsupp.linearCombination (ZMod 2) labels) = H ∧
      (∀ i a, label (translate valid cover i a) = label (some i) * label a) ∧
      ∀ j, ∃ (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
        label (some i) = (p j, 0) ∧ label (some (i.succAbove v)) = (q j, 0) ∧
        (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
        ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
          Nat.card A * ({x : L |
            let g := fun y : L => p j * (q j * y)
            g (g x) ≠ x ∨ returnRow e (p j) (q j) x ∉ H} : Set L).ncard := by
  classical
  obtain ⟨labels, kernel⟩ := labelsWithKernel (A := A) H dimension
  have twice (a : A) : a + a = 0 := by
    have two : (2 : ZMod 2) = 0 := by decide
    simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
  letI := extensionMul e labels
  obtain ⟨idExt, commExt, invExt, centre⟩ :=
    extensionSteinerAndCentre e labels unit comm invol twice centreless
  have pNe (j : J) : (p j, (0 : A)) ≠ (e, 0) := fun h => hp j (congrArg Prod.fst h)
  have qNe (j : J) : (q j, (0 : A)) ≠ (e, 0) := fun h => hq j (congrArg Prod.fst h)
  have nonidentity : ∃ y : L × A, y ≠ (e, 0) := by
    obtain ⟨x, hx⟩ := exists_ne e
    exact ⟨(x, 0), fun h => hx (congrArg Prod.fst h)⟩
  obtain ⟨r, label, zero, locate⟩ := pointedNumbering (e, (0 : A)) nonidentity
  obtain ⟨S, valid, cover, transport, byDeleted⟩ :=
    labelledSwitchCount label (by simpa only [zero] using idExt) commExt invExt
  refine ⟨labels, r, label, S, valid, cover, zero, centre, kernel, transport, fun j => ?_⟩
  obtain ⟨i, v, hi, hv'⟩ := locate (p j, 0) (q j, 0) (pNe j) (qNe j)
    (fun h => different j (congrArg Prod.fst h))
  obtain ⟨m, leave, byStart⟩ := byDeleted i
  refine ⟨i, v, m, hi, hv', leave, ?_⟩
  have read := (byStart v).2
  rw [hi, hv'] at read
  have count := noncommutingCount e (p j) (q j) labels comm invol (different j) invExt
  rw [kernel] at count
  exact read.trans count

end D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
