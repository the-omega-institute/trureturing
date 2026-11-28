/- GID: D5/S3/Quantum/SpinChains/MiaoFukaiHamiltonians
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/MiaoFukaiHamiltonians
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact periodic ladder Hamiltonians and a family of singleton charge components. -/

module

public import D5.S3.Quantum.SpinChains.MiaoFukaiChargeSector
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Miao and Fukai, arXiv:2611.29351v1, Eqs. (46), (50), (57)–(59), and (71).
The staggered Hamiltonian uses the normalized density sum with the minus-sign
base fixed by Eq. (50). In the zero-based indexing of the periodic chain the
first coordinate of each staggered pair is odd. -/

@[expose] public section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves

noncomputable section

def h46minus {L : ℕ} (Δ : ℂ) (j : Fin L) : Op L := T j - Δ • T j ^ 2

def h46plus {L : ℕ} (Δ : ℂ) (j : Fin L) : Op L := C j * (S j + Δ • S j ^ 2)

def h71 {L : ℕ} (Δ : ℂ) (j : Fin L) : Op L :=
  Ue j * (A j + Δ • DA j) + Um j * (F j + Δ • DF j)

def H46minus (L : ℕ) (Δ : ℂ) : Op L := ∑ j : Fin L, h46minus Δ j

def H46plus (L : ℕ) (Δ : ℂ) : Op L := ∑ j : Fin L, h46plus Δ j

def H71 (L : ℕ) (Δ : ℂ) : Op L := ∑ j : Fin L, h71 Δ j

/-- The plus-sign printing in Eq. (46) is the minus family at the opposite parameter. -/
theorem h46plus_eq_h46minus_neg {L : ℕ} (hL : 5 ≤ L) (Δ : ℂ) (j : Fin L) :
    h46plus Δ j = h46minus (-Δ) j := by
  rw [h46plus, mul_add, Matrix.mul_smul, ← controlled_square hL, ← T,
    h46minus, neg_smul, sub_neg_eq_add]

/-- The explicit Eq. (71) density agrees with the plus-sign printing of Eq. (46). -/
theorem h71_eq_h46plus {L : ℕ} (hL : 5 ≤ L) (Δ : ℂ) (j : Fin L) :
    h71 Δ j = h46plus Δ j := by
  obtain ⟨hlinear, hsquare⟩ := ladder_density_parts hL j
  rw [h46plus_eq_h46minus_neg hL, h46minus, neg_smul, sub_neg_eq_add,
    hlinear, hsquare, smul_add, h71, mul_add, mul_add, Matrix.mul_smul, Matrix.mul_smul]
  ac_rfl

def deltaH {L : ℕ} (μ v₀ : ℂ) (j k : Fin L) : Op L :=
  let aPlus := Complex.sin v₀ / Complex.sin (v₀ + μ)
  let aMinus := Complex.sin v₀ / Complex.sin (v₀ - μ)
  let kPlus := Complex.sin μ / Complex.sin (v₀ + μ) - 1
  let kMinus := -Complex.sin μ / Complex.sin (v₀ - μ) - 1
  let X := T j
  let Y := T k
  aPlus • (Y * X) + aMinus • (X * Y) +
    (2 * aPlus * aMinus * Complex.cos μ) • (X ^ 2 * Y ^ 2) +
    kPlus • (Y * X ^ 2) + kPlus • (Y ^ 2 * X) +
    kMinus • (X * Y ^ 2) + kMinus • (X ^ 2 * Y)

def staggeredPair {L : ℕ} (n : Fin (L / 2)) : Fin L × Fin L :=
  let j : Fin L := ⟨2 * n.val + 1, by have hn := n.isLt; omega⟩
  (j, next j)

theorem staggered_pair_indices {L : ℕ} (n : Fin (L / 2)) :
    (staggeredPair n).1.val = 2 * n.val + 1 ∧
      (staggeredPair n).2.val = (2 * n.val + 2) % L := by
  refine ⟨rfl, ?_⟩
  change (next (staggeredPair n).1).val = _
  rw [next_val, show (staggeredPair n).1.val = 2 * n.val + 1 from rfl]
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
  · have hn := n.isLt
    rw [show 2 * n.val + 2 = L by omega, Nat.mod_self]

/-- The final one-based pair is `(L, 1)`. -/
theorem staggered_last_pair {L : ℕ} (hL : 2 ≤ L) (he : Even L) :
    let n : Fin (L / 2) := ⟨L / 2 - 1, by omega⟩
    (staggeredPair n).1.val = L - 1 ∧ (staggeredPair n).2.val = 0 := by
  obtain ⟨m, hm⟩ := he
  dsimp only
  rw [(staggered_pair_indices _).1, (staggered_pair_indices _).2]
  exact ⟨by omega, by rw [show 2 * (L / 2 - 1) + 2 = L by omega, Nat.mod_self]⟩

def staggeredH (L : ℕ) (μ v₀ : ℂ) : Op L :=
  H46minus L (Complex.cos μ) +
    ∑ n : Fin (L / 2), deltaH μ v₀ (staggeredPair n).1 (staggeredPair n).2

def Nonsingular (μ v₀ : ℂ) : Prop :=
  Complex.sin (v₀ + μ) * Complex.sin (v₀ - μ) ≠ 0

def Kills {L : ℕ} (M : Op L) (x : Config L) : Prop :=
  M *ᵥ ket x = 0 ∧ ket x ᵥ* M = 0

private theorem kills_add {L : ℕ} {M N : Op L} {x : Config L}
    (hM : Kills M x) (hN : Kills N x) : Kills (M + N) x := by
  simp [Kills, Matrix.add_mulVec, Matrix.vecMul_add, hM.1, hM.2, hN.1, hN.2]

private theorem kills_sub {L : ℕ} {M N : Op L} {x : Config L}
    (hM : Kills M x) (hN : Kills N x) : Kills (M - N) x := by
  simp [Kills, Matrix.sub_mulVec, Matrix.vecMul_sub, hM.1, hM.2, hN.1, hN.2]

private theorem kills_smul {L : ℕ} {M : Op L} {x : Config L} {c : ℂ}
    (hM : Kills M x) : Kills (c • M) x := by
  simp [Kills, Matrix.smul_mulVec, Matrix.vecMul_smul, hM.1, hM.2]

private theorem kills_mul {L : ℕ} {M N : Op L} {x : Config L}
    (hM : Kills M x) (hN : Kills N x) : Kills (M * N) x := by
  simp [Kills, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul, hN.1, hM.2]

private theorem kills_square {L : ℕ} {M : Op L} {x : Config L}
    (hM : Kills M x) : Kills (M ^ 2) x := by
  simpa only [pow_two] using kills_mul hM hM

private theorem kills_sum {L : ℕ} {ι : Type} [Fintype ι] {M : ι → Op L}
    {x : Config L} (hM : ∀ i, Kills (M i) x) : Kills (∑ i, M i) x := by
  simp [Kills, Matrix.sum_mulVec, Matrix.vecMul_sum, fun i => (hM i).1, fun i => (hM i).2]

private theorem ordinary_local_kills {L : ℕ} (hL : 5 ≤ L) {x : Config L} (hx : Jammed x)
    (Δ : ℂ) (j : Fin L) :
    Kills (h46minus Δ j) x ∧ Kills (h46plus Δ j) x ∧ Kills (h71 Δ j) x := by
  have hT : Kills (T j) x := jammed_kills hL j hx
  have hminus (a : ℂ) : Kills (h46minus a j) x :=
    kills_sub hT (kills_smul (kills_square hT))
  rw [h71_eq_h46plus hL, h46plus_eq_h46minus_neg hL]
  exact ⟨hminus Δ, hminus (-Δ), hminus (-Δ)⟩

/-- All three printed ordinary Hamiltonian sums annihilate a jammed basis word on both sides. -/
theorem ordinary_kills {L : ℕ} (hL : 5 ≤ L) {x : Config L} (hx : Jammed x) (Δ : ℂ) :
    Kills (H46minus L Δ) x ∧ Kills (H46plus L Δ) x ∧ Kills (H71 L Δ) x :=
  ⟨kills_sum fun j => (ordinary_local_kills hL hx Δ j).1,
    kills_sum fun j => (ordinary_local_kills hL hx Δ j).2.1,
    kills_sum fun j => (ordinary_local_kills hL hx Δ j).2.2⟩

private theorem delta_kills {L : ℕ} (hL : 5 ≤ L) {x : Config L} (hx : Jammed x)
    (μ v₀ : ℂ) (j k : Fin L) : Kills (deltaH μ v₀ j k) x := by
  have hX : Kills (T j) x := jammed_kills hL j hx
  have hY : Kills (T k) x := jammed_kills hL k hx
  unfold deltaH
  dsimp only
  repeat first | exact hX | exact hY | apply kills_add | apply kills_smul |
    apply kills_mul | apply kills_square

/-- The normalized density sum in Eq. (57) annihilates the same jammed word. -/
theorem staggered_kills {L : ℕ} (hL : 5 ≤ L) {x : Config L} (hx : Jammed x)
    (_he : Even L) (μ v₀ : ℂ) (_hμv : Nonsingular μ v₀) :
    Kills (staggeredH L μ v₀) x :=
  kills_add (ordinary_kills hL hx (Complex.cos μ)).1
    (kills_sum fun n => delta_kills hL hx μ v₀ (staggeredPair n).1 (staggeredPair n).2)

def PreservesCharge {L : ℕ} (M : Op L) : Prop :=
  ∀ y x, charge y ≠ charge x → M y x = 0

private theorem charge_add {L : ℕ} {M N : Op L}
    (hM : PreservesCharge M) (hN : PreservesCharge N) : PreservesCharge (M + N) := by
  intro y x h
  simp [hM y x h, hN y x h]

private theorem charge_sub {L : ℕ} {M N : Op L}
    (hM : PreservesCharge M) (hN : PreservesCharge N) : PreservesCharge (M - N) := by
  intro y x h
  simp [hM y x h, hN y x h]

private theorem charge_smul {L : ℕ} {M : Op L} {c : ℂ}
    (hM : PreservesCharge M) : PreservesCharge (c • M) := by
  intro y x h
  simp [hM y x h]

private theorem charge_mul {L : ℕ} {M N : Op L}
    (hM : PreservesCharge M) (hN : PreservesCharge N) : PreservesCharge (M * N) := by
  intro y x h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : charge y = charge z
  · rw [hN z x (fun he => h (hz.trans he)), mul_zero]
  · rw [hM y z hz, zero_mul]

private theorem charge_sum {L : ℕ} {ι : Type} [Fintype ι] {M : ι → Op L}
    (hM : ∀ i, PreservesCharge (M i)) : PreservesCharge (∑ i, M i) := by
  intro y x h
  simp [Matrix.sum_apply, fun i => hM i y x h]

private theorem T_preserves_charge {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    PreservesCharge (T j) := by
  intro y x h
  by_contra hn
  exact h (charge_of_nonzero_entry hL j hn)

/-- All three ordinary sums are block diagonal for the unextended projector charge. -/
theorem ordinary_preserves_charge {L : ℕ} (hL : 5 ≤ L) (Δ : ℂ) :
    PreservesCharge (H46minus L Δ) ∧ PreservesCharge (H46plus L Δ) ∧
      PreservesCharge (H71 L Δ) := by
  have hminus (a : ℂ) (j : Fin L) : PreservesCharge (h46minus a j) := by
    rw [h46minus, pow_two]
    have hT := T_preserves_charge hL j
    exact charge_sub hT (charge_smul (charge_mul hT hT))
  refine ⟨charge_sum (hminus Δ), charge_sum fun j => ?_, charge_sum fun j => ?_⟩
  · rw [h46plus_eq_h46minus_neg hL]
    exact hminus (-Δ) j
  · rw [h71_eq_h46plus hL, h46plus_eq_h46minus_neg hL]
    exact hminus (-Δ) j

/-- The normalized staggered sum is block diagonal for the same charge. -/
theorem staggered_preserves_charge {L : ℕ} (hL : 5 ≤ L) (μ v₀ : ℂ) :
    PreservesCharge (staggeredH L μ v₀) := by
  apply charge_add (ordinary_preserves_charge hL (Complex.cos μ)).1
  apply charge_sum
  intro n
  simp only [deltaH, pow_two]
  repeat first | apply T_preserves_charge hL | apply charge_add | apply charge_smul | apply charge_mul

abbrev Sector (L q : ℕ) := {x : Config L // charge x = q}

/-- The support of the Hamiltonian restricted to the fixed-charge basis. -/
def sectorSupport {L q : ℕ} (M : Op L) : SimpleGraph (Sector L q) where
  Adj x y := x ≠ y ∧ (M y.val x.val ≠ 0 ∨ M x.val y.val ≠ 0)
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem singleton_of_kills {L q : ℕ} {M : Op L} (x : Sector L q)
    (h : Kills M x.val) :
    ((sectorSupport M).connectedComponentMk x).supp = {x} := by
  classical
  obtain ⟨hcol, hrow⟩ := h
  rw [ket, Matrix.mulVec_single_one] at hcol
  rw [ket, Matrix.single_one_vecMul] at hrow
  have hi : (sectorSupport M).IsIsolated x := by
    intro y hy
    rcases hy.2 with hy | hy
    · exact hy (congrFun hcol y.val)
    · exact hy (congrFun hrow y.val)
  ext y
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    Set.mem_singleton_iff]
  constructor
  · intro hr
    by_contra hne
    exact ((SimpleGraph.notMem_support_iff_isIsolated _ _).mpr hi)
      (SimpleGraph.mem_support_of_reachable (Ne.symm hne) hr.symm)
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- The labelled tile family, viewed in its common charge sector. -/
def sectorEmbedding {L : ℕ} (hL : 12 ≤ L) : (Fin (blocks L) → Bool) ↪ Sector L (targetCharge L) where
  toFun b := ⟨(jamEmbedding hL b).val, (jamEmbedding hL b).property.1⟩
  inj' := by
    intro b c h
    apply (jamEmbedding hL).injective
    exact Subtype.ext (congrArg Subtype.val h)

/-- Every vertex in the constructed family has energy zero and a singleton
component for each ordinary Hamiltonian and for every applicable staggered sum. -/
theorem tiled_singleton_components {L : ℕ} (hL : 12 ≤ L) :
    Odd (L - targetCharge L) ∧ (Finset.univ.map (sectorEmbedding hL)).card = 2 ^ blocks L ∧
    ∀ b : Fin (blocks L) → Bool,
      let x := sectorEmbedding hL b
      ket x.val ≠ 0 ∧ NP L *ᵥ ket x.val = (targetCharge L : ℂ) • ket x.val ∧
      (∀ Δ : ℂ,
        (Kills (H46minus L Δ) x.val ∧ ((sectorSupport (H46minus L Δ)).connectedComponentMk x).supp = {x}) ∧
        (Kills (H46plus L Δ) x.val ∧ ((sectorSupport (H46plus L Δ)).connectedComponentMk x).supp = {x}) ∧
        (Kills (H71 L Δ) x.val ∧ ((sectorSupport (H71 L Δ)).connectedComponentMk x).supp = {x})) ∧
      (Even L → ∀ μ v₀ : ℂ, Nonsingular μ v₀ →
        Kills (staggeredH L μ v₀) x.val ∧
          ((sectorSupport (staggeredH L μ v₀)).connectedComponentMk x).supp = {x}) := by
  refine ⟨(jammed_charge_count hL).1, by simp, ?_⟩
  intro b
  dsimp only
  let x := sectorEmbedding hL b
  have hj : Jammed x.val := (jamEmbedding hL b).property.2
  have hn : ket x.val ≠ 0 := by
    intro h
    have hz := congrFun h x.val
    simpa [ket] using hz
  have hq : NP L *ᵥ ket x.val = (targetCharge L : ℂ) • ket x.val := by
    rw [charge_eigenvalue, x.property]
  refine ⟨hn, hq, ?_, ?_⟩
  · intro Δ
    obtain ⟨hm, hp, h71⟩ := ordinary_kills (by omega) hj Δ
    exact ⟨⟨hm, singleton_of_kills x hm⟩, ⟨hp, singleton_of_kills x hp⟩,
      ⟨h71, singleton_of_kills x h71⟩⟩
  · intro he μ v₀ hd
    have h := staggered_kills (by omega) hj he μ v₀ hd
    exact ⟨h, singleton_of_kills x h⟩

end

end D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves
