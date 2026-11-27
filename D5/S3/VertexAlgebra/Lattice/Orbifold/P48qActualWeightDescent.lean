import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualCurrentGrading
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Descent to an oscillator-ground Cartan weight for an ordinary cubic twisted
module, using the actual current and conformal coefficients. See Bakalov--Kac,
`arXiv:math/0402315v3`, section 4. The argument uses a least energy in the
initial weight coset and the finite dimension of its conformal eigenspace.
-/

set_option autoImplicit false

open scoped VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualWeightDescent

open P48qAllJetWickField (NativeStates)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (Cartan)
open P48qMomentumEnergy (Fixed fixedGram fixedGram_nondegenerate fixedGram_symm)
open P48qNativeCurrentLocality (currentAlong)
open P48qFieldCarrierTransport (InResidueOn TwistedBorcherdsOn)
open NativeStandardThirdLift (standardLift)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (omega)
open LatticeSugawaraConformal (translation)
open HalfFockSpectralFiberSource (actualInverse)

open private currentCoefficient from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport

attribute [local instance] LieRing.ofAssociativeRing

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "L[" Y "]" =>
  HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6)
local notation "h[" Y ", " k ", " u "]" =>
  HVertexOperator.coeff (Y (currentAlong lattice u)) (-k - 3)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A nonzero finite dimensional invariant subspace for a commuting family
contains a joint eigenvector. The proof selects an invariant subspace of
minimum dimension and uses existence of eigenvalues over `ℂ`. -/
private theorem common_eigenvector {ι : Type*} (T : ι → Module.End ℂ W)
    (hcomm : ∀ i j, Commute (T i) (T j)) (E : Submodule ℂ W)
    [FiniteDimensional ℂ E] (hE : E ≠ ⊥)
    (hinv : ∀ i v, v ∈ E → T i v ∈ E) :
    ∃ v ∈ E, v ≠ 0 ∧ ∀ i, ∃ a : ℂ, T i v = a • v := by
  classical
  let P (n : ℕ) := ∃ F : Submodule ℂ W, F ≤ E ∧ F ≠ ⊥ ∧
    (∀ i v, v ∈ F → T i v ∈ F) ∧ Module.finrank ℂ F = n
  have hP : ∃ n, P n := ⟨_, E, le_rfl, hE, hinv, rfl⟩
  obtain ⟨F, hFE, hF, hFinv, hFr⟩ := Nat.find_spec hP
  let : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFE
  let : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr hF
  obtain ⟨v, hvF, hv⟩ := F.ne_bot_iff.mp hF
  refine ⟨v, hFE hvF, hv, fun i => ?_⟩
  let R : Module.End ℂ F := (T i).restrict (hFinv i)
  obtain ⟨a, ha⟩ := R.exists_eigenvalue
  obtain ⟨w, hw⟩ := ha.exists_hasEigenvector
  let G : Submodule ℂ W := F ⊓ (T i).eigenspace a
  have hwG : (w : W) ∈ G := by
    refine ⟨w.property, Module.End.mem_eigenspace_iff.mpr ?_⟩
    exact congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : W) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hG : G ≠ ⊥ := G.ne_bot_iff.mpr ⟨w, hwG, hw0⟩
  have hGinv : ∀ j x, x ∈ G → T j x ∈ G := by
    intro j x hx
    refine ⟨hFinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    have hc := congrArg (fun f : Module.End ℂ W => f x) (hcomm i j).eq
    change T i (T j x) = T j (T i x) at hc
    rw [hc, Module.End.mem_eigenspace_iff.mp hx.2, map_smul]
  have hmin := Nat.find_min' hP (show P (Module.finrank ℂ G) from
    ⟨G, le_trans inf_le_left hFE, hG, hGinv, rfl⟩)
  have hGF : G = F := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hFr]; exact hmin)
  have hvG : v ∈ G := hGF.symm ▸ hvF
  exact ⟨a, Module.End.mem_eigenspace_iff.mp hvG.2⟩

/-- The descent only uses the Ward identity, the commuting fixed-zero modes,
a real lower bound on eigenvalues, and finite dimensional eigenspaces. -/
private theorem descend (L : Module.End ℂ W) (A : ℤ → Cartan → Module.End ℂ W)
    (hgrade : ∀ k u, L * A k u - A k u * L = -((k : ℂ) / 3) • A k u)
    (hcomm : ∀ u v : Fixed, Commute (A 0 u) (A 0 v))
    (b : ℝ) (hlower : ∀ (z : ℂ) (v : W), v ≠ 0 → L v = z • v → b ≤ z.re)
    (hfinite : ∀ z : ℂ, FiniteDimensional ℂ (L.eigenspace z))
    (r : ℂ) (v : W) (hv : v ≠ 0) (hr : L v = r • v) :
    ∃ (n : ℕ) (w : W), w ≠ 0 ∧ L w = (r - (n : ℂ) / 3) • w ∧
      (∀ (k : ℤ) (u : Cartan), 0 < k → A k u w = 0) ∧
      ∀ u : Fixed, ∃ a : ℂ, A 0 u w = a • w := by
  classical
  let P (n : ℕ) := ∃ w : W, w ≠ 0 ∧ L w = (r - (n : ℂ) / 3) • w
  have h0 : P 0 := ⟨v, hv, by simpa using hr⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (r.re - b))
  have hbound (n : ℕ) (hn : P n) : n ≤ N := by
    obtain ⟨w, hw, he⟩ := hn
    have hb := hlower _ _ hw he
    have hreal : (r - (n : ℂ) / 3).re = r.re - (n : ℝ) / 3 := by
      simp [Complex.sub_re]
    rw [hreal] at hb
    exact_mod_cast (show (n : ℝ) ≤ (N : ℝ) by linarith)
  let n := Nat.findGreatest P N
  have hn : P n := Nat.findGreatest_spec (Nat.zero_le N) h0
  let z := r - (n : ℂ) / 3
  let E := L.eigenspace z
  let : FiniteDimensional ℂ E := hfinite z
  obtain ⟨w, hw, he⟩ := hn
  have hE : E ≠ ⊥ := E.ne_bot_iff.mpr ⟨w, Module.End.mem_eigenspace_iff.mpr he, hw⟩
  have hshift (k : ℤ) (u : Cartan) (x : W) (hx : x ∈ E) :
      L (A k u x) = (z - (k : ℂ) / 3) • A k u x := by
    have hg := congrArg (fun f : Module.End ℂ W => f x) (hgrade k u)
    change L (A k u x) - A k u (L x) = (-((k : ℂ) / 3)) • A k u x at hg
    rw [Module.End.mem_eigenspace_iff.mp hx, map_smul] at hg
    calc
      L (A k u x) = (L (A k u x) - z • A k u x) + z • A k u x := by abel
      _ = (-((k : ℂ) / 3)) • A k u x + z • A k u x := by rw [hg]
      _ = (z - (k : ℂ) / 3) • A k u x := by
        rw [← add_smul]
        congr 1
        ring
  have hkill (x : W) (hx : x ∈ E) (k : ℤ) (u : Cartan) (hk : 0 < k) :
      A k u x = 0 := by
    by_contra hne
    have hcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hweight : z - (k : ℂ) / 3 = r - ((n + k.toNat : ℕ) : ℂ) / 3 := by
      have hcast' := congrArg (fun m : ℤ => (m : ℂ)) hcast
      push_cast at hcast' ⊢
      dsimp [z]
      rw [hcast']
      ring
    have hnext : P (n + k.toNat) := ⟨_, hne, (hshift k u x hx).trans (by rw [hweight])⟩
    have hle : n + k.toNat ≤ n := Nat.le_findGreatest (hbound _ hnext) hnext
    omega
  have hinv : ∀ (u : Fixed) (x : W), x ∈ E → A 0 u x ∈ E := by
    intro u x hx
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hshift 0 u x hx
  obtain ⟨x, hxE, hx, hzero⟩ := common_eigenvector (fun u : Fixed => A 0 u) hcomm E hE hinv
  exact ⟨n, x, hx, Module.End.mem_eigenspace_iff.mp hxE, hkill x hxE, hzero⟩

private theorem represent_character (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (w : W) (hw : w ≠ 0)
    (hzero : ∀ u : Fixed, ∃ a : ℂ, h[Y, 0, (u : Cartan)] w = a • w) :
    ∃ x : Fixed, ∀ u : Fixed, h[Y, 0, (u : Cartan)] w = fixedGram u x • w := by
  classical
  choose a ha using hzero
  let T : Fixed →ₗ[ℂ] W := (LinearMap.applyₗ (R := ℂ) w).comp
    ((currentCoefficient Y 0).comp Fixed.subtype)
  have hT (u : Fixed) : T u = a u • w := ha u
  let χ : Module.Dual ℂ Fixed := {
    toFun := a
    map_add' := fun u v => smul_left_injective ℂ hw (by
      change a (u + v) • w = (a u + a v) • w
      rw [← hT, add_smul, ← hT, ← hT, map_add])
    map_smul' := fun c u => smul_left_injective ℂ hw (by
      change a (c • u) • w = (c * a u) • w
      rw [← hT, ← smul_smul, ← hT, map_smul]) }
  let x := (fixedGram.toDual fixedGram_nondegenerate).symm χ
  have hx : fixedGram.toDual fixedGram_nondegenerate x = χ :=
    (fixedGram.toDual fixedGram_nondegenerate).apply_symm_apply χ
  refine ⟨x, fun u => ?_⟩
  have he := DFunLike.congr_fun hx u
  change fixedGram x u = a u at he
  rw [fixedGram_symm.eq u x, he]
  exact ha u

/-- For an actual twisted target satisfying the current and conformal
Borcherds laws and translation, every conformal eigenvector descends in
its one-third coset to a nonzero
oscillator-ground vector with a fixed-Cartan character represented by the
nondegenerate fixed Gram form. -/
theorem actual_weight_descent
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (hresidue : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      InResidueOn s (Y (currentAlong lattice u)))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice (currentAlong lattice u) j (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (homega : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      ∃ N : ℕ,
        (∀ j ≥ (N : ℤ), mu lattice (omega lattice (actualInverse lattice)) j
          (currentAlong lattice u) = 0) ∧
        TwistedBorcherdsOn Y (omega lattice (actualInverse lattice))
          (currentAlong lattice u) 0 s N)
    (htranslate : ∀ (u : Cartan) (j : ℤ),
      HVertexOperator.coeff (Y (translation lattice (currentAlong lattice u))) j =
        (((j + 3 : ℤ) : ℂ) / 3) • HVertexOperator.coeff (Y (currentAlong lattice u)) (j + 3))
    (b : ℝ) (hlower : ∀ (z : ℂ) (v : W), v ≠ 0 → L[Y] v = z • v → b ≤ z.re)
    (hfinite : ∀ z : ℂ, FiniteDimensional ℂ (Module.End.eigenspace L[Y] z))
    (r : ℂ) (v : W) (hv : v ≠ 0) (hr : L[Y] v = r • v) :
    ∃ (n : ℕ) (w : W) (x : Fixed), w ≠ 0 ∧
      L[Y] w = (r - (n : ℂ) / 3) • w ∧
      (∀ (k : ℤ) (u : Cartan), 0 < k → h[Y, k, u] w = 0) ∧
      ∀ u : Fixed, h[Y, 0, (u : Cartan)] w = fixedGram u x • w := by
  have hcomm (u v : Fixed) : Commute h[Y, 0, (u : Cartan)] h[Y, 0, (v : Cartan)] := by
    apply commute_iff_lie_eq.mpr
    rw [P48qActualTwistedHeisenberg.current_commutator Y hVac hresidue hborcherds]
    simp
  have hgrade (k : ℤ) (u : Cartan) :
      L[Y] * h[Y, k, u] - h[Y, k, u] * L[Y] = -((k : ℂ) / 3) • h[Y, k, u] :=
    P48qActualCurrentGrading.actual_current_mode_ward Y hresidue homega htranslate u k
  obtain ⟨n, w, hw, he, hpos, hzero⟩ := descend L[Y] (fun k u => h[Y, k, u])
    hgrade hcomm b hlower hfinite r v hv hr
  obtain ⟨x, hx⟩ := represent_character Y w hw hzero
  exact ⟨n, w, x, hw, he, hpos, hx⟩

run_cmd do
  let axioms ← Lean.collectAxioms ``actual_weight_descent
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for actual_weight_descent: {axioms}"
  Lean.logInfo m!"actual_weight_descent depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualWeightDescent
