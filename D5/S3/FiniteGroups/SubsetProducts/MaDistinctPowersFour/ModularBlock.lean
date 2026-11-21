/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/ModularBlock
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/ModularBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consecutive exponents for four generators over a composite modulus. -/

/- Escape audit unfinished for 2 supporting theorems. See https://github.com/the-omega-institute/trureturing/issues/32494. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.LatinCore
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace MaLatin

theorem productLatin {M : Type*} [Group M] {k : ℕ} (b u : Fin k → M)
    (hb : Function.Injective b) (hu : Function.Injective u) :
    Latin (fun i j => b i * u j) :=
  ⟨fun _ _ _ h => hu (mul_left_cancel h), fun _ _ _ h => hb (mul_right_cancel h)⟩

private theorem productNoMotif {M : Type*} [CommGroup M] (x y : Fin 4 → M) :
    ¬ Motif (fun r c => x r * y c) := by
  rintro ⟨r₀,r₁,r₂,c₀,c₁,c₂,_,_,_,_,_,_,h₁,h₂,h₃,h₄,hn⟩
  let a := x r₀ * y c₀
  let b := x r₀ * y c₁
  let c := x r₀ * y c₂
  let t := x r₁ / x r₀
  let s := x r₂ / x r₀
  have ratio (r j : Fin 4) : (x r / x r₀) * (x r₀ * y j) = x r * y j := by
    rw [← mul_assoc, div_mul_cancel]
  have hab : t * a = b := (ratio r₁ c₀).trans h₁
  have hbc : t * b = c := (ratio r₁ c₁).trans h₂
  have hca : t * c = a := (ratio r₁ c₂).trans h₃
  have hsc : s * a = c := (ratio r₂ c₀).trans h₄
  have hs : s = t * t := by
    apply mul_right_cancel (b := a)
    rw [hsc, mul_assoc, hab, hbc]
  apply hn
  calc
    x r₂ * y c₂ = s * c := (ratio r₂ c₂).symm
    _ = b := by rw [hs, mul_assoc, hca, hab]

private theorem noEqualColumns_of_four_consecutive {M F : Type*} [CommGroup M] [Field F]
    (f : M →* F) (b u : Fin 4 → M) (r : F)
    (hb : Function.Injective (f ∘ b)) (hu : Function.Injective u)
    (hblock : ∀ i, f (b i) = r + (i.val : F)) (h20 : (20 : F) ≠ 0) :
    ¬ EqualColumns (fun i j => b i * u j) := by
  classical
  intro h
  choose next hn using fun (j i : Fin 4) => h j 0 i
  have next_inj (j : Fin 4) : Function.Injective (next j) := by
    intro i k e
    apply hb
    exact congrArg f (mul_right_cancel (b := u j) <|
      (hn j i).trans ((congrArg (fun v => b v * u 0) e).trans (hn j k).symm))
  let p (j : Fin 4) := Equiv.ofBijective (next j)
    (Finite.injective_iff_bijective.mp (next_inj j))
  let q (j : Fin 4) := f (u j / u 0)
  have hmul (j i : Fin 4) : b i * (u j / u 0) = b (p j i) := by
    apply mul_right_cancel (b := u 0)
    rw [mul_assoc, div_mul_cancel]
    exact hn j i
  have hq (j i : Fin 4) : q j * f (b i) = f (b (p j i)) := by
    rw [mul_comm, ← map_mul]
    exact congrArg f (hmul j i)
  have hqinj : Function.Injective q := by
    intro j k he
    have he' : p j 0 = p k 0 :=
      hb ((hq j 0).symm.trans ((congrArg (· * f (b 0)) he).trans (hq k 0)))
    apply hu
    apply mul_left_cancel (a := b 0)
    change next j 0 = next k 0 at he'
    exact (hn j 0).trans ((congrArg (fun v => b v * u 0) he').trans (hn k 0).symm)
  let s₁ : F := ∑ i : Fin 4, f (b i)
  let s₂ : F := ∑ i : Fin 4, (f (b i)) ^ 2
  have h₁ (j : Fin 4) : q j * s₁ = s₁ := by
    unfold s₁
    rw [Finset.mul_sum]
    simp only [hq]
    exact Equiv.sum_comp (p j) (fun i => f (b i))
  have h₂ (j : Fin 4) : q j ^ 2 * s₂ = s₂ := by
    unfold s₂
    rw [Finset.mul_sum]
    simp only [← mul_pow, hq]
    exact Equiv.sum_comp (p j) (fun i => (f (b i)) ^ 2)
  have invariant : 4 * s₂ - s₁ ^ 2 = 20 := by
    simp only [s₁, s₂, hblock, Fin.sum_univ_four]
    norm_num
    <;> ring
  have sq (j : Fin 4) : q j ^ 2 = 1 := by
    apply mul_right_cancel₀ h20
    rw [one_mul, ← invariant]
    calc
      q j ^ 2 * (4 * s₂ - s₁ ^ 2) =
          4 * (q j ^ 2 * s₂) - (q j * s₁) ^ 2 := by ring
      _ = 4 * s₂ - s₁ ^ 2 := by rw [h₁, h₂]
  have roots (j : Fin 4) := sq_eq_one_iff.mp (sq j)
  rcases roots 0 with h0 | h0 <;> rcases roots 1 with h1 | h1 <;>
    rcases roots 2 with h2 | h2
  all_goals first
    | exact (by decide : (0 : Fin 4) ≠ 1) (hqinj (h0.trans h1.symm))
    | exact (by decide : (0 : Fin 4) ≠ 2) (hqinj (h0.trans h2.symm))
    | exact (by decide : (1 : Fin 4) ≠ 2) (hqinj (h1.trans h2.symm))


/-- Four consecutive exponents admit distinct products with four arbitrary distinct generators. -/
theorem fourBlock_of_orderFour
    (m : ℕ) (classify : ∀ A : Fin 4 → Fin 4 → (ZMod m)ˣ,
      Latin A → Rainbow A ∨ EqualColumns A ∨ Motif A)
    (n r : ℕ) (hm : 1 < m)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ m → n + 1 < p)
    (hr : 1 ≤ r) (hrn : r + 3 ≤ n)
    (u : Fin 4 → (ZMod m)ˣ) (hu : Function.Injective u) :
    ∃ π : Equiv.Perm (Fin 4),
      Function.Injective fun i : Fin 4 => ((r + i.val : ℕ) : ZMod m) * (u (π i) : ZMod m) := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hpn := hprime p hp hpm
  have hcop (i : Fin 4) : Nat.Coprime (r + i.val) m := by
    by_contra h
    obtain ⟨q, hq, hqi, hqm⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hqn := hprime q hq hqm
    have hi := i.isLt
    have hle := Nat.le_of_dvd (by omega : 0 < r + i.val) hqi
    omega
  let b (i : Fin 4) : (ZMod m)ˣ := ZMod.unitOfCoprime (r + i.val) (hcop i)
  let f : (ZMod m)ˣ →* ZMod p :=
    (ZMod.castHom hpm (ZMod p)).toMonoidHom.comp (Units.coeHom (ZMod m))
  have hb' (i : Fin 4) : f (b i) = ((r + i.val : ℕ) : ZMod p) := by
    change ZMod.castHom hpm (ZMod p) (b i : ZMod m) = _
    rw [ZMod.coe_unitOfCoprime, map_natCast]
  have hb : Function.Injective (f ∘ b) := by
    intro i j hij
    change f (b i) = f (b j) at hij
    rw [hb', hb', ZMod.natCast_eq_natCast_iff'] at hij
    have hi := i.isLt
    have hj := j.isLt
    rw [Nat.mod_eq_of_lt (by omega : r + i.val < p),
        Nat.mod_eq_of_lt (by omega : r + j.val < p)] at hij
    apply Fin.ext
    omega
  have h20 : (20 : ZMod p) ≠ 0 := by
    change ((20 : ℕ) : ZMod p) ≠ 0
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 20 p).mp hz
    have hp5 : 5 < p := by omega
    have hh : p ∣ 4 * 5 := h
    rcases hp.dvd_mul.mp hh with h4 | h5
    · have := Nat.le_of_dvd (by decide : 0 < 4) h4
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 5) h5
      omega
  have hbRing (i : Fin 4) : f (b i) = (r : ZMod p) + (i.val : ZMod p) := by
    rw [hb', Nat.cast_add]
  rcases classify (fun i j => b i * u j)
      (productLatin b u (fun _ _ h => hb (congrArg f h)) hu) with hrain | heq | hmot
  · obtain ⟨π, hπ⟩ := hrain
    refine ⟨π, fun i j h => hπ (Units.val_injective ?_)⟩
    simpa only [Units.val_mul, b, ZMod.coe_unitOfCoprime] using h
  · exact (noEqualColumns_of_four_consecutive f b u (r : ZMod p) hb hu hbRing h20 heq).elim
  · exact (productNoMotif b u hmot).elim

end MaLatin
