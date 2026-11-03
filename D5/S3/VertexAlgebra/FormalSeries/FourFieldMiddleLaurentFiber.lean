/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldMiddleLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite seven-index fibers for the middle four-field inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedLaurentFiber

/-! All bounds follow from the four signed numerator coordinates. The fiber
is finite for every signed target, without a finite-numerator hypothesis. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.FourFieldMiddleLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open ThreeFieldBalancedLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
abbrev OuterIndex := ℕ × (ℕ × (ℕ × ℕ))
abbrev MiddleIndex := BalancedIndex × OuterIndex

def middleInput (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) (i : MiddleIndex) : Exponent 4 :=
  ![e 0+a 0+3*k+i.2.1+i.2.2.1+i.2.2.2.1+i.2.2.2.2,
    e 1+k-i.1.1-i.1.2.2-i.2.1,
    e 2+a 1+a 2+2*k+i.1.1+i.1.2.1+i.1.2.2-i.2.2.1-i.2.2.2.1,
    e 3+a 3-i.1.2.1-i.2.2.2.2]

def outerWeight (k : ℕ) (i : OuterIndex) : ℂ :=
  (-1 : ℂ)^(i.1+i.2.1+i.2.2.1+i.2.2.2) *
    integerBinomial (-(k : ℤ)) (i.1+i.2.1) * ((i.1+i.2.1).choose i.1 : ℂ) *
    integerBinomial (-(k : ℤ)) i.2.2.1 * integerBinomial (-(k : ℤ)) i.2.2.2

def middleWeight (k : ℕ) (a : Fin 4 → ℕ) (i : MiddleIndex) : ℂ :=
  balancedWeight k (fun c => a c.succ) i.1 * outerWeight k i.2

def MiddleAdmissible (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) (i : MiddleIndex) : Prop :=
  ∀ c,0≤middleInput k a e i c

private theorem input_total (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) (i : MiddleIndex) :
    middleInput k a e i 0+middleInput k a e i 1+
      middleInput k a e i 2+middleInput k a e i 3 =
        e 0+e 1+e 2+e 3+a 0+a 1+a 2+a 3+6*k := by
  simp only [middleInput,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  omega

/-- Each candidate bound is forced by genuine numerator nonnegativity. -/
theorem middle_bounds (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) (i : MiddleIndex)
    (h : MiddleAdmissible k a e i) :
    (i.1.1 : ℤ)+i.1.2.2+i.2.1≤e 1+k ∧
    (i.1.2.1 : ℤ)+i.2.2.2.2≤e 3+a 3 ∧
    (i.2.2.1 : ℤ)+i.2.2.2.1≤e 2+a 1+a 2+2*k+i.1.1+i.1.2.1+i.1.2.2 ∧
    0≤e 1+k ∧ 0≤e 3+a 3 ∧
    0≤e 1+e 3+k+a 3 ∧
    0≤e 1+e 3+e 2+a 1+a 2+a 3+3*k ∧
    0≤e 0+e 1+e 2+e 3+a 0+a 1+a 2+a 3+6*k := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [middleInput,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2 h3
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
  rw [← input_total k a e i]
  exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3

/-- The seven independent natural indices have finite, signed-derived bounds. -/
def middleFiber (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) : Finset MiddleIndex := by
  classical
  let B := (e 1+k).toNat
  let Y := (e 3+a 3).toNat
  let Z := (e 2+a 1+a 2+2*k+2*B+Y).toNat
  exact (((Finset.range (B+1)).product
    ((Finset.range (Y+1)).product (Finset.range (B+1)))).product
      ((Finset.range (B+1)).product ((Finset.range (Z+1)).product
        ((Finset.range (Z+1)).product (Finset.range (Y+1)))))).filter
          (MiddleAdmissible k a e)

theorem mem_middleFiber_iff (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) (i : MiddleIndex) :
    i∈middleFiber k a e ↔ MiddleAdmissible k a e i := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hb,hy,hz,hB,hY,_,_,_⟩ := middle_bounds k a e i h
    have B : ((e 1+k).toNat : ℤ)=e 1+k := Int.toNat_of_nonneg hB
    have Y : ((e 3+a 3).toNat : ℤ)=e 3+a 3 := Int.toNat_of_nonneg hY
    have Z := Int.self_le_toNat (e 2+a 1+a 2+2*k+2*(e 1+k).toNat+(e 3+a 3).toNat)
    simp only [middleFiber,Finset.mem_filter,Finset.product_eq_sprod,
      Finset.mem_product,Finset.mem_range]
    exact ⟨⟨⟨by omega,by omega,by omega⟩,by omega,by omega,by omega,by omega⟩,h⟩

def middleCoefficient {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) : R :=
  ∑ i∈middleFiber k a e,middleWeight k a i • signedExtend P (middleInput k a e i)
end
end D5.S3.VertexAlgebra.FourFieldMiddleLaurentFiber
