/- GID: D5/S3/ArithUnits/BouquetNativeRegionalRank
   generality: G
   mirror-B: D5/B/S3/ArithUnits/BouquetNativeRegionalRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every native four-leg region has rank equal to hit loops plus its padded central rank. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ArithUnits.BouquetNativeRegionalRank

open scoped BigOperators
open Module

variable {k p : ℕ} [Fact p.Prime]

/-- The two central linear forms in each loop. -/
def centralForm (D : Matrix (Fin k) (Fin k × Fin 2) (GaloisField p 2))
    (j : Fin k) (s : Fin 2) : (Fin k → GaloisField p 2) →ₗ[GaloisField p 2] GaloisField p 2 :=
  ∑ i : Fin k, D i (j,s) • LinearMap.proj i

/-- The loops meeting the selected region. -/
def hitLoops (R : Finset (Fin k × Fin 4)) : Finset (Fin k) :=
  R.image Prod.fst

/-- Restriction of the actual four-leg map to the selected rows. -/
def actualMap (D : Matrix (Fin k) (Fin k × Fin 2) (GaloisField p 2))
    (R : Finset (Fin k × Fin 4)) :
    ((Fin k → GaloisField p 2) × (Fin k → GaloisField p 2)) →ₗ[GaloisField p 2]
      (R → GaloisField p 2) :=
  LinearMap.pi fun r =>
    (centralForm D r.1.1 (if r.1.2 < 2 then 0 else 1)).comp (LinearMap.fst _ _ _) +
    (if r.1.2 = 0 ∨ r.1.2 = 2 then (1 : GaloisField p 2) else -1) •
      (LinearMap.proj r.1.1).comp (LinearMap.snd _ _ _)

/-- Two central slots per loop, with the mask-specific constraints and zero padding. -/
def virtualMap (D : Matrix (Fin k) (Fin k × Fin 2) (GaloisField p 2))
    (R : Finset (Fin k × Fin 4)) :
    (Fin k → GaloisField p 2) →ₗ[GaloisField p 2] ((Fin k × Fin 2) → GaloisField p 2) :=
  LinearMap.pi fun t =>
    let j := t.1
    let a := centralForm D j 0
    let b := centralForm D j 1
    if (j,0) ∈ R ∧ (j,1) ∈ R then
      if (j,2) ∈ R ∨ (j,3) ∈ R then (if t.2 = 0 then a else b)
      else (if t.2 = 0 then a else 0)
    else if (j,2) ∈ R ∧ (j,3) ∈ R then
      if (j,0) ∈ R ∨ (j,1) ∈ R then (if t.2 = 0 then a else b)
      else (if t.2 = 0 then b else 0)
    else if ((j,0) ∈ R ∧ (j,2) ∈ R) ∨ ((j,1) ∈ R ∧ (j,3) ∈ R) then
      (if t.2 = 0 then a - b else 0)
    else if ((j,0) ∈ R ∧ (j,3) ∈ R) ∨ ((j,1) ∈ R ∧ (j,2) ∈ R) then
      (if t.2 = 0 then a + b else 0)
    else 0

/-- The native regional rank splits into one loop dimension per hit and the central rank. -/
theorem native_regional_rank (hk : 2 ≤ k) (hkp : k < p)
    (D : Matrix (Fin k) (Fin k × Fin 2) (GaloisField p 2))
    (R : Finset (Fin k × Fin 4)) :
    finrank (GaloisField p 2) (LinearMap.range (actualMap D R)) =
      (hitLoops R).card + finrank (GaloisField p 2) (LinearMap.range (virtualMap D R)) := by
  classical
  let K := GaloisField p 2
  let J := hitLoops R
  have htwo : (2 : K) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff K p 2).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) hd
  let signed (j : Fin k) (l : Fin 4) : (Fin k → K) →ₗ[K] K :=
    (if l = 0 ∨ l = 2 then (1 : K) else -1) •
      centralForm D j (if l < 2 then 0 else 1)
  have hrow (x : (Fin k → K) × (Fin k → K)) (j : Fin k) (l : Fin 4)
      (hr : (j,l) ∈ R) :
      actualMap D R x ⟨(j,l),hr⟩ = 0 ↔ x.2 j = -signed j l x.1 := by
    fin_cases l <;> simp [actualMap, signed]
    all_goals constructor <;> intro h <;> first | linear_combination h | linear_combination -h
  have hlocal (j : Fin k) (lam : Fin k → K) :
      (∀ l m : Fin 4, (j,l) ∈ R → (j,m) ∈ R → signed j l lam = signed j m lam) ↔
      (∀ t : Fin 2, virtualMap D R lam (j,t) = 0) := by
    by_cases h0 : (j,0) ∈ R <;> by_cases h1 : (j,1) ∈ R <;>
      by_cases h2 : (j,2) ∈ R <;> by_cases h3 : (j,3) ∈ R
    · constructor
      · intro h
        have e01 := h 0 1 h0 h1
        simp [signed] at e01
        have e02 := h 0 2 h0 h2
        simp [signed] at e02
        have ha : centralForm D j 0 lam = 0 := by
          have hh : (2 : K) * centralForm D j 0 lam = 0 := by linear_combination e01
          exact (mul_eq_zero.mp hh).resolve_left htwo
        have hb : centralForm D j 1 lam = 0 := by linear_combination ha - e02
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,hs1,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e01 := h 0 1 h0 h1
        simp [signed] at e01
        have e02 := h 0 2 h0 h2
        simp [signed] at e02
        have ha : centralForm D j 0 lam = 0 := by
          have hh : (2 : K) * centralForm D j 0 lam = 0 := by linear_combination e01
          exact (mul_eq_zero.mp hh).resolve_left htwo
        have hb : centralForm D j 1 lam = 0 := by linear_combination ha - e02
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,hs1,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e01 := h 0 1 h0 h1
        simp [signed] at e01
        have e03 := h 0 3 h0 h3
        simp [signed] at e03
        have ha : centralForm D j 0 lam = 0 := by
          have hh : (2 : K) * centralForm D j 0 lam = 0 := by linear_combination e01
          exact (mul_eq_zero.mp hh).resolve_left htwo
        have hb : centralForm D j 1 lam = 0 := by linear_combination e03 - ha
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,hs1,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e01 := h 0 1 h0 h1
        simp [signed] at e01
        have ha : centralForm D j 0 lam = 0 := by
          have hh : (2 : K) * centralForm D j 0 lam = 0 := by linear_combination e01
          exact (mul_eq_zero.mp hh).resolve_left htwo
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e23 := h 2 3 h2 h3
        simp [signed] at e23
        have e02 := h 0 2 h0 h2
        simp [signed] at e02
        have hb : centralForm D j 1 lam = 0 := by
          have hh : (2 : K) * centralForm D j 1 lam = 0 := by linear_combination e23
          exact (mul_eq_zero.mp hh).resolve_left htwo
        have ha : centralForm D j 0 lam = 0 := by linear_combination e02 + hb
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,hs1,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e02 := h 0 2 h0 h2
        simp [signed] at e02
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
        linear_combination e02
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals first | linear_combination hs0 | linear_combination -hs0
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e03 := h 0 3 h0 h3
        simp [signed] at e03
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
        linear_combination e03
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals first | linear_combination hs0 | linear_combination -hs0
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 0 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e23 := h 2 3 h2 h3
        simp [signed] at e23
        have e12 := h 1 2 h1 h2
        simp [signed] at e12
        have hb : centralForm D j 1 lam = 0 := by
          have hh : (2 : K) * centralForm D j 1 lam = 0 := by linear_combination e23
          exact (mul_eq_zero.mp hh).resolve_left htwo
        have ha : centralForm D j 0 lam = 0 := by linear_combination -e12 - hb
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, ha, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 1 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,hs1,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e12 := h 1 2 h1 h2
        simp [signed] at e12
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
        linear_combination -e12
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 1 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals first | linear_combination hs0 | linear_combination -hs0
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e13 := h 1 3 h1 h3
        simp [signed] at e13
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
        linear_combination -e13
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 1 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals first | linear_combination hs0 | linear_combination -hs0
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 1 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        have e23 := h 2 3 h2 h3
        simp [signed] at e23
        have hb : centralForm D j 1 lam = 0 := by
          have hh : (2 : K) * centralForm D j 1 lam = 0 := by linear_combination e23
          exact (mul_eq_zero.mp hh).resolve_left htwo
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3, hb]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 2 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
          all_goals simp only [hs0,neg_zero]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 2 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        have hv (l : Fin 4) (hl : (j,l) ∈ R) : signed j l lam = signed j 3 lam := by
          fin_cases l <;> try contradiction
          all_goals simp [signed]
        intro l m hl hm
        exact (hv l hl).trans (hv m hm).symm
    · constructor
      · intro h
        intro t
        fin_cases t <;> simp [virtualMap, h0, h1, h2, h3]
      · intro h
        have hs0 := h 0
        have hs1 := h 1
        simp [virtualMap, h0, h1, h2, h3] at hs0 hs1
        intro l m hl hm
        fin_cases l <;> contradiction
  have hhit (j : Fin k) : j ∈ J ↔ ∃ l : Fin 4, (j,l) ∈ R := by
    simp only [J, hitLoops, Finset.mem_image]
    constructor
    · rintro ⟨⟨i,l⟩,hr,hi⟩
      change i = j at hi
      subst i
      exact ⟨l,hr⟩
    · rintro ⟨l,hr⟩
      exact ⟨(j,l),hr,rfl⟩
  let anchor (j : Fin k) (h : j ∈ J) : Fin 4 := Classical.choose ((hhit j).mp h)
  have hanchor (j : Fin k) (h : j ∈ J) : (j,anchor j h) ∈ R :=
    Classical.choose_spec ((hhit j).mp h)
  let T : (Fin k → K) →ₗ[K] (Fin k → K) :=
    LinearMap.pi fun j => if h : j ∈ J then signed j (anchor j h) else 0
  let W : (Fin k → K) →ₗ[K] (R → K) :=
    LinearMap.pi fun r => signed r.1.1 r.1.2 - (LinearMap.proj r.1.1).comp T
  have hW (lam : Fin k → K) : lam ∈ LinearMap.ker W ↔
      ∀ j : Fin k, ∀ l m : Fin 4, (j,l) ∈ R → (j,m) ∈ R →
        signed j l lam = signed j m lam := by
    simp only [LinearMap.mem_ker]
    constructor
    · intro h j l m hl hm
      have h1 := congrFun h ⟨(j,l),hl⟩
      have h2 := congrFun h ⟨(j,m),hm⟩
      simp only [W, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Pi.zero_apply] at h1 h2
      linear_combination h1 - h2
    · intro h
      ext r
      have hj : r.1.1 ∈ J := (hhit _).mpr ⟨r.1.2,r.2⟩
      have hh := h r.1.1 r.1.2 (anchor _ hj) r.2 (hanchor _ hj)
      simpa [W, T, hj, sub_eq_zero] using hh
  have hker : LinearMap.ker W = LinearMap.ker (virtualMap D R) := by
    ext lam
    rw [hW, LinearMap.mem_ker]
    constructor
    · intro h
      ext t
      exact (hlocal t.1 lam).mp (h t.1) t.2
    · intro h j
      apply (hlocal j lam).mpr
      intro t
      exact congrFun h (j,t)
  have hz (x : LinearMap.ker (actualMap D R)) (j : Fin k) (hj : j ∈ J) :
      x.1.2 j = -T x.1.1 j := by
    have hh := congrFun (LinearMap.mem_ker.mp x.2) ⟨(j,anchor j hj),hanchor j hj⟩
    simpa [T, hj] using (hrow x.1 j (anchor j hj) (hanchor j hj)).mp hh
  have hforward (x : LinearMap.ker (actualMap D R)) : x.1.1 ∈ LinearMap.ker W := by
    rw [hW]
    intro j l m hl hm
    have h1 := (hrow x.1 j l hl).mp
      (congrFun (LinearMap.mem_ker.mp x.2) ⟨(j,l),hl⟩)
    have h2 := (hrow x.1 j m hm).mp
      (congrFun (LinearMap.mem_ker.mp x.2) ⟨(j,m),hm⟩)
    linear_combination h1 - h2
  let forward : LinearMap.ker (actualMap D R) →ₗ[K]
      (LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) :=
    { toFun := fun x => (⟨x.1.1,hforward x⟩,fun j => x.1.2 j.1)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let restore (x : LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) :
      (Fin k → K) × (Fin k → K) :=
    (x.1.1,fun j => if h : j ∈ J then -T x.1.1 j else x.2 ⟨j,h⟩)
  have hrestore (x : LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) :
      restore x ∈ LinearMap.ker (actualMap D R) := by
    apply LinearMap.mem_ker.mpr
    ext r
    have hj : r.1.1 ∈ J := (hhit _).mpr ⟨r.1.2,r.2⟩
    apply (hrow (restore x) r.1.1 r.1.2 r.2).mpr
    have hh := congrFun (LinearMap.mem_ker.mp x.1.2) r
    simp only [W, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero] at hh
    simp [restore, hj, hh]
  let inverse : (LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) →ₗ[K]
      LinearMap.ker (actualMap D R) :=
    { toFun := fun x => ⟨restore x,hrestore x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · funext j
          by_cases hj : j ∈ J <;> simp [restore,hj]
          exact add_comm _ _
      map_smul' := by
        intro c x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · funext j
          by_cases hj : j ∈ J <;> simp [restore,hj]
          exact (mul_neg c _).symm }
  have hleft (x : LinearMap.ker (actualMap D R)) : inverse (forward x) = x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j ∈ J
      · simpa [inverse,forward,restore,hj] using (hz x j hj).symm
      · simp [inverse,forward,restore,hj]
  have hright (x : LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) :
      forward (inverse x) = x := by
    apply Prod.ext
    · rfl
    · funext j
      simp [forward,inverse,restore,j.2]
  let equivalence : LinearMap.ker (actualMap D R) ≃ₗ[K]
      (LinearMap.ker W × ({j : Fin k // j ∉ J} → K)) :=
    { forward with invFun := inverse, left_inv := hleft, right_inv := hright }
  have hdim := equivalence.finrank_eq
  rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_subtype_compl,
    Fintype.card_fin, show Fintype.card {j : Fin k // j ∈ J} = J.card from Fintype.card_coe J,
    hker] at hdim
  have hF := (actualMap D R).finrank_range_add_finrank_ker
  have hV := (virtualMap D R).finrank_range_add_finrank_ker
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hF hV
  have hcard : J.card ≤ k := (Finset.card_le_card (Finset.subset_univ J)).trans_eq (Finset.card_fin k)
  dsimp only [K] at hdim
  change _ = J.card + _
  omega

#print axioms native_regional_rank

end D5.S3.ArithUnits.BouquetNativeRegionalRank
