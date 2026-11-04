/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/ContinuousCover
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/ContinuousCover
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: ContinuousCover and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative
open private basic_positive from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Algebra

structure CoverRow where
  j : ℕ
  second : Bool
  shift : ℤ
  deriving DecidableEq

def epsLo (z : ℚ) : ℚ := (25-16*(z+1)+80*(64*z))/(8*(5+16*(64*z)*(z+1)))
def epsHi (z : ℚ) : ℚ := 5/(8*(z+1))
def etaMax (z : ℚ) : ℚ := (1+124*(z+1))/(8*(5+8*(64*z)*(z+1)))
def nominal (r : CoverRow) : ℚ := -(5:ℚ)*r.j/8+(if r.second then 3/8 else 0)+r.shift
def lower (z : ℚ) (r : CoverRow) : ℚ := nominal r+r.j*epsHi z+etaMax z
def upper (z : ℚ) (r : CoverRow) : ℚ := nominal r+r.j*epsLo z+1/8-etaMax z

private def Chain {α : Type*} (lo hi : α→ℚ) (a b : ℚ) : List α→Prop
  | [] => b<a
  | r::rs => lo r≤a ∧ a≤hi r ∧ Chain lo hi (hi r) b rs

private theorem chain_hit {α : Type*} (lo hi : α→ℚ) (rs : List α) (a b x : ℚ)
    (hc : Chain lo hi a b rs) (ha : a≤x) (hb : x≤b) :
    ∃ r∈rs, lo r≤x ∧ x≤hi r := by
  induction rs generalizing a with
  | nil => simp only [Chain] at hc; linarith
  | cons r rs ih =>
    rcases hc with ⟨hl,hu,hrest⟩
    by_cases hx : x≤hi r
    · exact ⟨r,by simp,by linarith,hx⟩
    · obtain ⟨s,hs,hsl,hsu⟩ := ih (hi r) hrest (by linarith)
      exact ⟨s,by simp [hs],hsl,hsu⟩

def chain8 : List CoverRow := [
  ⟨8,true,4⟩,
  ⟨6,true,3⟩,
  ⟨4,true,2⟩,
  ⟨2,true,1⟩,
  ⟨0,true,0⟩,
  ⟨7,true,4⟩,
  ⟨5,true,3⟩,
  ⟨3,true,2⟩,
  ⟨1,true,1⟩,
  ⟨8,true,5⟩]

private theorem chain8_certificate : Chain (lower 8) (upper 8) 0 1 chain8 := by
  norm_num [chain8,Chain,lower,upper,nominal,epsLo,epsHi,etaMax]

private theorem chain8_indices : ∀ r∈chain8, r.j≤31 := by
  simp only [chain8,List.mem_cons,List.mem_nil_iff,or_false]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

def chain16 : List CoverRow := [
  ⟨16,true,9⟩,
  ⟨9,true,5⟩,
  ⟨2,true,1⟩,
  ⟨12,true,7⟩,
  ⟨5,true,3⟩,
  ⟨15,true,9⟩,
  ⟨8,true,5⟩,
  ⟨1,true,1⟩,
  ⟨11,true,7⟩]

private theorem chain16_certificate : Chain (lower 16) (upper 16) 0 1 chain16 := by
  norm_num [chain16,Chain,lower,upper,nominal,epsLo,epsHi,etaMax]

private theorem chain16_indices : ∀ r∈chain16, r.j≤31 := by
  simp only [chain16,List.mem_cons,List.mem_nil_iff,or_false]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

def chain32 : List CoverRow := [
  ⟨5,false,3⟩,
  ⟨18,false,11⟩,
  ⟨31,false,19⟩,
  ⟨11,false,7⟩,
  ⟨24,false,15⟩,
  ⟨4,false,3⟩,
  ⟨17,false,11⟩,
  ⟨30,false,19⟩,
  ⟨10,false,7⟩]

private theorem chain32_certificate : Chain (lower 32) (upper 32) 0 1 chain32 := by
  norm_num [chain32,Chain,lower,upper,nominal,epsLo,epsHi,etaMax]

private theorem chain32_indices : ∀ r∈chain32, r.j≤31 := by
  simp only [chain32,List.mem_cons,List.mem_nil_iff,or_false]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

/-- Every actual epsilon and eta in the certified continuous ranges is covered. -/
theorem continuous_cover (z eps eta x : ℚ) (hz : z=8 ∨ z=16 ∨ z=32)
    (heL : epsLo z≤eps) (heU : eps≤epsHi z) (heta : eta≤etaMax z)
    (hx : 0≤x) (hx' : x≤1) :
    ∃ j : ℕ, ∃ second : Bool, ∃ s : ℤ, j≤31 ∧
      (if second then 3/8+eta else eta) ≤ x+j*(5/8-eps)-s ∧
      x+j*(5/8-eps)-s ≤ (if second then 1/2-eta else 1/8-eta) := by
  have extract (rs : List CoverRow)
      (hc : Chain (lower z) (upper z) 0 1 rs)
      (hj : ∀ r∈rs, r.j≤31) :
      ∃ j : ℕ, ∃ second : Bool, ∃ s : ℤ, j≤31 ∧
        (if second then 3/8+eta else eta) ≤ x+j*(5/8-eps)-s ∧
        x+j*(5/8-eps)-s ≤ (if second then 1/2-eta else 1/8-eta) := by
    obtain ⟨r,hr,hl,hu⟩ := chain_hit (lower z) (upper z) rs 0 1 x hc hx hx'
    have hnon : (0:ℚ)≤r.j := by positivity
    have hl' := mul_le_mul_of_nonneg_left heU hnon
    have hu' := mul_le_mul_of_nonneg_left heL hnon
    refine ⟨r.j,r.second,r.shift,hj r hr,?_,?_⟩
    all_goals dsimp [lower,upper,nominal] at hl hu
    all_goals cases hs : r.second <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true] at * <;> nlinarith
  rcases hz with rfl|rfl|rfl
  · exact extract chain8 chain8_certificate chain8_indices
  · exact extract chain16 chain16_certificate chain16_indices
  · exact extract chain32 chain32_certificate chain32_indices

/-- The three exact rational certificates apply for all p>=64 and both h. -/
theorem continuous_parameter_bounds (p q h : ℤ) (hp : 64≤p)
    (hq : q=2 ∨ q=4 ∨ q=8) (hh : h=1 ∨ h=2) :
    epsLo (4*q) ≤ (D p q h:ℚ)/(8*(A p q h:ℚ)) ∧
    (D p q h:ℚ)/(8*(A p q h:ℚ)) ≤ epsHi (4*q) ∧
    ((1+124*h*Q q:ℤ):ℚ)/(8*(A p q h:ℚ)) ≤ etaMax (4*q) := by
  have hpp : (64:ℚ)≤p := by exact_mod_cast hp
  have hq2 : 2≤q := by omega
  have hh1 : 1≤h := by omega
  have hAi : 0<A p q h := (basic_positive p q h (by omega) hq2 hh1).1
  have hden : (0:ℚ)<8*(A p q h:ℚ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hAi)
  rcases hq with rfl|rfl|rfl <;> rcases hh with rfl|rfl
  all_goals refine ⟨(le_div_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_,(div_le_iff₀ hden).2 ?_⟩
  all_goals norm_num [epsLo,epsHi,etaMax,D,A,L,Q,SecondPeakHighD.A,
    SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals push_cast
  all_goals nlinarith

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
