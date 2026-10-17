import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.BranchStorage
import Reg.Support.FibonacciQuadratic
import Mathlib.Tactic.IntervalCases

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Reg.Support.FibonacciQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Reg.Support.FibonacciBranchStorageWitness
noncomputable section
universe u

def returns (i : Bool) : Return :=
  if i then ⟨1,4,by decide,by decide⟩ else ⟨11,1,by decide,by decide⟩
def high (i : Bool) := returnWord .high (returns i)
def low (i : Bool) := returnWord .low (returns i)
def colors (i : Bool) := returnColors (returns i)
theorem colors_false : colors false = ([2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2] : List Color) := by decide
theorem colors_true : colors true = ([2,1,0,2,1,0,2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2,2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2,2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2,2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2] : List Color) := by decide
def P := stem .high
def Q := stem .low
def h := colorsD ++ colorsE
def loU : ℝ := eval ((65170004374593217984374873/910763447271179530132922476 : ℚ), (101145664164737438744945839/227690861817794882533230619 : ℚ))
def hiU : ℝ := eval ((65181285317365973229747975/910763447271179530132922476 : ℚ), (101147407166245223571436315/227690861817794882533230619 : ℚ))
def loV : ℝ := eval ((-92469680710161158787739997/910763447271179530132922476 : ℚ), (153577986650352595668986515/455381723635589765066461238 : ℚ))
def hiV : ℝ := eval ((-92453676957411832320966579/910763447271179530132922476 : ℚ), (153582932081944167558760233/455381723635589765066461238 : ℚ))
def budget : ℝ := eval ((-3372570706008700249138214203/4553817236355897650664612380 : ℚ), (2869187707423306017104095319/2276908618177948825332306190 : ℚ))
theorem precise_t : (6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266338622235369317931800607667263544333/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < t ∧ t < 6180339887498948482045868343656381177203091798057628621354486227052604628189024497072072041893911374847540880753868917521266338622235369317931800607667263544334/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  rcases tail_arithmetic with ⟨ht,hp,_,_,_,_⟩
  constructor <;> nlinarith

 theorem budget_bounds : 0 < budget ∧ budget < lam := by
  rcases precise_t with ⟨hlo,hhi⟩
  norm_num [budget,eval,lam,T2]
  constructor <;> linarith

 theorem legal : LegalWord .G0 .G1 P ∧ LegalWord .G0 .G1 Q ∧
    (∀ i, LegalWord .G1 .G1 (high i)) ∧ (∀ i, LegalWord .G1 .G1 (low i)) := by
  refine ⟨by rfl,by rfl,?_,?_⟩
  all_goals intro i; cases i <;> rfl

 theorem lengths : P.length = h.length ∧ Q.length = h.length ∧
    (∀ i, (high i).length = 86) ∧ (∀ i, (low i).length = 86) ∧
    (∀ i, (colors i).length = 86) := by decide

 theorem distinct : high false ≠ high true ∧ low false ≠ low true := by decide
 theorem first_difference : 0 < P.length ∧ P[0] ≠ Q[0] := by decide

 theorem slope : (-g)^86 = eval (power (1,-2) 86) := by
  rw [eval_power]
  congr 1
  simp [eval,g]
  ring

 theorem positive_slope : 0 < (-g)^86 := by
  have hg := tail_arithmetic.2.2.2.1
  rw [show (86 : ℕ) = 2*43 by decide, pow_mul]
  exact pow_pos (sq_pos_of_ne_zero (neg_ne_zero.mpr (ne_of_gt hg))) _

 theorem endpoints : canonicalReturnLo high 86 = loU ∧ canonicalReturnHi high 86 = hiU ∧
    canonicalReturnLo low 86 = loV ∧ canonicalReturnHi low 86 = hiV := by
  have ht := tail_arithmetic.1
  rcases precise_t with ⟨tl,tu⟩
  have highOrder : compose (high true) 0 ≤ compose (high false) 0 := by
    rw [show (0 : ℝ) = eval (0,0) by simp [eval]]
    simp only [compose_eval]
    norm_num [high, returns, returnWord,repeatWord,block,U,C,composePair,step,shiftPair,eval]
    linarith
  have lowOrder : compose (low false) 0 ≤ compose (low true) 0 := by
    rw [show (0 : ℝ) = eval (0,0) by simp [eval]]
    simp only [compose_eval]
    norm_num [low, returns, returnWord,repeatWord,block,V,C,composePair,step,shiftPair,eval]
    linarith
  have den : 1-(-g)^86 ≠ 0 := ne_of_gt (by
    have hs := (return_slope_control 86 (by decide)).2.1
    linarith)
  simp only [canonicalReturnLo,canonicalReturnHi,canonicalAffineLo,canonicalAffineHi,
    if_pos positive_slope,min_eq_right highOrder,max_eq_left highOrder,
    min_eq_left lowOrder,max_eq_right lowOrder]
  rw [show (0 : ℝ) = eval (0,0) by simp [eval]]
  simp only [compose_eval]
  rw [slope]
  refine ⟨?_,?_,?_,?_⟩ <;> apply (div_eq_iff (by simpa [slope] using den)).mpr
  all_goals norm_num [high,low,returns,returnWord,repeatWord,block,U,V,C,
    composePair,step,shiftPair,loU,hiU,loV,hiV,power,mul,eval]
  all_goals nlinarith [ht]

 theorem endpoint_support : InSupport .G1 loU ∧ InSupport .G1 hiU ∧
    InSupport .G1 loV ∧ InSupport .G1 hiV := by
  rcases precise_t with ⟨tl,tu⟩
  norm_num [InSupport,supportUpper,loU,hiU,loV,hiV,eval]
  repeat' constructor
  all_goals linarith

theorem certP : EndpointCertificate budget loU hiU P h := by
  intro r hr
  have bound : r < 26 := by simpa [h,colorsD,colorsE] using hr
  refine ⟨⟨suffix_supported .G0 .G1 P legal.1 loU endpoint_support.1 r,?_⟩,
    ⟨suffix_supported .G0 .G1 P legal.1 hiU endpoint_support.2.1 r,?_⟩⟩
  all_goals interval_cases r
  all_goals simp only [max_le_iff,loU,hiU,compose_eval]
  all_goals norm_num [h,P,stem,block,U,C,colorsD,colorsE,loU,hiU,
    compose_eval,composePair,step,shiftPair,budget,eval,cut,T2,lam,g,phi,max_le_iff]
  all_goals repeat' constructor
  all_goals linarith [precise_t.1,precise_t.2]

 theorem certQ : EndpointCertificate budget loV hiV Q h := by
  intro r hr
  have bound : r < 26 := by simpa [h,colorsD,colorsE] using hr
  refine ⟨⟨suffix_supported .G0 .G1 Q legal.2.1 loV endpoint_support.2.2.1 r,?_⟩,
    ⟨suffix_supported .G0 .G1 Q legal.2.1 hiV endpoint_support.2.2.2 r,?_⟩⟩
  all_goals interval_cases r
  all_goals simp only [max_le_iff,loV,hiV,compose_eval]
  all_goals norm_num [h,Q,stem,block,V,C,colorsD,colorsE,loV,hiV,
    compose_eval,composePair,step,shiftPair,budget,eval,cut,T2,lam,g,phi,max_le_iff]
  all_goals repeat' constructor
  all_goals linarith [precise_t.1,precise_t.2]


end
end Reg.Support.FibonacciBranchStorageWitness
