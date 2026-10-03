import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

open Matrix
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

namespace Reg.Support.GeneralInstrumentModels

theorem complete (d : ℕ) :
    ∑ _a : Unit, (0 : Matrix (Fin d) (Fin d) ℂ)ᴴ * 0 +
      ∑ _i : Unit, (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * 1 = 1 := by simp

theorem survival_zero_succ (d n : ℕ) :
    survival (fun _ : Unit => (0 : Matrix (Fin d) (Fin d) ℂ)) (n + 1) = 0 := by
  simp [survival, noClickDual]

theorem dark_layer_one (d : ℕ) :
    darkLayer (fun _ : Unit => (0 : Matrix (Fin d) (Fin d) ℂ))
      (fun _ : Unit => (1 : Matrix (Fin d) (Fin d) ℂ)) 1 = ⊥ := by
  simp [darkLayer]

end Reg.Support.GeneralInstrumentModels
