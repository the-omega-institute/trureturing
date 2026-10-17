import D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
import D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJMInflationScore
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def T1 (e : Fin 10 → Fin 4) : ℤ :=
  256 * F1 e - ∑ h : Fin 3 → Fin 4, ejmIntNumerator (h 0) (h 1) (h 2) *
    F1 (Fin.append h (fun j : Fin 7 => e (Fin.natAdd 3 j)))
example : T1 ![0,0,0,0,0,0,0,0,0,0] = (-333398031441957) := by decide +kernel

def T2 (e : Fin 9 → Fin 4) : ℤ :=
  256 * F2 e - 64 * ∑ h : Fin 1 → Fin 4,
    F2 (Fin.append h (fun j : Fin 8 => e (Fin.natAdd 1 j)))
example : T2 ![0,0,0,0,0,0,0,0,0] = (342684669818304) := by decide +kernel


set_option trace.profiler true in
theorem lookup0 : F1 ![0,0,0,0,0,0,0,0,0,0] = (-10502458495547) := by rfl
#print axioms lookup0

set_option trace.profiler true in
theorem lookup1 : F2 ![0,0,0,0,0,0,0,0,0] = (892409425237) := by rfl
#print axioms lookup1
