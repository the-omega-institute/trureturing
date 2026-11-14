/- GID: D5/S3/Combinatorics/Orthogonality/SevenBitClassDomains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenBitClassDomains
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete original minimum-vector class partition. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitGeometry
/-! The126 possible nonzero, noncharacteristic minima exhaust the original
deleted domain. No compatible class is sampled or dropped. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
open SevenBitGeometry
def minimum (i : Fin 126) : Vector := ⟨i.val+1,by omega⟩
def candidates (i : Fin 126) : List Vector :=
  deleted.filter (fun v => decide (minimum i < v) && compatible (minimum i) v)
end D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
