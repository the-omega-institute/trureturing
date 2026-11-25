/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueNodes
   generality: I
   mirror-B: none(waiver:ordinary-seven-site-certificate-supplier)
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueData]
   utility: none
   digest: Forty-seven residue-line interpolation nodes with residue 39 omitted. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueData

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

def nodes (i : Fin 47) : Fin 1009 :=
  ⟨if i.val < 39 then i.val else i.val + 1, by split <;> omega⟩

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
