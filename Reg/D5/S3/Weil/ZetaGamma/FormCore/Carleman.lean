/- SOURCE_ONLY_UNCOMPILED. Source pins and faithful attempt inventory, not validated registrations. -/
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.Carleman

-- The actual candidate readout is the two-variable Carleman pairing kernel. A faithful rejected family must violate the complete integrability-and-product-bound law while leaving the original L2 inputs fixed; the zero kernel does not reject that law. No explicit L2 witness for a rejected singular kernel, and hence no full-family sensitivity/dependence certificate or raw product-lambda source selection, is supplied.
def source_carleman_integrable_and_integral_le := @_root_.D5.S3.Weil.ZetaGamma.FormCore.Carleman.carleman_integrable_and_integral_le

end Reg.D5.S3.Weil.ZetaGamma.FormCore.Carleman
