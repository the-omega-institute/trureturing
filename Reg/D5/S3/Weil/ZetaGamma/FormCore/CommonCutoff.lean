/- SOURCE_ONLY_UNCOMPILED. Source pins and faithful attempt inventory, not validated registrations. -/
import D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff

-- The actual family is rho(s) with the original epsilon>0 tail guard. Constant one is a plausible rejected integrability family, not a proved source-bound certificate here. The endpoint-dependent half-line rejection, nonconstant observation and raw implicit measure/function selections remain unproved.
def source_actual_density_tail_integrable := @_root_.D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_density_tail_integrable

-- The source law simultaneously asserts two energy-tail integrability facts, image-pairing integrability and the signed finite-cutoff identity. A readout for only one equality is not equivalent to that conjunction. The intended joint energy/correlation family lacks a rejected fixed-input witness, joined source selections and complete sensitivity/dependence proofs; generic transport enrollment alone does not supply them.
def source_actual_common_cutoff_integrable_and_identity := @_root_.D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity

end Reg.D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff
