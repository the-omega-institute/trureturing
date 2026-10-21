using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class EvenCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.",
        H("Actual Gamma form core: EvenCore"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-evencore-actual-ioc-exists-weil-test-core-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation"),
                H("actual ioc exists weil test core approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows."))),
                DescribeRole.Theorem))));
}
