using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ThetaReflectedKernelComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict reflected-entry comparison for the complete physical theta kernel.",
        H("Complete physical entries and their reflections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-kernel-reflection-comparison"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison."
                    + "physical_kernel_reflection_comparison"),
                H("Positive entries strictly dominate reflected entries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every a,b>0 and every finite real v>=0, the literal physical "
                        + "kernel satisfies 0<K_v(a,-b)<K_v(a,b). Its definition is one half the "
                        + "integral over y>|(a+b)/2| of y*cosh(2*v*y)*Phi(y+(a-b)/2)*Phi(y-(a-b)/2), "
                        + "with the complete original theta kernel Phi=romikPhi.")),
                    Paragraph(Text("Put p=(a+b)/2, d=|a-b|/2 and r0=p^2+d^2. The two exact changes "
                        + "of variable r=y^2+d^2 and r=y^2+p^2 retain the Jacobian and express both "
                        + "entries as one quarter of a radial integral over r>r0. Strict concavity "
                        + "of log(Phi(sqrt(r))) compares symmetric pairs, and the cosh factor "
                        + "preserves the comparison. The possible zero square occurs at one "
                        + "radial point and is excluded only on a null set. Strictness is paid "
                        + "on a nonempty interval.")),
                    Paragraph(Text("The actual Gaussian bound supplies both original weighted L1 "
                        + "integrands and a radial majorant M^2*exp(v^2)*exp(-r). Thus no upper "
                        + "bound on finite v is needed. These are the W2, W12 and W13 formulas "
                        + "in the existing Suzuki source note, now with their analytic suppliers "
                        + "paid in Lean. This is a repository derivation from the classical "
                        + "theta concavity theorem; no literature-priority claim is made.")),
                    Paragraph(Text("Taking b=a and v=0 gives strict positivity of the original odd "
                        + "diagonal difference. Entrywise reflection domination does not establish "
                        + "positive definiteness for arbitrary signed coefficients, all finite Gram "
                        + "matrices, the full Weil pairing, Robin's inequality or RH."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Fourier/ThetaRadialCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/SourceThetaMomentBounds"))
        ]));
}
