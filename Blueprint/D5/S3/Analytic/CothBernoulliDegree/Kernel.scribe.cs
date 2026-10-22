using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CothBernoulliDegree;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivative certificates and estimates for rational kernels.",
        H("Rational kernels"), Blocks(
            Describe.Lean(DescribeId.Create("coth-kernel-phase-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.phase_bound"),
                H("A uniform negative phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real M at least five, the product of (1+(5/M)^2)^(-M/2) and sin(M arctan(5/M)) is at most -1/8. The arctangent lies above its chord on [0,1], while log(1+x^2) lies below its chord. These give a phase between 5 pi/4 and 5 and an amplitude at least sqrt(2)/8. The sine is at most -sqrt(2)/2 throughout that interval. Equality holds at M=5."))),
                DescribeRole.Theorem))));
}
