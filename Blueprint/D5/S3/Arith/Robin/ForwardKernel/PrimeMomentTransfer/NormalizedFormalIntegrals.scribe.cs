using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class NormalizedFormalIntegralsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted normalized estimates for formal cubic and fourth moments.",
        H("Normalized formal integrals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integrated-third-envelope"),
                DeclarationHandle.Create(Prefix + "integrated_third_envelope"),
                H("Integration of the cubic envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose N is at least two, H is positive, C and E are nonnegative, and w has supported bounded variation norm at most B. If the absolute formal cubic moment on [N,2N] is at most C times the sum of E times (H log N) to the power three halves and H times log N squared, its weighted integral divided by N times (H log N) to the power three halves has absolute value at most C B times the sum of E and the square root of log N divided by H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integrated-fourth-envelope"),
                DeclarationHandle.Create(Prefix + "integrated_fourth_envelope"),
                H("Integration of the fourth envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose N is at least two, H is positive, C and E are nonnegative, and w has supported bounded variation norm at most B. If the difference between the formal fourth moment and H squared times (log x minus log H) squared times the fourth overlap pairing is uniformly bounded by C times the sum of E H squared log N squared and H squared log N, the difference between their weighted integrals after normalization is at most C B times the sum of E and the reciprocal of log N."))),
                DescribeRole.Theorem)
            )));
}
