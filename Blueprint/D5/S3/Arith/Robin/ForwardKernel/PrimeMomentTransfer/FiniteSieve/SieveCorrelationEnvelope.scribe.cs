using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveCorrelationEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decreasing error bounds for interval correlations",
        H("Decreasing error bounds for interval correlations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("antitone-error-envelope"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.antitone_error_envelope"),
                H("antitone error envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A uniformly negligible family of interval errors that is uniformly bounded on each bounded scale interval admits a nonnegative majorant, antitone on [2,infinity), tending to zero and bounding every error by the majorant times its moment scale. The majorant is the supremum of all subsequent normalized errors together with zero; local boundedness and eventual smallness ensure finiteness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("correlation-locally-bounded"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope.correlation_locally_bounded"),
                H("correlation locally bounded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural order and nonnegative window size M, the distinct correlations of an arbitrary real function on finite shift sets are locally uniformly bounded after division by (H log H)^(k/2) on H >= 2. On each bounded scale interval every shift tuple lies in one fixed finite product of bounded sets of natural numbers."))),
                DescribeRole.Theorem))));
}
