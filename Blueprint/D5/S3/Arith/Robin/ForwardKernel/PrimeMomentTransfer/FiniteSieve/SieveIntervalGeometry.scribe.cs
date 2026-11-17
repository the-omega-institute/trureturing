using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveIntervalGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntervalGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer interval geometry for finite sieve sums.",
        H("Integer interval geometry for finite sieve sums."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-interval-card-le"),
                DeclarationHandle.Create(Prefix + "sieve_interval_card_le"),
                H("Cardinality with endpoint error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H>0 and 0<=a<=b, the number of selected integer points is at most H(b-a)+1. "
                    + "The difference of the two floors gives the count, with an endpoint error bounded by one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-interval-moment-prefix"),
                DeclarationHandle.Create(Prefix + "sieve_interval_moment_prefix"),
                H("Reduction to the prefix of the same cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real scale and endpoints, every natural moment of the interval sieve sum equals the corresponding "
                    + "moment for the prefix whose length is the number of selected integer points. "
                    + "Reversed floor endpoints select the empty interval; otherwise translation gives the prefix law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sieve-endpoint-grid"),
                DeclarationHandle.Create(Prefix + "sieveEndpointGrid"),
                H("sieve endpoint grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real window M and mesh delta, the finite endpoint grid consists of delta times the natural numbers from zero through the natural floor of M/delta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-round-down"),
                DeclarationHandle.Create(Prefix + "sieveRoundDown"),
                H("sieve round down"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An endpoint x rounded down to mesh delta is delta times the natural floor of x/delta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sieve-grid-rounding"),
                DeclarationHandle.Create(Prefix + "sieve_grid_rounding"),
                H("A finite mesh for ordered endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For M>=0, delta>0 and 0<=a<=b<=M, round each endpoint x down to delta*floor(x/delta). "
                    + "Both rounded endpoints belong to the finite grid delta*n for 0<=n<=floor(M/delta), "
                    + "remain ordered in [0,M], and differ from the original endpoints by at most delta."))),
                DescribeRole.Theorem))));
}
