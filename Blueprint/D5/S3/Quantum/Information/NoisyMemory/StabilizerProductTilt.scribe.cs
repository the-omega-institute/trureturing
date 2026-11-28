using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.NoisyMemory;

internal sealed class StabilizerProductTiltDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/NoisyMemory/StabilizerProductTilt.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/chen2026noisyquantummemory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp reciprocal moments for paired product laws with bounded coordinate increments.",
        H("Reciprocal moments of Boolean product laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocal-product-bound"),
                DeclarationHandle.Create(Module + "product_average_mul_reciprocal_le"),
                H("Sharp bound from one-coordinate increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let f be positive on Boolean strings, with every change from zero to one "
                    + "increasing f by a factor in [1,2]. The expectation of f under independent "
                    + "inclusion rates p, multiplied by the expectation of its reciprocal under "
                    + "independent rates w, is bounded by the product of "
                    + "max(1,(1+pᵢ)(1−wᵢ/2)). The proof conditions on one bit and "
                    + "optimizes the ratio of its two conditional averages."))),
                DescribeRole.Theorem))));
}
