using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldFaithfulnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithfulness of the Original Fixed-Sector Action",
        H("Faithfulness of the Original Fixed-Sector Action"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-twisted-vacuum-coefficient"),
                DeclarationHandle.Create(Prefix + "originalI_three_eq_vacuum"),
                H("Recovering the fixed vacuum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In rank 24, the original mode of index three takes a pair of negative twisted states "
                    + "of weight two to the fixed-sector vacuum after rescaling the second state. "
                    + "Its vacuum scalar is the same nonzero normalized coefficient used in the Leech vacuum channel."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fixed-action-faithful"),
                DeclarationHandle.Create(Prefix + "fixedParitySlice_faithful"),
                H("Detecting fixed states with twisted modes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every mode of a fixed state vanishes on the negative twisted sector, "
                    + "the mixed Jacobi identity forces its creation on the recovered vacuum to vanish."))),
                DescribeRole.Theorem))));
}
