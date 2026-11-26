using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Wick;

internal sealed class AffineOccurrenceWickDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wick evaluation by occurrence positions",
        H("Affine occupation moments"),
        Blocks(
            Describe.Lean(DescribeId.Create("affine-occurrence-wick-wick"),
                DeclarationHandle.Create(Prefix + "wick"),
                H("Ordered Wick evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty word evaluates to one. The head either contributes its mean or pairs with a "
                    + "tail position. A paired position is removed before evaluating the remaining word. "
                    + "Equal labels at distinct positions contribute separately."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("affine-occurrence-wick-affine-moment-eq-wick"),
                DeclarationHandle.Create(Prefix + "affineMoment_eq_wick"),
                H("Affine moment as a Wick evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a symmetric covariance, take the occupation of the mapped word and evaluate its "
                    + "affine moment. The result is the Wick evaluation on the original word with both "
                    + "covariance entries and means pulled back along the label map. The occupation "
                    + "recurrence gives one term per tail occurrence, with multiplicity for repeated labels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-occurrence-wick-affine-moment-pullback"),
                DeclarationHandle.Create(Prefix + "affineMoment_pullback"),
                H("Affine moments under a label map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite occurrence type, pulling the symmetric covariance and the mean back "
                    + "before taking the moment gives the same result as mapping the occurrence word first. "
                    + "The map can identify distinct positions."))),
                DescribeRole.Theorem))));
}
