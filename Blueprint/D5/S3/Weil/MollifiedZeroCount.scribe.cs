using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class MollifiedZeroCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count zeta zeros using a mollified second moment",
        H("Count zeta zeros using a mollified second moment"),
        Blocks(Describe.Lean(
            DescribeId.Create("right-strip-dyadic-count-le-of-mollified-second-moment"),
            DeclarationHandle.Create("D5/S3/Weil/MollifiedZeroCount.rightStripDyadicCount_le_of_mollified_second_moment"),
            H("From a vertical mean square to a zero count"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At each actual zeta zero the mollified error equals minus one. The disk mean-value "
                + "inequality forces each disk to carry a definite amount of squared error. The existing "
                + "local zero count controls the overlap with multiplicities. Integrating the vertical "
                + "bound over the fixed horizontal interval and absorbing a logarithm yields the asserted "
                + "dyadic estimate."))),
            DescribeRole.Theorem))));
}
