using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyTwoGroupNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Abstract finite abelian two-groups in coordinates", H("Abstract finite abelian two-groups in coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-twogroupnormalization-coordinate-presentation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyTwoGroupNormalization.coordinate_presentation"),
                H("Discharge the coordinate presentation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite abelian structure theorem supplies prime-power cyclic factors. A factor with positive exponent has its prime dividing the group order, so the two-group cardinality forces that prime to be two. Zero exponents remain trivial independently of their prime. Reindexing gives coordinates indexed by a finite ordinal. If fewer than two exponents were positive, evaluation would inject the group into one cyclic factor, or the whole group would be trivial; either case contradicts noncyclicity."))), DescribeRole.Theorem))));
}
