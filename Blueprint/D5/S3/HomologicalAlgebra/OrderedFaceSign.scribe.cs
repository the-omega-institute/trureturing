using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class OrderedFaceSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral orientation signs for incidences of ordered simplices.",
        H("Ordered face sign"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("insertion-sign"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/OrderedFaceSign.insertionSign"),
                H("The orientation sign at a vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Raise minus one to the number of face vertices that precede the chosen vertex. "
                    + "This count gives the same incidence sign on either side of the insertion or deletion."))),
                DescribeRole.Definition)),
        []));
}
