using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Annihilation of the integer recurrence", H("Annihilation of the integer recurrence"), Blocks(
            Paragraph(Text("The split Horner equalities start at the zero vector, follow all 58 coefficients, and end at the zero vector. This is an exact integer assertion. The diagram action bridge identifies the sparse recurrence with left multiplication in the literal planar diagram algebra.")),
            Describe.Lean(DescribeId.Create("annihilation"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.annihilation"),
                H("annihilation"), StatementSource.FromAuthor(Disp(Equal(Id("hornerValue"), Id("ZeroVector")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("ZeroVector(i)=0 for every i in Fin(8192)."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
}
