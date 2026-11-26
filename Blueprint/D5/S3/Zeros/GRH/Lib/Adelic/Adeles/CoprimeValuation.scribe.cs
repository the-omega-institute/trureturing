using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class CoprimeValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime Valuation", H("Coprime Valuation"),
        Blocks(
            Paragraph(Text("Places, completions, adeles, integral adeles, maps under field embeddings, CM conjugation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/CoprimeValuation.eq"),
                H("eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Two continuous maps to a Hausdorff space that agree on the image of a map with dense range are equal.")))))));
}
