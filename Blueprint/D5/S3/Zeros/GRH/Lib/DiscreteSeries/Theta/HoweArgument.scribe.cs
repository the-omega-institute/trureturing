using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class HoweArgumentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Howe Argument", H("Howe Argument"),
        Blocks(
            Paragraph(Text("Howe's argument: joint harmonic generates Fock space modulo other K-types.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/HoweArgument.howe_argument"),
                H("howe_argument"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Howe's count: let G be a space of polynomials stable under the column action, containing a joint harmonic, the images of the row operators E_aa − Λ_a and compact lowerings, and 𝔤P for each row K-highest P of weight outside Λ + HCParam.rootCone. Then G is everything.")))))));
}
