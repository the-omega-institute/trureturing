using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class AinfDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ainf", H("Ainf"),
        Blocks(
            Paragraph(Text("Tilt of O_C, A_inf, theta, epsilon, xi, mu, actions; tilt is algebraically closed.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/Ainf.isAIC"),
                H("isAIC"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every monic polynomial of positive degree over O^♭, the tilt of the ring of integers of C_p, has a root in O^♭.")))))));
}
