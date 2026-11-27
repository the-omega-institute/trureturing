using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class KunnethDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kunneth", H("Kunneth"),
        Blocks(
            Paragraph(Text("Künneth formula in Hodge cohomology, surjectivity of the cross product.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/Kunneth.kunneth"),
                H("kunneth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Künneth: over a field k of characteristic 0, if X has an atlas of dimension d, every class in Hdg^n(X × X) is a finite sum of cross products x × y of Hodge classes on X.")))))));
}
