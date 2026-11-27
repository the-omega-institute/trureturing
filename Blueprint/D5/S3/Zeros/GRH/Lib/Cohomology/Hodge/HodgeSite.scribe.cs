using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class HodgeSiteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Site", H("Hodge Site"),
        Blocks(
            Paragraph(Text("Ext classes of cocycles of functors; connecting classes commute up to sign. Hodge cohomology as Ext on pairs (algebra, free module); scaling, base change, charts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/HodgeSite.exists_univPoint"),
                H("exists_univPoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a chart a over a field E, with ring R and q étale coordinates, some E-algebra section u of R ⊕ R^q → R is universal: composing with u is a bijection from maps of tests (R, R^q) → (A, M) to E-algebra maps R → A ⊕ M.")))))));
}
