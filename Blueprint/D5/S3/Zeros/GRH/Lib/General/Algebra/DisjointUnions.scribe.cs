using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class DisjointUnionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint Unions", H("Disjoint Unions"),
        Blocks(
            Paragraph(Text("General lemmas of commutative and general algebra (textbook or folklore).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/DisjointUnions.sigma_bijective"),
                H("sigma_bijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Cohomology turns disjoint unions into products: the map H^n(∐ X_i, F) → ∏ H^n(X_i, F) given by pull-back along the inclusions is bijective.")))))));
}
