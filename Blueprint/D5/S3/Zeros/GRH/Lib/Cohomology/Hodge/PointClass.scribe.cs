using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class PointClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Point Class", H("Point Class"),
        Blocks(
            Paragraph(Text("Class of a rational point in Hodge cohomology; independence of choices, excision, sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass.map_eq_sum_pointClass"),
                H("map_eq_sum_pointClass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let X be separated, s a finite set of k-points, U = X∖s. If ξ ∈ Hdg^d(X, U) has local multiplicity n(z) ∈ k at each z ∈ s (IsPointSum), its image in Hdg^d(X) is Σ_{z∈s} n(z)·cl(z).")))))));
}
