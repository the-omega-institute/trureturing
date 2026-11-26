using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class CellNeighbourhoodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cell Neighbourhood", H("Cell Neighbourhood"),
        Blocks(
            Paragraph(Text("Jacobian and injectivity of the open-cell double coset chart of U(p,q). Explicit perturbation bounds for determinant, inverse and discriminant near an open-cell matrix.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/CellNeighbourhood.mem_openCell_and_bounds_of_near"),
                H("mem_openCell_and_bounds_of_near"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let M ≥ 8(ϱ+1), 𝗀(Z) ≥ M⁻¹, all |Z_ab| ≤ M², P ≥ M^{9(ϱ+1)} and ‖Z' − Z‖ < P⁻⁶. Then 𝗀(Z') ≥ 𝗀(Z)/2, Z' lies in Ω (Shape.openCell), and ‖Z'⁻¹‖, ‖Z'‖, δ(Z')^{−1/2} ≤ P, with δ = cornerDefect.")))))));
}
