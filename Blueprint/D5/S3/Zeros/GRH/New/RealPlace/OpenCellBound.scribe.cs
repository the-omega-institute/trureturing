using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class OpenCellBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Open Cell Bound", H("Open Cell Bound"),
        Blocks(
            Paragraph(Text("Mean-square bound for Bessel integrals on the open cell.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/OpenCellBound.open_cell"),
                H("open_cell"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Open-cell bound. For ρ ≥ B, 𝗀(Z(γ)) > 0, Box(ρ) meeting γBox(ρ): there are compact A, random t ∈ 𝖴⁰H and n of mass ≤ cellMass with 𝔼‖∫_A φ(y) W(γty)W(ty)* dy‖² ≤ ∫|φ|² dn; almost surely A contains the y ∈ Box(ρ) with R(γty) ≤ ρ.")))))));
}
