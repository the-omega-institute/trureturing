using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class CrystallineBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Bound", H("Crystalline Bound"),
        Blocks(
            Paragraph(Text("Case analysis on ℓ bounding crystalline classes modulo those orthogonal to congruent lattices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/CrystallineBound.crystalline_defect_le"),
                H("crystalline_defect_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Local loss, crystalline case. Let L be crystalline with jumps in U'; let U, U' lie in opposite windows Lift.IsInJumpWindow at b + δ (thick) or G + δ (thin), with the listed conditions on sizes and on a Kummer chart. Assume U' lies in [−η, 0], or negative members of U' and negative members of U are ≤ −h/2 with ≤ μ jumps per embedding in [−η, η]. Then Z_f(L) modulo Lift.cupOrthogonal for crystalline lattices with jumps in U has normalised length ≤ [G_ℓ : j(Γ)]·y if y ≥ 10⁵(rk L·⌊2λ/Q⌋·m + μλ), λ = lambdaLoss.")))))));
}
