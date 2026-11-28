using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class OnePlaceDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Place Defect", H("One Place Defect"),
        Blocks(
            Paragraph(Text("Crystalline defect of the dual of a block at one place, by cases.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/OnePlaceDefect.block_defect_le_at_place"),
                H("block_defect_le_at_place"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Local loss at one place above ℓ. For O large take lattices: one of rank r with row jumps J, others with single jump c ∈ [0, t); and a class Lift.InClass with jumps among theirs, crystalline, or tame for ℓ ∣ g. For L among them and in the class, Z_f(L^∨(1)) modulo Lift.cupOrthogonal has normalised length ≤ [G_ℓ : j(Γ)]·rk L·loss/x, x = 1 for the row, else D.t.")))))));
}
