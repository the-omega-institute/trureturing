using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.Dual;

internal sealed class DualWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual Weights", H("Dual Weights"),
        Blocks(
            Paragraph(Text("Integral invariant pairing of opposite weights; it gives the values of ofAlgForm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/Dual/DualWeights.exists_dual_pairing_of_isHCParam"),
                H("exists_dual_pairing_of_isHCParam"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For weights with parameters l and −l there is an invariant integer bilinear pairing A with: F_η(x, g) = A(η(g), ρ(x)v⁺) for algebraic forms η of the second weight; CA = hookNumber κ' for an integer matrix C; each A(·, v) = ⟨v', ·⟩ with ‖v'‖ = ‖v‖.")))))));
}
