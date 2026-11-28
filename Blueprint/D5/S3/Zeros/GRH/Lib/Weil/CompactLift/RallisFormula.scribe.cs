using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.CompactLift;

internal sealed class RallisFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rallis Formula", H("Rallis Formula"),
        Blocks(
            Paragraph(Text("Definite theta lift equals class-sum lift of algebraic forms; matching of parameters. Seesaw: periods of a descent are read on periods of a lift. Rallis inner product formula for sharp data; injectivity of the lift in Weil's range.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/CompactLift/RallisFormula.rallis_inner_product_euler"),
                H("rallis_inner_product_euler"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Rallis inner product formula, rk T > 2 rk S, v an edge from type e: there is A ≠ 0 such that, for F sharp for J of mass c, the lift L by v ⊗ F kills no nonzero J-invariant form y, and ⟨Ly', Ly⟩ = Ac∑ρ(γ)⟨y', R(γ)y⟩ over cosets off S₀ (cosetTerm).")))))));
}
