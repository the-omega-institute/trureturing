using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class ExponentTheoremsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponent Theorems", H("Exponent Theorems"),
        Blocks(
            Paragraph(Text("Final exponent and length bounds for crystalline classes against congruent dual lattices. The prime ℓ of this comment is p in the code.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/ExponentTheorems.tame_types_exponent"),
                H("tame_types_exponent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Tame types. Let j be a homeomorphism onto G_p, K tame on inertia (Lift.IsTameType), κ = r²(N+1)², b + 6(W+η) + κ + 2 < p. For L of class (F, K(s⁻¹)) with jump sets in [−η, η] ∪ ε[b, b+W], p^{3κ+150(η+W+1)} Z_f(L) is orthogonal to the class (F, K) with jump sets in the opposite window.")))))));
}
