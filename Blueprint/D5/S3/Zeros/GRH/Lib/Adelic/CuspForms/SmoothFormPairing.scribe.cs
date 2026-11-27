using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class SmoothFormPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth Form Pairing", H("Smooth Form Pairing"),
        Blocks(
            Paragraph(Text("Integral elements supported off a modulus are congruent to one; block embedding. Smooth algebraic modular forms on definite unitary groups, right translation, invariant pairing.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/SmoothFormPairing.smoothPairing"),
                H("smoothPairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a σ-sesquilinear B invariant under the weight κ action of U(J)(E), V definite, the pairing (φ, φ') ↦ ∫ B(φ(g), φ'(g)) dg of forms, over Γ\\G_f with vol K₀ = 1.")))))));
}
