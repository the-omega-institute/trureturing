using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class FlipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flip", H("Flip"),
        Blocks(
            Paragraph(Text("Adjoint map exchanges the two groups of a dual pair, up to a phase.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/Flip.exists_pairTheta_flip"),
                H("exists_pairTheta_flip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V' have signs opposite to V and x_{V'} l = (1, conj(cα/ᾱ))·x_V. For each b some z of modulus one has θ^{W,V'}_{b⁻¹υ^{rk W}, a'⁻¹υ^{rk V}}(f^φ)(h, lg) = z θ^{V,W}_{a',b}(f)(g,h) for all a', f, g, h, φ being flipCoords.")))))));
}
