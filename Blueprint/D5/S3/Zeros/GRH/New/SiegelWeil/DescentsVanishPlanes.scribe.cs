using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.SiegelWeil;

internal sealed class DescentsVanishPlanesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descents Vanish Planes", H("Descents Vanish Planes"),
        Blocks(
            Paragraph(Text("Climbing the theta tower: bounded descents with a too small Hecke root vanish.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/SiegelWeil/DescentsVanishPlanes.descentsVanish_add_planes"),
                H("descentsVanish_add_planes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W' = W ⊕ ℍ^p (adapted), V definite, r = rk W, n = rk V > 2r + 2p + 3, w split, w̄ ∈ S, a's base change unramified at w̄, Y automorphic, spherical at w, H_w(X)Y = 0, |X| = q_w^{(r+2−2n)/2}. Then DescentsVanish for W, a implies it for W', aυ^p.")))))));
}
