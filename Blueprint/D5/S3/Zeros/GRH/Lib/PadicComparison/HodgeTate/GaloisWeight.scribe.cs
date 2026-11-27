using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class GaloisWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois Weight", H("Galois Weight"),
        Blocks(
            Paragraph(Text("Galois acts on Hodge–Tate images of degree h through a cyclotomic power.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisWeight.hodgeTateMap_galois_twist"),
                H("hodgeTateMap_galois_twist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let g ∈ G_p fix E, let t ∈ k equal χ(g⁻¹), and let x be a Hodge class over E with λ_h(x_k) = restrictToPairs ξ. Then t^h ξ and the pull-back of ξ along the g-twist of tests have the same image under restrictToPairs.")))))));
}
