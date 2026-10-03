using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lipschitz frontier cover of an orthant-cut region.",
        H("Lipschitz frontier cover of an orthant-cut region"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-frontier-cover-inter-orthant"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra.exists_frontier_cover_inter_orthant"),
                H("Lipschitz frontier cover of an orthant-cut region"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Lipschitz frontier cover of an orthant-cut region. If D₀ is bounded with a Lipschitz " +
                    "cube cover of its frontier, then D₀ ∩ orthant (orthant cutting the coordinates g k) " +
                    "also has a Lipschitz cube-covered frontier: frontier (D₀ ∩ O) ⊆ frontier D₀ ∪ " +
                    "(closure D₀ ∩ frontier O) (frontier_inter_subset), the orthant boundary lands in " +
                    "finitely many coordinate hyperplanes, and each bounded hyperplane slice is cube- " +
                    "covered by exists_lipschitz_cube_cover_hyperplane_slab."))),
                DescribeRole.Theorem)
        )));
}
