using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class CyclotomicCrossingFibresDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint cyclotomic-crossing Frobenius fibres.",
        H("Disjoint cyclotomic-crossing Frobenius fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-cyclotomic-crossing-fibres"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/CyclotomicCrossingFibres.exists_cyclotomicCrossing_fibres"),
                H("Disjoint cyclotomic-crossing Frobenius fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an abelian Galois extension L/K, σ in Gal(L/K), m ≥ 1 with m % 4 ≠ 2 and " +
                    "(disc L).natAbs coprime to m, there is a family S indexed by " +
                    "H_n = {τ in (ℤ/mℤ)ˣ : |Gal(L/K)| divides ord τ}. These sets are pairwise disjoint. " +
                    "Each lies in the unramified σ-Frobenius fibre of prime ideals of K and has " +
                    "Dirichlet density 1/(|Gal(L/K)|·|(ℤ/mℤ)ˣ|)."))),
                DescribeRole.Theorem)
        )));
}
