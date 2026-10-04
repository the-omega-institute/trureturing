using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypermatrix;

internal sealed class MaskedHypermatrixCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");
    private static readonly LibraryNoteRef Koszul =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/berkesch2013tensorcomplexes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original masked nondegenerate hypermatrix count", H("Original masked nondegenerate hypermatrix count"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"), H("Original masked nondegenerate hypermatrix count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, Koszul),
                Blocks(Paragraph(Text("Let F be any finite field, q its cardinality, and k any natural number at least one. Let lambda,mu map Fin(k) to natural numbers and be antitone. For every j assume mu(j) at most lambda(j), lambda(j) at most k minus j, and mu(j) strictly less than k minus j. Count the actual pairs of (k plus one)-by-k matrices over F whose first face vanishes in rows r at least k plus one minus lambda(j), whose second face vanishes in rows r at least k plus one minus mu(j), and whose evaluated integral coefficientPolynomial is nonzero. The count is q to k squared times (q minus one) to 2k times the product over j of [k plus one minus j minus lambda(j)]_q times [k minus j minus mu(j)]_q. The determinant is evaluated on the same tensor entries. Its rank equivalence is internal: every nonzero face combination over the algebraic closure has rank k exactly when this determinant is nonzero. The proof connects these actual objects to the constructed masked-cell count and factors the actual weighted sum. It retains k=1 and every characteristic, including characteristic two; no rational-combination restriction or normalization assumption is added."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("koprowski-lewis-2026-conjecture-3-1-hypermatrix-count"),
                    ResolutionKind.Proved))
        ), []));
}
