using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class IndecomposablePermutationDoubleArrayDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/kurkov2024a003319");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual indecomposable-permutation count is the common exact left border of Kurkov's two arrays.",
        H("Indecomposable Permutations and Kurkov's Double Array"),
        Blocks(
            Paragraph(Text(
                "All indices are natural numbers. A permutation of Fin n is indecomposable "
                    + "when no proper nonempty initial interval is invariant. The two arrays "
                    + "are defined independently by their exact source recurrences; the count "
                    + "is not replaced by a recurrence-defined proxy.")),
            Node(
                "indecomposable",
                "Indecomposable permutations",
                "IndecomposablePerm",
                "For each n, this subtype contains exactly the permutations p of Fin n for "
                    + "which no k with 0<k<n preserves membership in the initial segment "
                    + "{0,...,k-1}. Translating Fin n by one gives the source convention on "
                    + "permutations of {1,...,n}.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "count",
                "The actual permutation count",
                "c",
                "The value c(n) is the finite cardinality of IndecomposablePerm(n). In "
                    + "particular, its meaning comes from the source permutation class rather "
                    + "than either triangular recurrence.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "u-array",
                "Kurkov's first array",
                "U",
                "The initial row is U(0,k)=1. The successor recurrence is "
                    + "U(m+1,k)=(k+2)U(m,k+1)+sum_{j=0}^{k} U(m,j), with the displayed "
                    + "finite sum represented by range(k+1). This is OEIS A370380.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "v-array",
                "Kurkov's second array",
                "V",
                "The initial row is V(0,k)=1. The successor recurrence is "
                    + "V(m+1,k)=sum_{j=0}^{k+1} binomial(k+2,j+1)V(m,j), represented "
                    + "by range(k+2). This is OEIS A370381.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "result",
                "Kurkov's double-array conjecture",
                "result",
                "There is one empty and one singleton indecomposable permutation. For n>=2, "
                    + "the theorem proves c(n)=U(n-2,0)=V(n-2,0). For the actual count, the "
                    + "least positive invariant prefix gives a proved equivalence between a "
                    + "permutation and its first indecomposable block together with the "
                    + "remaining permutation. Cardinality yields the factorial convolution. "
                    + "Partial sums and rising factorials give the same convolution for U. "
                    + "For V, a finite Nat-valued binomial operator is iterated on a shifted "
                    + "row, a delta sequence and power sequences; its unrolling gives the "
                    + "third convolution. Unit-diagonal triangular uniqueness then identifies "
                    + "both borders with the actual count. All auxiliary identities remain "
                    + "local to this theorem.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a003319-kurkov-double-array"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("a003319-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);
}
