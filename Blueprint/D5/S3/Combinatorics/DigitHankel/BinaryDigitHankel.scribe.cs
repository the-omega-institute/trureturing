using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class BinaryDigitHankelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonvanishing indices of the binary digit Hankel determinants at t = -2 are exactly the triples around ceil(2^(k+2)/3).",
        H("Nonvanishing Indices at Minus Two"),
        Blocks(
            Node("binary-digit-hankel-result", "The exact nonvanishing indices", "result", "For a nonnegative integer u with binary digits epsilon_j, let S(u,t) = sum_j epsilon_j t^j, and let H(n,t) = det(S(i+j,t)) for indices i and j from zero to n minus one. Put n_k = ceil(2^(k+2)/3) for every nonnegative integer k. For every integer n at least two, H(n,-2) is nonzero if and only if n is one of n_k - 1, n_k, or n_k + 1 for some nonnegative integer k. This establishes the case d = 2 of Conjecture 5.7 in Section 5.1 of Sobolewski and Ulas's paper, arXiv:2607.09376v1. Sparse binary kernel vectors force vanishing outside the triples. Reflection recurrences and simultaneous determinant evaluations show that all three members of each triple are nonzero, with the first two triples evaluated directly. The statement concerns t = -2; the equivalence for t = 2 times a primitive root of unity of higher order is not asserted.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("sobolewski-ulas-binary-hankel-minus-two"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
