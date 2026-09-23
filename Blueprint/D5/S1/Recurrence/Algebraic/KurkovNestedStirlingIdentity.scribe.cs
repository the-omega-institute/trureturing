using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovNestedStirlingIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/kurkov2026a132393");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's full nested rational sum equals the unsigned Stirling number.",
        H("Kurkov's Nested Stirling Identity"),
        Blocks(
            Paragraph(Text(
                "The target is Mikhail Kurkov's May 24, 2026 conjecture in OEIS A132393. "
                + "All parameters are natural numbers, with n at least zero and m at least one. "
                + "All displayed summand arithmetic is rational except natural indices, "
                + "factorials, falling factorials and the sign exponent. The falling factorial "
                + "is descending. No determinant evaluation or other mathematical conclusion "
                + "is assumed in the theorem.")),
            Node("Chain", "The literal nested summation domain",
                "A chain is an antitone function from Fin m to Fin (n+1). "
                + "Thus its coordinates satisfy n >= j_1 >= ... >= j_m >= 0. "
                + "The finite sum counts every such chain once, exactly as the nested sums.",
                DescribeRole.Definition),
            Node("sourceTerm", "The source summand",
                "The formal position i represents t=i+1. The numerator is the descending "
                + "factorial of n+i of length j_t. Rational Vandermonde differences are "
                + "j_q-j_p+p-q. The denominator factors are (n-j_t+t)^(m+1) and "
                + "(j_t+m-t)!, each positive on the chain domain. Consequently the natural "
                + "subtractions in the indices agree with ordinary integer subtraction.",
                DescribeRole.Definition),
            Node("sourceRHS", "The full rational expression",
                "The finite chain sum is multiplied by (n+m)! and the product of "
                + "(n+i)^i for positions i from one through m. No finite cutoff or "
                + "fixed-m specialization enters this definition.",
                DescribeRole.Definition),
            Node("result", "The full unbounded Kurkov identity",
                "Put N=n+m and l_t=n-j_t+t. This gives a proved bijection with "
                + "m-element subsets of 1,...,N. Factorial and sign normalization, "
                + "the attributed rectangular Cauchy-Binet proof and Mathlib's "
                + "Vandermonde determinant turn the literal sum into a signed moment determinant. "
                + "Moment indices are integers. Frozen Stirling inclusion-exclusion supplies "
                + "the zero and negative moments; Pascal's identity gives the moment recurrence. "
                + "Row reversal cancels the global sign. A unit triangular column operation "
                + "and a boundary cofactor give the determinant recurrence. The node-count "
                + "rank bound supplies its vanishing boundary. Multiplying by N! yields "
                + "exactly the unsigned Stirling recurrence and initial values. "
                + "All classical identities remain proof-local; the only public theorem "
                + "is this source assertion.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a132393-kurkov-nested-stirling-identity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, string explanation,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create("a132393-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(explanation))), role, claim);
}
