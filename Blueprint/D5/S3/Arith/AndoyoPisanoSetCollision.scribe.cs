using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class AndoyoPisanoSetCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/AndoyoPisanoSetCollision.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/andoyo2026pisanolegendrecollision");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The distinct integer seed pairs (0,1) and (1,1) have equal complete Pisano sets.",
        H("A collision of complete Pisano sets"),
        Blocks(
            Definition("integer-recurrence", "F", "Integer Fibonacci seeds",
                "For all integers a and b, F(a,b,0)=a, F(a,b,1)=b, and "
                + "F(a,b,n+2)=F(a,b,n+1)+F(a,b,n). In particular the zeroth term is included."),
            Definition("scalar-period", "ScalarPeriod", "Positive scalar periods",
                "A natural t is a scalar period modulo p exactly when t>0 and, for every "
                + "natural n including zero, the casts of F(a,b,n+t) and F(a,b,n) in ZMod p agree."),
            Definition("least-period", "pi", "The least positive scalar period",
                "The period is the natural infimum of the set of positive scalar periods. "
                + "For the two seed pairs used in the theorem, finite invertible pair dynamics "
                + "provides a positive period, and the infimum belongs to that set and is no larger "
                + "than every member. Equality of the full positive-period predicates gives the "
                + "same least positive period for the shifted pair."),
            Definition("index-counts", "signCount", "Legendre counts with multiplicity",
                "For a prime p and an integer sign s, count indices n in Finset.range(pi(p,a,b)) "
                + "whose Legendre symbol legendreSym p (F(a,b,n)) equals s. This is an index set; "
                + "repeated residue values contribute separately. The three signs used are 1, -1 and 0."),
            Definition("integer-balance", "K", "The integer Pisano-Legendre balance",
                "Cast each of the three natural counts to the integers before subtracting: "
                + "K=N(1)-N(-1)-N(0). The zero class is subtracted explicitly."),
            Definition("complete-set", "chi", "The complete Pisano set",
                "For arbitrary integer a and b, chi(a,b) is the set of integers K(p,a,b) "
                + "as p ranges over every prime different from two."),
            Describe.Lean(DescribeId.Create("equal-pisano-sets"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An affirmative answer to Andoyo's Question 5.3"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("There exist integers a1,b1,a2,b2 with distinct ordered "
                        + "pairs, each different from (0,0), and chi(a1,b1)=chi(a2,b2). "
                        + "The proof supplies (0,1) and (1,1). There are no positivity, "
                        + "coprimality or phase-quotient hypotheses.")),
                    Paragraph(Text("Write f(n)=F(0,1,n) and g(n)=F(1,1,n). The recurrence "
                        + "gives g(n)=f(n+1). A scalar period t of g fixes f(t+1) and f(t+2) "
                        + "modulo p; subtraction in the recurrence fixes f(t)=f(0). This "
                        + "recovers the zeroth index and proves equality of all positive "
                        + "scalar-period predicates. The original canonical period-return "
                        + "bridge and finite injective dynamics establish existence, and "
                        + "minimality gives the same least positive period T.")),
                    Paragraph(Text("For each sign separately, let u(n) be its index indicator. "
                        + "The endpoint equality u(T)=u(0) makes the sum of u(n+1) over n<T "
                        + "equal the sum of u(n) over n<T, by cancelling the two expansions "
                        + "of the sum over n<T+1. This accounts for wraparound, repeated "
                        + "values and the zero class, with no T>1 premise. Equal integer "
                        + "balances for every same odd prime imply equality of the complete sets.")),
                    Paragraph(Text("The source is Definitions 2.6 and 2.7 and Section 5, "
                        + "Question 5.3 of the cited preprint and journal article. The proof "
                        + "settles this existential question; it supplies no distribution "
                        + "or infinitude assertion for primes with a prescribed balance."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("andoyo-2026-pisano-question-5-3"), ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string name, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
