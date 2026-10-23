using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PrimeFactorSubtractionValueFinitenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive integer value of the prime-factor subtraction difference occurs at only finitely many indices.",
        H("Positive values of A399155 have finite fibers"),
        Blocks(
            Paragraph(Text(
                "The proof uses the prior smallest-factor formula from OEIS A175126 and largest-factor "
                + "bound from OEIS A309892. The repository's existing A399155 triage distinguishes their "
                + "comparison consequence from the separate positive-value fiber-finiteness observation.")),
            Describe.Lean(
                DescribeId.Create("prime-factor-subtraction-smallest-steps"),
                DeclarationHandle.Create(Prefix + "stepsSmallest"),
                H("Smallest-factor walk"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The step count is zero below two. At every other natural value n, subtract n.minFac "
                    + "and add one to the step count of the resulting value. A prime divisor also divides "
                    + "the value after its subtraction, so a walk beginning at least two never visits one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-subtraction-largest-steps"),
                DeclarationHandle.Create(Prefix + "stepsLargest"),
                H("Largest-factor walk"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The step count is zero below two. At every other natural value n, subtract its "
                    + "largest prime factor and add one to the step count of the resulting value. "
                    + "The largest-factor function reuses CenteredReducedResidueProgressions.GreatestPrimeFactor, "
                    + "whose definition is exactly the supremum of n.primeFactors with the identity map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-subtraction-value"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The integer-valued difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sequence value is the smallest-factor step count minus the largest-factor step "
                    + "count, with both counts interpreted as integers. The subtraction is integer "
                    + "subtraction rather than truncated natural subtraction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-subtraction-value-finiteness-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exact finite-fiber assertion"),
                StatementSource.FromAuthor(Finiteness()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive integer v, the natural indices n at least two satisfying a(n)=v "
                    + "form a finite set. The two walk definitions and their integer-valued difference a are defined in this module."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-subtraction-value-finiteness-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Each positive value is attained only finitely often"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a prime index both walks take one step, so their difference is zero. "
                    + "For composite n at least six, the lower estimate is 6a(n)+3sqrt(n)+3 at least n, "
                    + "where sqrt is the natural square root. For every n at least six, three times the "
                    + "largest-factor step count is at most n+1. If its largest factor is at least three, "
                    + "this follows directly from the weighted bound. Otherwise that factor equals two: "
                    + "the smallest prime factor of n/2 is at most two, forcing four to divide n. "
                    + "Then (n-2)/2 is odd and at least three, so an odd prime divisor shows that the "
                    + "largest factor of n-2 is at least three. Charge the first step separately and "
                    + "apply the weighted bound to the remainder. At an odd composite index its smallest "
                    + "factor is at most sqrt(n). The exact smallest-factor counts give the displayed lower "
                    + "bound in both parities. For a positive value v, put t=sqrt(n). The inequalities "
                    + "t squared at most n and n at most 6v+3t+3 give t at most 6v+6 and n at most 24v+21. "
                    + "Prime indices cannot occur, and the small indices satisfy the same final bound, "
                    + "so the fiber is a subset of a finite natural interval."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a399155-value-finiteness"), ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ArithUnits/CenteredReducedResidueProgressions"))]));

    private static Formula Finiteness() => Disp(Seq(
        Forall, Sp, F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("v"), Sp, Implies, Sp,
        Call("Finite", Seq(OpenBrace, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp, Mid, Sp,
            D(2), Sp, Le, Sp, F.Id("n"), Sp, Land, Sp,
            Call("a", F.Id("n")), Sp, Eq, Sp, F.Id("v"), CloseBrace))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
