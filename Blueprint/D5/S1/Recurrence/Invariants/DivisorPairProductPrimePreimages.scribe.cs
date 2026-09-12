using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class DivisorPairProductPrimePreimagesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/seidov2006a119623");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime values of the second elementary symmetric divisor function have exactly two preimages when attained at composites.",
        H("Prime Divisor-Pair Sums and Their Preimages"),
        Blocks(
            Paragraph(Text(
                "All variables range over the natural numbers. The function S2 sums the "
                + "products of unordered pairs of distinct positive divisors.")),
            Node("S2", "The second elementary symmetric divisor function", DefinitionFormula(),
                "For each n, S2(n) is the sum of d times e over positive divisors d and e "
                + "of n with d less than e.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("eq_two_mul_prime_of_composite_of_s2_prime",
                "Classification of composite prime-value arguments", ClassificationFormula(),
                "The divisor-sum identity separates repeated prime factors from squarefree "
                + "arguments. A repeated prime factor produces a common factor of the first "
                + "and second power sums, while parity excludes squarefree arguments with at "
                + "least two odd prime factors. The remaining composite is twice an odd prime.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("seidov_conjecture", "Seidov's exact two-preimage conjecture",
                ConjectureFormula(),
                "For a composite n whose S2 value is prime, the equality S2(m)=S2(n) holds "
                + "exactly when m is n or the prime S2(n). The classification above reduces "
                + "composite arguments to twice an odd prime. The evaluations S2(p)=p and "
                + "S2(2q)=2q^2+9q+2, together with strict increase of the latter expression, "
                + "separate all remaining cases, including m equal to zero or one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a119623-divisor-pair-product-prime-preimages"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("seidov-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var e = F.Id("e");
        var indices = Seq(d, Sp, Mid, Sp, n, Comma, Sp, e, Sp, Mid, Sp, n,
            Comma, Sp, d, Sp, Lt, Sp, e);
        var sum = Seq(Sum, Underscore, Grp(indices), Sp, Multiply(d, e));
        return Universal(n, Equal(S2(n), sum));
    }

    private static Formula ClassificationFormula()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        var conclusion = Seq(
            Exists, Sp, q, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Prime(q), Sp, Land, Sp, Odd(q), Sp, Land, Sp,
            Equal(n, Multiply(D(2), q)));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Neg, Sp, Prime(n), Sp, Implies, Sp,
                D(1), Sp, Lt, Sp, n, Sp, Implies, Sp,
                Prime(S2(n)), Sp, Implies, Sp),
            conclusion
        ]));
    }

    private static Formula ConjectureFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var alternatives = Parenthesized(Seq(
            Equal(m, n), Sp, Lor, Sp, Equal(m, S2(n))));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Neg, Sp, Prime(n), Sp, Implies, Sp,
                D(1), Sp, Lt, Sp, n, Sp, Implies, Sp,
                Prime(S2(n)), Sp, Implies, Sp),
            Seq(Forall, Sp, m, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                Equal(S2(m), S2(n)), Sp, Iff, Sp, alternatives)
        ]));
    }

    private static Formula S2(Formula value) =>
        new Formula.Apply(new Formula.Subscript(F.Id("S"), D(2)), [value]);
    private static Formula Prime(Formula value) => Call("Prime", value);
    private static Formula Odd(Formula value) => Call("Odd", value);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(Formula variable, Formula body) => Disp(Seq(
        Forall, Sp, variable, Sp, InMacro, Sp, Naturals(), Comma, Sp, body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.Add(Comma);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
