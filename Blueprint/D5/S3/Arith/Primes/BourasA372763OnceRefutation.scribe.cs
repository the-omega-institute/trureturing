using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class BourasA372763OnceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/BourasA372763OnceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/bouras2024a372763");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime 11 occurs at indices 10 and 21 in OEIS A372763.",
        H("Bouras's unique prime occurrence conjecture is false"),
        Blocks(
            Node("nested", "The inner continued fraction", NestedFormula(),
                "The right fold evaluates k - (k+1)/t for k = 2 through n-1, starting from x. "
                + "All divisions in this expression are rational divisions. The subtraction n-2 "
                + "in List.range' is truncated natural subtraction. For n at least three, this is "
                + "the inner expression in OEIS A372763, NAME (unpaginated): "
                + "\"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5))))).\"",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("K", "The reciprocal of the inner expression", ReciprocalFormula(),
                "K takes the reciprocal of nested, with terminal rational value x. "
                + "The rational operations are total, including division by zero; the two fractions "
                + "used below have nonzero tails. OEIS A372763, NAME (unpaginated): "
                + "\"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5))))).\"",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The denominator sequence", SequenceFormula(),
                "OEIS A372763, NAME (unpaginated): "
                + "\"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5))))).\" "
                + "Rat.den is the positive denominator of the reduced rational number. "
                + "The entry has offset three; the terminal value is the rational number n+5.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A372763, COMMENTS (unpaginated): "
                + "\"Conjecture 2: Except for 2 and 3, all primes appear in the sequence once.\" "
                + "The prime p ranges over the natural numbers. A unique occurrence means exactly "
                + "one natural index n at least three with a(n)=p.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The repeated prime 11", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Exact rational evaluation gives a(10)=11 and a(21)=11. The natural number 11 is prime "
                + "and differs from 2 and 3. Both indices are at least three and are unequal, "
                + "so the asserted uniqueness fails. The repeated value already appears in the "
                + "published OEIS data. This refutation does not assert an upper bound on its "
                + "global number of occurrences or resolve Conjecture 1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bouras372763-once"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("bouras-a372763-once-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Rat));
    private static Formula Imp(Formula premise, Formula conclusion) => new Formula.Logic(
        premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula NestedFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var k = F.Id("k");
        var t = F.Id("t");
        var step = Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(k, Sp, Colon, Sp, Nat)), Sp,
            Parenthesized(Seq(t, Sp, Colon, Sp, Rat)), Sp, Mapsto, Sp,
            Subtract(Cast(k), new Formula.Fraction(Add(Cast(k), D(1)), t))));
        var range = Parenthesized(App(Seq(Qualified("List", "range"), Apos),
            D(2), Parenthesized(Subtract(n, D(2)))));
        return Disp(All("n", Nat, All("x", Rat, Equal(Call("nested", n, x),
            App(Qualified("List", "foldr"), step, x, range)))));
    }

    private static Formula ReciprocalFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        return Disp(All("n", Nat, All("x", Rat, Equal(Call("K", n, x),
            new Formula.Fraction(D(1), Call("nested", n, x))))));
    }

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Nat, Equal(Call("a", n),
            App(Qualified("Rat", "den"),
                Parenthesized(Call("K", n, Parenthesized(Add(Cast(n), D(5)))))))));
    }

    private static Formula ClaimBody()
    {
        var p = F.Id("p");
        var n = F.Id("n");
        var occurrence = new Formula.Logic(
            new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.And, Equal(Call("a", n), p));
        var unique = Seq(Exists, Bang, Sp, Parenthesized(Seq(n, Sp, Colon, Sp, Nat)),
            Comma, Sp, Parenthesized(occurrence));
        return All("p", Nat, Imp(App(Qualified("Nat", "Prime"), p),
            Imp(NotEqual(p, D(2)), Imp(NotEqual(p, D(3)), unique))));
    }
}
