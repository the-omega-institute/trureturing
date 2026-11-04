using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class KimotoWakayamaEvenCongruenceRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/kimotowakayama2022apery");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized even Apéry-like ratio at (p,m,n,s) = (3,5,2,7) fails modulo nine.",
        H("A failure of the even Kimoto–Wakayama congruence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-even"),
                DeclarationHandle.Create(Prefix + "normalizedEven"),
                H("The normalized numbers of even weight"),
                StatementSource.FromAuthor(Disp(NormalizedEvenFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The rational number normalizedEven(s,j) is the normalized Apéry-like "
                        + "number of weight 2s+2 at j. The initial values and recurrence "
                        + "specify it for every natural s and j. The lower-weight term is zero "
                        + "when s=0, so the weight-zero row is identically zero. Subtraction in "
                        + "the indices is natural subtraction; the recurrence is used only for "
                        + "j at least two. Section 3.4 of Kimoto and Wakayama gives the recurrence "
                        + "and initial values (arXiv v2 TeX, lines 1431–1470, especially "
                        + "1446–1448 and 1450–1466)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rational-congruence"),
                DeclarationHandle.Create(Prefix + "RatCongr"),
                H("Congruence of rational numbers"),
                StatementSource.FromAuthor(Disp(RatCongrFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "RatCongr(p,n,x,y) means that x−y is p to the power n times a rational "
                        + "number admitting an integer denominator indivisible by p. Its "
                        + "definition uses integer a and b, with no primality assumption on p. "
                        + "For prime p the condition on b also makes b nonzero, so multiplying "
                        + "by b gives precisely congruence in the localization of the integers "
                        + "away from p. This is the meaning of rational congruence in the "
                        + "even assertion of Conjecture 3.6 (arXiv v2 TeX, lines 1608–1617). "
                        + "The casts of p to an integer and of p, a and b to rational numbers "
                        + "are shown explicitly."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The even assertion restricted to odd primes"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimProposition()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 3.6 gives the following even assertion (arXiv v2 TeX, "
                            + "lines 1608–1617): “For positive integers "),
                        Math(Seq(X("m"), Comma, X("n"), Comma, X("s"))),
                        Text(" such that "),
                        Math(AtLeast(Multiply(X("m"), X("p")), X("s"))),
                        Text(" and "),
                        Math(AtLeast(Multiply(X("m"), Power(X("p"),
                            Subtract(X("n"), D(1)))), X("s"))),
                        Text(", we have")),
                    new DocumentBlock.DisplayFormula(SourceEvenAssertion()),
                    Paragraph(Text(
                        "” Here claim quantifies only over odd primes p, expressed by "
                            + "Nat.Prime p and p≠2. It is therefore a weaker assertion than "
                            + "the source assertion allowing all primes, and its failure "
                            + "also refutes that assertion. The source subsequently assumes "
                            + "odd primes in the subsection (TeX line 1635). The two "
                            + "conclusions are congruence of the displayed ratios and "
                            + "noncongruence of the right ratio to zero. All divisions are "
                            + "rational divisions, including the total value zero for division "
                            + "by zero; no additional nonzero-denominator hypothesis is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The assertion fails at p=3, m=5, n=2, s=7"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimProposition())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Compute the eight entries with weight indices zero through seven "
                            + "by keeping two consecutive rows. Before the row at j=0, the "
                            + "previous row is zero; the row at zero is (1,0,0,0,0,0,0,0), "
                            + "and the row at one is (3/4,1,0,0,0,0,0,0). Each later row uses "
                            + "the recurrence, including the preceding row's entry of one "
                            + "lower weight. Continuing through j=45 gives the entries at "
                            + "j=15 and j=45 for weight sixteen. In particular, "
                            + "normalizedEven(7,15) = 7333120509469805428121 / "
                            + "355769406331851217305600000.")),
                    Paragraph(Text(
                        "These exact values give the left ratio "
                            + "L = 3²⁸ normalizedEven(7,45) / (3¹⁴ normalizedEven(7,15)) "
                            + "as P/Q, where P = "
                            + "102790658465770739117540100122976721847176041588902154700374527298060572494857673559242663743632025784157718049052857 "
                            + "and Q = "
                            + "248060981949704625896344570711464099546609864372154310051109270678757921001761367078238673489100800000000000. "
                            + "The right ratio is 3¹⁴ normalizedEven(7,15) divided by itself. "
                            + "Its denominator is nonzero by the value at fifteen, so it equals one.")),
                    Paragraph(Text(
                        "If RatCongr(3,2,P/Q,1) held, there would be integers a and b "
                            + "with 3 not dividing b and (P/Q−1)b=9a. Subtracting one and "
                            + "clearing the nonzero integer Q gives (P−Q)b=9aQ as an integer "
                            + "equality. Taking remainders modulo nine uses P−Q≡3 and forces "
                            + "3b≡0 modulo nine. Thus 3 divides b, a contradiction.")),
                    Paragraph(Text(
                        "Finally, three is an odd prime, m=5, n=2 and s=7 are positive, "
                            + "and both required bounds reduce to 7≤15. If claim held, its "
                            + "congruence conclusion at these parameters would be "
                            + "RatCongr(3,2,L,1), contrary to the preceding calculation. "
                            + "The congruence conclusion alone already fails; the assertion "
                            + "about odd weights and any corrected even congruence are not "
                            + "conclusions of this argument."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kimoto-wakayama-2019-even-normalized-apery-congruence"),
                    ResolutionKind.Refuted)))));

    private static Formula NormalizedEvenFormula()
    {
        var s = X("s");
        var j = X("j");
        var previous = Subtract(j, D(1));
        var coefficient = Add(Subtract(Multiply(D(8), Power(NatToRat(j), D(2))),
            Multiply(D(8), NatToRat(j))), D(3));
        var numerator = Add(
            Subtract(Multiply(Parenthesized(coefficient), Normalized(s, previous)),
                Multiply(Multiply(D(4), Power(NatToRat(previous), D(2))),
                    Normalized(s, Subtract(j, D(2))))),
            Multiply(D(4), If(Equal(s, D(0)), Typed(D(0), Rationals()),
                Normalized(Subtract(s, D(1)), previous))));
        var recurrence = Arrow(AtMost(D(2), j),
            Equal(Typed(Normalized(s, j), Rationals()),
                Fraction(numerator, Multiply(D(4), Power(NatToRat(j), D(2))))));
        return All("s", Naturals(), Conjunction(
            Equal(Typed(Normalized(s, D(0)), Rationals()),
                If(Equal(s, D(0)), Typed(D(1), Rationals()), Typed(D(0), Rationals()))),
            Conjunction(
                Equal(Typed(Normalized(s, D(1)), Rationals()),
                    If(Equal(s, D(0)), Fraction(Typed(D(3), Rationals()), Typed(D(4), Rationals())),
                        If(Equal(s, D(1)), Typed(D(1), Rationals()), Typed(D(0), Rationals())))),
                All("j", Naturals(), recurrence))));
    }

    private static Formula RatCongrFormula()
    {
        var p = X("p");
        var n = X("n");
        var x = X("x");
        var y = X("y");
        var a = X("a");
        var b = X("b");
        return All("p", Naturals(), All("n", Naturals(),
            All("x", Rationals(), All("y", Rationals(),
                Equivalence(Congruent(p, n, x, y),
                    Some("a", Integers(), Some("b", Integers(),
                        Conjunction(new Formula.Not(Parenthesized(Divides(NatToInt(p), b))),
                            Equal(Multiply(Parenthesized(Subtract(x, y)), IntToRat(b)),
                                Multiply(Power(NatToRat(p), n), IntToRat(a)))))))))));
    }

    private static Formula ClaimProposition()
    {
        var p = X("p");
        var m = X("m");
        var n = X("n");
        var s = X("s");
        var denominator = Multiply(Power(NatToRat(p), Multiply(D(2), s)),
            Normalized(s, Multiply(m, p)));
        Formula Ratio(Formula exponent) => Fraction(
            Multiply(Power(NatToRat(p), Multiply(Multiply(D(2), s), exponent)),
                Normalized(s, Multiply(m, Power(p, exponent)))), denominator);
        var right = Ratio(Subtract(n, D(1)));
        var conclusion = Conjunction(Congruent(p, n, Ratio(n), right),
            new Formula.Not(Parenthesized(Congruent(p, n, right, Typed(D(0), Rationals())))));
        return All("p", Naturals(), Arrow(At(Qualified("Nat", "Prime"), p),
            Arrow(NotEqual(p, D(2)), All("m", Naturals(), All("n", Naturals(),
                All("s", Naturals(), Arrow(LessThan(D(0), m), Arrow(LessThan(D(0), n),
                    Arrow(LessThan(D(0), s), Arrow(AtMost(s, Multiply(m, p)),
                        Arrow(AtMost(s, Multiply(m, Power(p, Subtract(n, D(1))))),
                            conclusion)))))))))));
    }

    private static Formula SourceEvenAssertion()
    {
        var p = X("p");
        var m = X("m");
        var n = X("n");
        var s = X("s");
        var weight = Add(Multiply(D(2), s), D(2));
        Formula Number(Formula index) => At(new Formula.Subscript(
            Seq(Widetilde, Grp(X("J"))), weight), index);
        var denominator = Multiply(Power(p, Multiply(D(2), s)), Number(Multiply(m, p)));
        Formula Ratio(Formula exponent) => Fraction(
            Multiply(Power(p, Multiply(Multiply(D(2), s), exponent)),
                Number(Multiply(m, Power(p, exponent)))), denominator);
        return Seq(Ratio(n), Sp, Equiv, Sp, Ratio(Subtract(n, D(1))), Sp,
            Parenthesized(Seq(Neg, Equiv, D(0))), Sp,
            Pmod, Grp(Power(p, n)));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Arith", "Congruence",
        "KimotoWakayamaEvenCongruenceRefutation", name);
    private static Formula Normalized(Formula s, Formula j) => At(Local("normalizedEven"), s, j);
    private static Formula Congruent(Formula p, Formula n, Formula x, Formula y) =>
        At(Local("RatCongr"), p, n, x, y);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(X("Q")));
    private static Formula NatToRat(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Rationals());
    private static Formula NatToInt(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Integers());
    private static Formula IntToRat(Formula value) => Typed(At(Qualified("Int", "cast"), value), Rationals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula AtLeast(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
