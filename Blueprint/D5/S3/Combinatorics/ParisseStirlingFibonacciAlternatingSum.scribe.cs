using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ParisseStirlingFibonacciAlternatingSumDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/parisse2024hypersequences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating factorial-Stirling weighted sum of the even-index terms of a "
            + "Fibonacci recurrence equals the signed weighted sum of the preceding Stirling row.",
        H("An Alternating Stirling Identity for Fibonacci and Lucas Numbers"),
        Blocks(
            Node("stirling-row-polynomial", "The Stirling row polynomial", "Q",
                QFormula(),
                "The source writes the Stirling numbers of the second kind for the number of "
                    + "partitions of a set into a prescribed number of nonempty blocks. Collecting "
                    + "a row of them with the factorials as weights gives the polynomial whose "
                    + "coefficient at an index is that index factorial times the Stirling number. "
                    + "The recurrence displayed here is what the Stirling recurrence becomes under "
                    + "that collection: multiplying an index by its coefficient is differentiation "
                    + "followed by multiplication by the variable, and lowering the second argument "
                    + "by one is multiplication by the variable. The polynomial of the zeroth row "
                    + "is the constant one. The polynomial itself is classical: it is the Fubini "
                    + "polynomial, also called the ordered Bell polynomial, whose value at one "
                    + "counts the ordered partitions of a set. What is set up here is its "
                    + "presentation by that differential recurrence, which is the form the later "
                    + "argument uses.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("fibonacci-pairing", "The pairing with a recurrence sequence", "L",
                LFormula(),
                "A polynomial is paired with a sequence by summing each coefficient against the "
                    + "term of the sequence whose index is shifted by a fixed amount. Only the "
                    + "indices carrying a nonzero coefficient contribute, so the sum is finite. "
                    + "When the sequence obeys the Fibonacci recurrence this pairing turns "
                    + "multiplication of the polynomial by the variable into a shift of one, and "
                    + "multiplication by one plus the variable into a shift of two.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("lucas-numbers", "The Lucas numbers", "lucas",
                LucasFormula(),
                "The source writes the Lucas numbers with the values two and one at the first two "
                    + "indices, continuing by the Fibonacci recurrence. They are the second of the "
                    + "two sequences to which the source applies its formula for weighted sums.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alternating-identity-statement", "The two conjectured identities", "claim",
                ClaimFormula(),
                "Section 4 of the source states verbatim: \"For all ell in N zero, the sum over m "
                    + "from zero to ell of minus one to the m times m factorial times the Stirling "
                    + "number of the second kind at ell plus one and m plus one times the Fibonacci "
                    + "number at twice m plus one equals minus one to the ell times the sum over m "
                    + "from zero to ell of m factorial times the Stirling number of the second kind "
                    + "at ell and m times the Fibonacci number at m plus two.\" The second statement "
                    + "is the same with the Lucas numbers in place of the Fibonacci numbers. Both "
                    + "arise as the constant term of the formula the source derives for the weighted "
                    + "sums of powers times Fibonacci and Lucas numbers, after the evaluation of its "
                    + "coefficients at zero. The source names the unsigned right-hand side of the "
                    + "first as the sequence A000557 and the negated right-hand side of the second "
                    + "as A263968; both sequence records carry the factorial-Stirling form, which "
                    + "settles the reading of the stacked bracket symbols.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alternating-identity-proved", "Both identities hold", "result",
                ResultFormula(),
                "Neither identity depends on the first two terms of the sequence, so both follow "
                    + "from one statement about an arbitrary integer sequence obeying the Fibonacci "
                    + "recurrence. Write the Stirling row polynomial for the row at hand. The "
                    + "recurrence for those polynomials yields, by induction, the functional "
                    + "equation asserting that the variable times the polynomial composed with "
                    + "minus one minus the variable equals minus one to the row index times one "
                    + "plus the variable times the polynomial; the induction step differentiates "
                    + "the previous instance and combines it with the composite of the recurrence "
                    + "in a single linear step. The pairing sends one plus the variable raised to a "
                    + "power to the term of the sequence at twice that power plus one, which is the "
                    + "doubling of the index under the binomial transform and again uses only the "
                    + "recurrence. On the other side, the Stirling recurrence rewrites the weight "
                    + "at each index as the sum of two neighbouring coefficients of the row "
                    + "polynomial; reindexing one of the two parts and cancelling the even-index "
                    + "terms against each other collapses the alternating sum to the pairing of the "
                    + "composite polynomial. The boundary term drops out because the row polynomial "
                    + "has no constant term once the row index is at least one, which also lets the "
                    + "variable be factored out and cancelled in the functional equation. What "
                    + "remains is the pairing shifted twice, which is the right-hand side. At row "
                    + "index zero both sides are the term of the sequence at index two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("parisse-stirling-fibonacci-alternating-sum"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula PolynomialRing() =>
        Seq(new Formula.Integers(), OpenBracket, F.Id("X"), CloseBracket);

    private static Formula SequenceType() =>
        new Formula.TypeArrow(Naturals(), new Formula.Integers());

    private static Formula Fib(Formula argument) => Call("fib", argument);

    private static Formula Stirling(Formula row, Formula column) => Call("S", row, column);

    private static Formula Factorial(Formula argument) => Seq(Parenthesized(argument), Bang);

    private static Formula MinusOnePow(Formula exponent) =>
        new Formula.Power(Parenthesized(new Formula.Negate(D(1))), exponent);

    private static Formula SumTo(string index, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(F.Id(index), Eq, D(0)), Caret, Grp(upper), Sp,
            Parenthesized(body));

    private static Formula QFormula()
    {
        var n = F.Id("n");
        var x = F.Id("X");
        var step = Equal(Call("Q", Add(n, D(1))),
            Add(Multiply(Multiply(x, Parenthesized(Add(D(1), x))),
                    Call("derivative", Call("Q", n))),
                Multiply(x, Call("Q", n))));
        return Disp(And(Equal(Call("Q", D(0)), D(1)), Universal("n", Naturals(), step)));
    }

    private static Formula LFormula()
    {
        var u = F.Id("u");
        var c = F.Id("c");
        var p = F.Id("p");
        var k = F.Id("k");
        var body = Seq(F.Sum, Underscore, Grp(k, InMacro, Sp, Call("support", p)), Sp,
            Parenthesized(Multiply(Call("coeff", p, k), Call("u", Add(k, c)))));
        return Disp(Universal("u", SequenceType(),
            Universal("c", Naturals(),
                Universal("p", PolynomialRing(), Equal(Call("L", u, c, p), body)))));
    }

    private static Formula LucasFormula()
    {
        var n = F.Id("n");
        var step = Equal(Call("lucas", Add(n, D(2))),
            Add(Call("lucas", n), Call("lucas", Add(n, D(1)))));
        return Disp(And(Equal(Call("lucas", D(0)), D(2)),
            And(Equal(Call("lucas", D(1)), D(1)), Universal("n", Naturals(), step))));
    }

    private static Formula Identity(Formula term, Formula shifted)
    {
        var l = F.Id("l");
        var m = F.Id("m");
        var left = SumTo("m", l,
            Multiply(Multiply(MinusOnePow(m), Factorial(m)),
                Multiply(Stirling(Add(l, D(1)), Add(m, D(1))), term)));
        var right = Multiply(MinusOnePow(l),
            SumTo("m", l, Multiply(Factorial(m), Multiply(Stirling(l, m), shifted))));
        return Universal("l", Naturals(), Equal(left, right));
    }

    private static Formula ClaimFormula()
    {
        var m = F.Id("m");
        var even = Add(Multiply(D(2), m), D(2));
        var plain = Add(m, D(2));
        var fibonacci = Identity(Fib(even), Fib(plain));
        var lucasPart = Identity(Call("lucas", even), Call("lucas", plain));
        return Disp(Iff(F.Id("claim"), And(fibonacci, lucasPart)));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
