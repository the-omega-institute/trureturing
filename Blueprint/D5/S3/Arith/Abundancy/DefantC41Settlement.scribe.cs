using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class DefantC41SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/DefantC41Settlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/defant2014abundancy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational prime 3 has a 2-powerful friend in Defant's ring of radicand −11.",
        H("Defant's Conjecture 4.1"),
        Blocks(
            Definition("defant-radicands", "Radicands", "K", Radicands(),
                "Defant restricts the conjecture to these nine negative radicands."),
            Definition("defant-ring", "Quadratic integer ring", "R", Ring(),
                "In the integral basis, the generator is the square root of d when d is "
                    + "2 or 3 modulo 4, and half the sum of one and that root when d is "
                    + "1 modulo 4. The two parameters a and b encode the equation "
                    + "for the square of the generator as a plus b times the generator. "
                    + "The remainder and division in the parameters are integer operations."),
            Definition("defant-nonzero", "Nonzero elements", "Nonzero", NonzeroElements(),
                "The divisor sum, index, and friendship are defined on nonzero ring elements."),
            Definition("defant-absolute-value", "Absolute value", "absoluteValue", AbsoluteValue(),
                "The norm is the integer obtained by multiplying an element by its conjugate. "
                    + "The absolute value is its real square root."),
            Definition("defant-sector", "Half-open sector", "A", Sector(),
                "The real and imaginary projections here are integral coordinates. "
                    + "The coordinate tests give arguments in [0, π/2) for d = −1, "
                    + "[0, π/3) for d = −3, and [0, π) otherwise."),
            Definition("defant-delta", "Power sum of sector divisors", "delta", DivisorSum(),
                "Definition 2.1 permits integer exponents. The terms range over the ring, "
                    + "with zero weight outside the actual divisors in the half-open sector. "
                    + "The positive definite multiplicative norm bounds the coordinates of "
                    + "these divisors by the norm of the input, so the sum has finite support."),
            Definition("defant-index", "Normalized abundancy index", "I", Index(),
                "Definition 2.2 uses positive natural exponents. The numerator casts n to "
                    + "an integer exponent and the denominator uses its natural power."),
            Definition("defant-friendship", "Powerful friendship", "PowerfullyFriendly",
                Friendship(),
                "Two nonzero inputs are n-powerfully friendly when the normalized indices "
                    + "agree and the absolute values differ."),
            Definition("defant-prime-power", "Rational prime power", "primePower", PrimePower(),
                "Take the natural power and cast it into the quadratic ring. Primality of p "
                    + "implies the power is nonzero, giving the subtype witness."),
            Definition("defant-conjecture", "Conjecture 4.1", "claim",
                Equal(F.Id("claim"), Parenthesized(Conjecture())),
                "In every listed ring, for every positive rational prime and both positive "
                    + "exponents, the conjecture denies friendship with every nonzero element."),
            Describe.Lean(
                DescribeId.Create("defant-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A rational prime with a powerful friend"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Parenthesized(Conjecture())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For d = −11 the integral basis generator π satisfies π² = π − 3. "
                    + "Take p = 3, k = 1, n = 2, and the challenger 7π − 3. "
                    + "The squared absolute values are 9 and 135. A sector element divides "
                    + "an input exactly when its norm divides both integral coordinates "
                    + "of the input times its conjugate. The norm bound confines both "
                    + "divisor sets to coordinates −15 through 11 and 0 through 7. "
                    + "The complete divisor sets in that box give sums of 16 and 240, "
                    + "so both indices equal 16/9 and the absolute values differ."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Radicands() => Equal(F.Id("K"), new Formula.SetLiteral(
        [Negative(D(1, 6, 3)), Negative(D(6, 7)), Negative(D(4, 3)), Negative(D(1, 9)),
         Negative(D(1, 1)), Negative(D(7)), Negative(D(3)), Negative(D(2)), Negative(D(1))]));

    private static Formula Ring()
    {
        var d = F.Id("d");
        var condition = Equal(new Formula.Modulo(d, D(4)), D(1));
        var a = Conditional(condition, Seq(Parenthesized(Seq(d, Minus, D(1))), Slash, D(4)), d);
        var b = Conditional(condition, D(1), D(0));
        return Equal(Call("R", d), Call("QuadraticAlgebra", NumberDomain("Z"), a, b));
    }

    private static Formula NonzeroElements()
    {
        var d = F.Id("d");
        var z = F.Id("z");
        return Equal(Call("Nonzero", d), Seq(
            OpenBrace, Typed(z, Call("R", d)), Sp, Mid, Sp, Different(z, D(0)), CloseBrace));
    }

    private static Formula AbsoluteValue()
    {
        var z = F.Id("z");
        return Equal(Call("absoluteValue", z),
            Seq(Sqrt, Grp(Cast(Qualified("QuadraticAlgebra", "norm", z), NumberDomain("R")))));
    }

    private static Formula Sector()
    {
        var d = F.Id("d");
        var z = F.Id("z");
        var real = Field(z, "re");
        var imag = Field(z, "im");
        var condition = Logic(Equal(d, Negative(D(1))), FormulaLogicOperator.Or,
            Equal(d, Negative(D(3))));
        var first = Logic(Less(D(0), real), FormulaLogicOperator.And,
            Relation(D(0), FormulaRelationOperator.LessThanOrEqual, imag));
        var boundary = Logic(Equal(imag, D(0)), FormulaLogicOperator.And, Less(D(0), real));
        var second = Logic(Less(D(0), imag), FormulaLogicOperator.Or, boundary);
        return Equal(Call("A", d),
            Seq(OpenBrace, z, Sp, Mid, Sp, Conditional(condition, first, second), CloseBrace));
    }

    private static Formula DivisorSum()
    {
        var d = F.Id("d");
        var x = F.Id("x");
        var z = F.Id("z");
        var divides = Relation(x, FormulaRelationOperator.Divides, Field(z, "val"));
        var sector = Relation(x, FormulaRelationOperator.MemberOf, Call("A", d));
        var summand = Conditional(Logic(divides, FormulaLogicOperator.And, sector),
            Power(Call("absoluteValue", x), F.Id("n")), D(0));
        var sum = Seq(Sum, Caret, Grp(Operator("f")), Underscore,
            Grp(Typed(x, Call("R", d))), Sp, summand);
        return Equal(Typed(Call("delta", F.Id("n"), z), NumberDomain("R")), sum);
    }

    private static Formula Index()
    {
        var z = F.Id("z");
        var n = F.Id("n");
        return Equal(Call("I", n, z), new Formula.Fraction(
            Call("delta", Cast(n, NumberDomain("Z")), z),
            Power(Call("absoluteValue", Field(z, "val")), n)));
    }

    private static Formula Friendship()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        var w = F.Id("w");
        var index = Equal(Call("I", n, z), Call("I", n, w));
        var magnitude = Different(Call("absoluteValue", Field(z, "val")),
            Call("absoluteValue", Field(w, "val")));
        return Logic(Call("PowerfullyFriendly", n, z, w), FormulaLogicOperator.Iff,
            Logic(index, FormulaLogicOperator.And, magnitude));
    }

    private static Formula PrimePower()
    {
        var d = F.Id("d");
        var p = F.Id("p");
        var k = F.Id("k");
        return Equal(Field(Call("primePower", d, p, k, F.Id("hp")), "val"),
            Cast(Cast(Power(p, k), NumberDomain("N")), Call("R", d)));
    }

    private static Formula Conjecture()
    {
        var d = F.Id("d");
        var p = F.Id("p");
        var k = F.Id("k");
        var n = F.Id("n");
        var z = F.Id("z");
        var natural = NumberDomain("N");
        var prime = Qualified("Nat", "Prime", p);
        var power = Call("primePower", d, p, k, F.Id("hp"));
        var solitude = Universal("z", Call("Nonzero", d),
            Seq(Neg, Call("PowerfullyFriendly", n, power, z)));
        var positiveIndex = Universal("n", natural,
            Logic(Less(D(0), n), FormulaLogicOperator.Implies, solitude));
        var primePowers = Seq(Forall, Sp, Parenthesized(Typed(p, natural)), Sp,
            Parenthesized(Typed(F.Id("hp"), prime)), Sp,
            Parenthesized(Typed(k, natural)), Comma, Sp,
            Logic(Less(D(0), k), FormulaLogicOperator.Implies, positiveIndex));
        return Universal("d", NumberDomain("Z"),
            Logic(Relation(d, FormulaRelationOperator.MemberOf, F.Id("K")),
                FormulaLogicOperator.Implies, primePowers));
    }

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Operator("if"), Sp, condition, Sp,
            Operator("then"), Sp, yes, Sp, Operator("else"), Sp, no));

    private static Formula Operator(string name) => Seq(Mathrm, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(owner), Dot, F.Id(name)), [.. arguments]);

    private static Formula Field(Formula value, string name) =>
        Seq(value, Dot, F.Id(name));

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Different(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Cast(Formula value, Formula domain) =>
        Parenthesized(Typed(value, domain));

    private static Formula Typed(Formula value, Formula domain) =>
        Seq(value, Colon, Sp, domain);

    private static Formula NumberDomain(string name) => Seq(Mathbb, Grp(F.Id(name)));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Negative(Formula value) => Seq(Minus, value);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
