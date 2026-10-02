using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class LogLaplacianBellNonvanishingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/LogLaplacianBellNonvanishing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/rosenzweig2026loglaplacian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Bell polynomial values in Rosenzweig and Stanfill's Open Problem 1.3 are nonzero at every positive natural index.",
        H("Nonvanishing Bell values for the logarithmic Laplacian"),
        Blocks(
            Node("BellProfile", "Natural Bell profiles", ProfileFormula(),
                "BellProfile is the subtype of natural-valued functions with exactly the two source constraints. The zero-based index i corresponds to the source index i+1. The subtraction n-k is truncated natural subtraction, Nat.sub n k; Fin(L) is the type of natural indices smaller than L and val(i) is its natural value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bellOrdinary", "The partial ordinary Bell polynomial", BellFormula(),
                "This is the defining sum (1.20), with rational coefficients. The function val(r) is the underlying natural sequence of the subtype r; every factorial is formed in N before the displayed cast to Q. Each entry is at most k, so these profiles form a finite type.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pBell", "The polynomial of Definition 1.1", PolynomialFormula(),
                "pBell uses the first expression of (1.5), with n representing j, s a rational sequence and t rational. The determinant expression is not used; the displayed sum includes both endpoints k=0 and k=n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S1", "The sequence of equation (1.8)", SequenceFormula(),
                "The first expression of (1.8) defines S1, with the exponent 1-k formed in Z and rational division. Mathlib bernoulli has the convention B1=-1/2. The paper uses positive k; the extension to k=0 is zero and never enters a Bell summand.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Open Problem 1.3", Disp(IffFormula(F.Id("claim"), ClaimBody())),
                "The paper's N is the positive naturals, encoded as m:N with 1<=m. pBell, bellOrdinary and S1 are the defining expressions of (1.5), (1.20)-(1.21) and (1.8); m is cast to Q at the evaluation point. Thus claim is the universal nonvanishing assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Nonvanishing at every positive index", Disp(ClaimBody()),
                "Put a=(2m-1)/2 and b_r=24^r a S1(2r). The von Staudt-Clausen theorem gives "
                    + "v2(B_{2r})=-1, hence v2(b_r)=r-1-v2(r)>=0 for r>=1 and v2(b_1)=0. "
                    + "Odd-index coefficients vanish. After multiplying the Bell value by 24^m m!, "
                    + "a nonzero profile contributes (m!/product j_i!) product b_{i/2}^{j_i}. "
                    + "A positive count at an index i>=4 gives strictly positive valuation, "
                    + "using v2((2j)!)=v2(j!)+j and product-factorial divisibility. "
                    + "The only remaining profile has j_2=m and all other counts zero; "
                    + "its contribution b_1^m has valuation zero. The ultrametric inequality therefore "
                    + "makes the scaled sum nonzero with valuation zero, proving the assertion. The identity scaled_pBell links the defining Bell sum to the finite-profile sum; scaledEntry_pos_val supplies the strict positive valuation of each nonprincipal even profile.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance, string? declaration = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("rs13-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + (declaration ?? name)), H(title),
            StatementSource.FromAuthor(formula), provenance, Exposition(name, prose), role, resolution);


    private static BlockSequence Exposition(string name, string prose)
    {
        DocumentBlock? quote = name switch
        {
            "BellProfile" => ProfileQuote(),
            "bellOrdinary" => BellQuote(),
            "pBell" => PolynomialQuote(),
            "S1" => SequenceQuote(),
            "claim" => ClaimQuote(),
            _ => null,
        };
        return quote is null ? Blocks(Paragraph(Text(prose))) : Blocks(quote, Paragraph(Text(prose)));
    }

    private static Formula Indexed(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula SourceP(Formula n, Formula s, Formula t) =>
        Seq(Indexed(F.Id("p"), Seq(n, Comma, s)), Parenthesized(t));
    private static Formula SourceB(Formula n, Formula k) =>
        Indexed(Seq(Widehat, Grp(F.Id("B"))), Seq(n, Comma, k));
    private static Formula SourceJ(Formula i) => Indexed(F.Id("j"), i);
    private static Formula SourceZ(Formula i) => Indexed(F.Id("z"), i);
    private static Formula SourceLength() => Add(Sub(F.Id("n"), F.Id("k")), D(1));

    private static DocumentBlock ProfileQuote()
    {
        var length = SourceLength();
        var count = Seq(SourceJ(D(1)), Plus, SourceJ(D(2)), Plus, Seq(Dot, Dot, Dot), Plus, SourceJ(length));
        var weight = Seq(SourceJ(D(1)), Plus, D(2), SourceJ(D(2)), Plus, Seq(Dot, Dot, Dot), Plus,
            Parenthesized(length), SourceJ(length));
        return Paragraph(Text("Section 1.2, page 6: “with the sum being over all sequences "),
            Math(Seq(SourceJ(D(1)), Comma, SourceJ(D(2)), Comma, Seq(Dot, Dot, Dot), Comma, SourceJ(length))),
            Text(" of nonnegative integers such that "),
            Math(Seq(Equal(count, F.Id("k")), Comma, Qquad, Sp, Equal(weight, F.Id("n")))), Text(".”"));
    }

    private static DocumentBlock BellQuote()
    {
        var length = SourceLength();
        var arguments = Seq(SourceZ(D(1)), Comma, SourceZ(D(2)), Comma, Seq(Dot, Dot, Dot), Comma, SourceZ(length));
        var lhs = Seq(SourceB(F.Id("n"), F.Id("k")), Parenthesized(arguments));
        var denominator = Seq(SourceJ(D(1)), Bang, SourceJ(D(2)), Bang, Seq(Dot, Dot, Dot), SourceJ(length), Bang);
        var powers = Seq(SourceZ(D(1)), Caret, Grp(SourceJ(D(1))),
            SourceZ(D(2)), Caret, Grp(SourceJ(D(2))), Seq(Dot, Dot, Dot),
            SourceZ(length), Caret, Grp(SourceJ(length)));
        return Paragraph(Text("Section 1.2, page 6: “"), Math(SourceB(F.Id("n"), F.Id("k"))),
            Text(" denotes the partial ordinary Bell polynomials [4, p. 136] "),
            Math(Equal(lhs, Seq(Sum, Sp, new Formula.Fraction(Seq(F.Id("k"), Bang), denominator), Sp, powers))), Text(",”"));
    }

    private static DocumentBlock PolynomialQuote()
    {
        var j = F.Id("j"); var k = F.Id("k"); var t = F.Id("t"); var sequence = F.Id("S");
        var polynomial = SourceP(j, sequence, t);
        var bell = Seq(SourceB(j, k), Parenthesized(Seq(Indexed(F.Id("s"), D(1)), Comma,
            Seq(Dot, Dot, Dot), Comma, Indexed(F.Id("s"), Add(Sub(j, k), D(1))))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, Eq, D(0))), Caret, Grp(j), Sp,
            new Formula.Fraction(new Formula.Power(Parenthesized(Seq(Minus, D(1))), k), Seq(k, Bang)), Sp,
            bell, Sp, new Formula.Power(t, k));
        var matrix = Seq(Indexed(Seq(Mathcal, Grp(F.Id("N"))), Seq(j, Comma, sequence)), Parenthesized(t));
        var determinant = Seq(new Formula.Fraction(new Formula.Power(Parenthesized(Seq(Minus, D(1))), j), Seq(j, Bang)),
            Sp, F.Id("det"), Sp, matrix);
        return Paragraph(Text("Definition 1.1, page 2: “Given a sequence of numbers, "), Math(sequence),
            Text(", indexed over a set "), Text("J⊇ℕ"),
            Text(", we define "), Math(Seq(polynomial, Colon, Eq, sum, Eq, determinant, Comma, Qquad, Sp,
                j, Sp, InMacro, Sp, Indexed(Nats(), D(0)))), Text(", where "),
            Math(SourceB(F.Id("n"), k)), Text(" denote the partial ordinary Bell polynomials (see Section 1.2) and the "),
            Math(Seq(j, Sp, Times, Sp, j)), Text(" lower Hessenberg matrix "), Math(matrix),
            Text(" consists of "), Math(Seq(Indexed(F.Id("s"), D(1)), Sp, t)), Text(" on the diagonal, "),
            Math(Seq(Parenthesized(Add(k, D(1))), Indexed(F.Id("s"), Add(k, D(1))), Sp, t)),
            Text(" on the "), Math(k), Text("th subdiagonal, the sequence "),
            Math(Seq(D(1), Comma, D(2), Comma, Seq(Dot, Dot, Dot), Comma, Sub(j, D(1)))),
            Text(" on the first superdiagonal, and zeros on all other superdiagonals (cf. [19, Eq. (5.3)]):”"));
    }

    private static DocumentBlock SequenceQuote()
    {
        var k = F.Id("k"); var bk = Indexed(F.Id("B"), k);
        var first = Mul(Parenthesized(Sub(D(1), new Formula.Power(D(2), Sub(D(1), k)))), new Formula.Fraction(Mul(D(2), bk), k));
        var second = Seq(Minus, new Formula.Fraction(D(2), k), Sp, bk, Parenthesized(new Formula.Fraction(D(1), D(2))));
        var entry = Seq(Indexed(F.Id("s"), k), Caret, Grp(Parenthesized(D(1))));
        return Paragraph(Text("Equation (1.8), page 2: “"), Math(Seq(entry, Eq, first, Eq, second,
            Comma, Qquad, Sp, k, Sp, InMacro, Sp, Nats())), Text(".” Section 1.2, page 5: “"), Math(bk),
            Text(" denotes the Bernoulli numbers with the convention "),
            Math(Equal(Indexed(F.Id("B"), D(1)), Seq(Minus, new Formula.Fraction(D(1), D(2))))), Text(";”."));
    }

    private static DocumentBlock ClaimQuote()
    {
        var m = F.Id("m");
        var value = SourceP(Seq(D(2), m), S1(), Sub(new Formula.Fraction(D(1), D(2)), m));
        return Paragraph(Text("Open Problem 1.3, page 2: “Show that "), Math(NotEqual(value, D(0))),
            Text(" for all "), Math(Seq(m, Sp, InMacro, Sp, Nats())), Text(" where the sequence "),
            Math(S1()), Text(" satisfies (1.8).”"));
    }

    private static Formula ProfileFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var r = F.Id("r"); var i = F.Id("i");
        var domain = IndexType(n, k);
        var entry = Call("r", i);
        var count = Equal(SumOver("i", domain, entry), k);
        var weight = Equal(SumOver("i", domain,
            Mul(Parenthesized(Add(Call("val", i), D(1))), entry)), n);
        var profiles = Seq(OpenBrace, r, Sp, Colon, Sp, Arrow(domain, Nats()),
            Sp, Mid, Sp, And(count, weight), CloseBrace);
        return Disp(All("n", Nats(), All("k", Nats(),
            Equal(Call("BellProfile", n, k), profiles))));
    }

    private static Formula BellFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var s = F.Id("s");
        var r = F.Id("r"); var i = F.Id("i"); var domain = IndexType(n, k);
        var entry = new Formula.Apply(Call("val", r), [i]);
        var denominator = ProductOver("i", domain, Cast(Factorial(entry), Rats()));
        var coefficient = new Formula.Fraction(Cast(Factorial(k), Rats()), denominator);
        var powers = ProductOver("i", domain,
            new Formula.Power(Call("s", Add(Call("val", i), D(1))), entry));
        var sum = SumOver("r", Call("BellProfile", n, k), Mul(coefficient, powers));
        return Disp(All("n", Nats(), All("k", Nats(), All("s", Arrow(Nats(), Rats()),
            Equal(Call("bellOrdinary", n, k, s), sum)))));
    }

    private static Formula PolynomialFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var s = F.Id("s"); var t = F.Id("t");
        var coefficient = new Formula.Fraction(
            new Formula.Power(Parenthesized(Seq(Minus, Cast(D(1), Rats()))), k),
            Cast(Factorial(k), Rats()));
        var summand = Mul(Mul(coefficient, Call("bellOrdinary", n, k, s)), new Formula.Power(t, k));
        var boundedSum = Seq(new Formula.Subscript(Sum, Seq(k, Sp, Eq, Sp, D(0))), Caret, Grp(n), Sp, summand);
        return Disp(All("n", Nats(), All("s", Arrow(Nats(), Rats()), All("t", Rats(),
            Equal(Call("pBell", n, s, t), boundedSum)))));
    }

    private static Formula SequenceFormula()
    {
        var k = F.Id("k");
        var exponent = Sub(Cast(D(1), Ints()), Cast(k, Ints()));
        var factor = Parenthesized(Sub(Cast(D(1), Rats()),
            new Formula.Power(Cast(D(2), Rats()), exponent)));
        var numerator = Mul(factor, Parenthesized(Mul(Cast(D(2), Rats()), Call("bernoulli", k))));
        return Disp(All("k", Nats(), Equal(new Formula.Apply(S1(), [k]),
            new Formula.Fraction(numerator, Cast(k, Rats())))));
    }

    private static Formula ClaimBody()
    {
        var m = F.Id("m");
        var point = Sub(new Formula.Fraction(Cast(D(1), Rats()), Cast(D(2), Rats())), Cast(m, Rats()));
        var value = Call("pBell", Mul(D(2), m), S1(), point);
        return All("m", Nats(), new Formula.Logic(Parenthesized(LeqFormula(D(1), m)),
            FormulaLogicOperator.Implies, Parenthesized(NotEqual(value, Cast(D(0), Rats())))));
    }

    private static Formula S1() => new Formula.Subscript(F.Id("S"), D(1));
    private static Formula IndexType(Formula n, Formula k) => Call("Fin", Add(Sub(n, k), D(1)));
    private static Formula SumOver(string index, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(index), Colon, Sp, type)), Sp, body);
    private static Formula ProductOver(string index, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id(index), Colon, Sp, type)), Sp, body);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LeqFormula(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
}
