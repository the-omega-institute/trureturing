using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class OhScrimshawQMotzkinHankelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/oh2018identities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At n = 3 the two-shifted Hankel determinant of Cigler's q-Motzkin numbers takes the value 3 at q = 1, while the printed factor f_3 takes the value 2, so no power of q times f_3 equals the determinant.",
        H("Oh and Scrimshaw's two-shifted q-Motzkin conjecture is false as printed"),
        Blocks(
            Node("q-motzkin", "Cigler's q-Motzkin numbers", MotzkinFormula(),
                "The recursion of the source over any commutative ring with parameter q: M(0) = 1 and M(n + 1) = M(n) + sum over k < n of q^(k+1) M(k) M(n - k - 1). The conjecture uses the polynomial ring Z[q] with q the variable.",
                "qMotzkin", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printed-factor", "The printed factor", FactorFormula(),
                "For n divisible by three the source sums q^k over 1 <= k <= n with k not congruent to 1 modulo 3; otherwise it multiplies q + 1 by the sum of q^(3k) over k <= floor(n/3). NatMod and NatDiv are the natural remainder and quotient.",
                "fPrinted", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hankel", "The two-shifted Hankel determinant", HankelFormula(),
                "The determinant of the n x n matrix with entries M(i + j + 2) for 0 <= i, j < n.",
                "hankelTwoShifted", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The printed conjecture", ClaimDefinitionFormula(),
                "For every n >= 1 some natural power of q times f_n equals the determinant in Z[q]. Only the first of the two conjectures that share the label conj:factored_motzkin_2shifted is stated.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The counterexample n = 3", Disp(new Formula.Not(F.Id("claim"))),
                "Evaluation at q = 1 is a ring homomorphism from Z[q] to Z, so it commutes with the determinant and with the recursion. At q = 1 the recursion gives the Motzkin numbers 1, 1, 2, 4, 9, 21, 51, and the determinant becomes det[[2, 4, 9], [4, 9, 21], [9, 21, 51]] = 3. The printed side becomes 1^c f_3(1), and f_3 = q^2 + q^3 gives 2. So the identity fails at n = 3 for every c.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("oh-scrimshaw-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp, body);

    private static Formula MotzkinFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n"), k = F.Id("k");
        Formula zero = Equal(Call("qMotzkin", q, D(0)), D(1));
        Formula term = Times(Times(Power(q, Add(k, D(1))), Call("qMotzkin", q, k)),
            Call("qMotzkin", q, Subtract(Subtract(n, k), D(1))));
        Formula step = All("n", Naturals(), Equal(Call("qMotzkin", q, Add(n, D(1))),
            Add(Call("qMotzkin", q, n), SumOver("k", Fin(n), term))));
        return Disp(new Formula.Logic(Parenthesized(zero), FormulaLogicOperator.And, Parenthesized(step)));
    }

    private static Formula FactorFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n"), k = F.Id("k");
        Formula indices = Seq(OpenBrace, new Formula.Relation(k, FormulaRelationOperator.MemberOf,
            Call("Finset.Icc", D(1), n)), Sp, Mid, Sp,
            new Formula.Relation(Call("NatMod", k, D(3)), FormulaRelationOperator.NotEqual, D(1)), CloseBrace);
        Formula first = SumOver("k", indices, Power(q, k));
        Formula second = Times(Parenthesized(Add(q, D(1))),
            SumOver("k", Call("Finset.range", Add(Call("NatDiv", n, D(3)), D(1))), Power(q, Times(D(3), k))));
        Formula value = Call("ite", Equal(Call("NatMod", n, D(3)), D(0)), first, second);
        return Disp(All("n", Naturals(), Equal(Call("fPrinted", q, n), value)));
    }

    private static Formula HankelFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula entries = new Formula.Subscript(
            Seq(OpenBracket, Call("qMotzkin", q, Add(Add(i, j), D(2))), CloseBracket),
            Seq(i, Comma, Sp, j, Sp, InMacro, Sp, Fin(n)));
        return Disp(All("n", Naturals(), Equal(Call("hankelTwoShifted", q, n), Call("det", entries))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), c = F.Id("c"), x = F.Id("X");
        return All("n", Naturals(), Implies(AtMost(D(1), n), Some("c", Naturals(),
            Equal(Call("hankelTwoShifted", x, n), Times(Power(x, c), Call("fPrinted", x, n))))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
