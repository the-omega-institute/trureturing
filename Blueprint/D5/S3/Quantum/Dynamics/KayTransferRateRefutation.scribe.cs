using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class KayTransferRateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/KayTransferRateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kay2010perfectstatetransferreview");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kay's review of perfect state transfer (arXiv:0903.4274v3, subsection Transfer Rate) conjectures that no set of eigenvalues fulfilling the perfect state transfer condition can make all the sums R_k, k = 0, ..., M - 1, of its rate lemma equal for an integer M > 2, and states that it has a proof only for M > N/2. The conjecture is false: for the eight eigenvalues 0, 31, 46, 65, 88, 107, 122, 153 with transfer time pi and M = 4 = N/2, all four sums equal 194/38984495395755.",
        H("An eight-level perfect state transfer spectrum fulfils Kay's rate condition with M = 4"),
        Blocks(
            Node("spectrum", "The perfect state transfer condition", SpectrumFormula(),
                "The source orders the eigenvalues of the chain as lambda_1 < ... < lambda_N and states the condition \"lambda_n - lambda_{n-1} = (2 m_n + 1) pi / t_0 where t_0 is the state transfer time, and m_n is a positive integer (which can vary with n).\" Here the levels are lam(0), ..., lam(N - 1), the transfer time is t, and m(n) is the multiplier of the gap between the levels n and n + 1. The gaps are positive, so the levels are strictly increasing.",
                "SpectrumCondition", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("derivative", "The derivative of the characteristic product", DerivativeFormula(),
                "The source writes \"B'(lambda_n) = prod_{m = 1, m != n}^N (lambda_n - lambda_m), which is the derivative of the function B(lambda) = prod_{m=1}^N (lambda - lambda_m)\". The product runs over the levels j different from n.",
                "derivativeAt", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("class", "Residue classes of the levels", ClassFormula(),
                "The sum R_k of the source \"is restricted to those terms satisfying the condition (t_0 / pi)(lambda_n - lambda_1) mod M = k\". The level n lies in the class k modulo M when the real number (t / pi)(lam(n) - lam(0)) is an integer z with z mod M = k. Under the perfect state transfer condition this number is the sum of the odd integers 2 m(i) + 1 over the gaps i below n.",
                "InClass", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sum", "The sums of the rate lemma", SumFormula(),
                "The source defines \"R_k = sum_{n=1}^N (-1)^n / B'(lambda_n)\", the sum being restricted to the levels of the residue class k modulo M. The index n of the source starts at one, so the level with the index n in Fin(N) carries the sign (-1)^(val(n) + 1), where val(n) is its position counted from zero.",
                "rateSum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("condition", "The condition of the rate lemma", ConditionFormula(),
                "The lemma of the source states that, for a set of eigenvalues fulfilling the perfect state transfer condition, \"a necessary and sufficient condition to perfectly achieve the rate M / 2 t_0 for integer M is that all the R_k for k = 0 ... M - 1 should be equal\".",
                "RateCondition", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The transfer-rate conjecture", ClaimFormula(),
                "The source states: \"We conjecture that it is impossible to fulfill the condition of Lemma 6 for any M > 2, although we only have a proof for M > N/2.\" The statement quantifies over every number N >= 1 of levels, every set of levels with a transfer time fulfilling the perfect state transfer condition, and every integer M > 2. The empty set of levels is excluded because all its sums are empty and therefore equal.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "Take N = 8, the levels 0, 31, 46, 65, 88, 107, 122, 153 and the transfer time pi. The gaps are 31, 15, 19, 23, 19, 15, 31, that is 2 m + 1 with m = 15, 7, 9, 11, 9, 7, 15, so the perfect state transfer condition holds. The derivatives B'(lambda_n) are -16291106900640, 760363989840, -273136152240, 203460697440, -203460697440, 273136152240, -760363989840, 16291106900640. For M = 4 the residues of the levels are 0, 3, 2, 1, 0, 3, 2, 1, so the classes are {0, 88}, {65, 153}, {46, 122}, {31, 107} for k = 0, 1, 2, 3. Every term (-1)^n / B'(lambda_n) is positive, and each class sum is 1/16291106900640 + 1/203460697440 = 1/203460697440 + 1/16291106900640 = 1/273136152240 + 1/760363989840 = 1/760363989840 + 1/273136152240 = 194/38984495395755. Hence R_0 = R_1 = R_2 = R_3 with M = 4 > 2, and M = N/2 lies outside the range M > N/2 for which the source states a proof.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kay-2010-transfer-rate-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("kayrate-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => Call("Fin", n);

    private static Formula Levels(Formula body)
    {
        Formula big = F.Id("N");
        return All("N", Naturals(), All("lam", Arrow(FinOf(big), Reals()), All("t", Reals(), body)));
    }

    private static Formula SpectrumFormula()
    {
        Formula big = F.Id("N"), lam = F.Id("lam"), t = F.Id("t"), m = F.Id("m"), n = F.Id("n");
        Formula gap = Equal(Sub(App(lam, Add(n, D(1))), App(lam, n)),
            new Formula.Fraction(Mul(Parenthesized(Add(Mul(D(2), App(m, n)), D(1))), Pi), t));
        Formula body = And(Less(D(0), t), Some("m", Arrow(Naturals(), Naturals()),
            All("n", Naturals(), Implies(Less(Add(n, D(1)), big), And(Less(D(0), App(m, n)), gap)))));
        return Disp(Levels(Iff(Call("SpectrumCondition", lam, t), body)));
    }

    private static Formula DerivativeFormula()
    {
        Formula big = F.Id("N"), lam = F.Id("lam"), n = F.Id("n"), j = F.Id("j");
        Formula product = Seq(
            new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, FinOf(big), Comma, Sp, NotEqual(j, n))), Sp,
            Parenthesized(Sub(App(lam, n), App(lam, j))));
        return Disp(All("N", Naturals(), All("lam", Arrow(FinOf(big), Reals()), All("n", FinOf(big),
            Equal(Call("derivativeAt", lam, n), product)))));
    }

    private static Formula ClassFormula()
    {
        Formula big = F.Id("N"), lam = F.Id("lam"), t = F.Id("t"), modulus = F.Id("M"), k = F.Id("k"),
            n = F.Id("n"), z = F.Id("z");
        Formula scaled = Mul(new Formula.Fraction(t, Pi), Parenthesized(Sub(App(lam, n), App(lam, D(0)))));
        Formula body = Some("z", Integers(),
            And(Equal(scaled, z), Equal(new Formula.Modulo(z, modulus), k)));
        return Disp(Levels(All("M", Naturals(), All("k", Naturals(), All("n", FinOf(big),
            Iff(Call("InClass", lam, t, modulus, k, n), body))))));
    }

    private static Formula SumFormula()
    {
        Formula big = F.Id("N"), lam = F.Id("lam"), t = F.Id("t"), modulus = F.Id("M"), k = F.Id("k"),
            n = F.Id("n");
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(D(1))), Add(Call("val", n), D(1)));
        Formula sum = Seq(
            new Formula.Subscript(Sum, Seq(n, Sp, InMacro, Sp, FinOf(big), Comma, Sp,
                Call("InClass", lam, t, modulus, k, n))), Sp,
            new Formula.Fraction(sign, Call("derivativeAt", lam, n)));
        return Disp(Levels(All("M", Naturals(), All("k", Naturals(),
            Equal(Call("rateSum", lam, t, modulus, k), sum)))));
    }

    private static Formula ConditionFormula()
    {
        Formula lam = F.Id("lam"), t = F.Id("t"), modulus = F.Id("M"), k = F.Id("k"), l = F.Id("l");
        Formula body = All("k", Naturals(), Implies(Less(k, modulus),
            All("l", Naturals(), Implies(Less(l, modulus),
                Equal(Call("rateSum", lam, t, modulus, k), Call("rateSum", lam, t, modulus, l))))));
        return Disp(Levels(All("M", Naturals(), Iff(Call("RateCondition", lam, t, modulus), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula big = F.Id("N"), lam = F.Id("lam"), t = F.Id("t"), modulus = F.Id("M");
        Formula body = All("N", Naturals(), Implies(Less(D(0), big),
            All("lam", Arrow(FinOf(big), Reals()), All("t", Reals(),
                Implies(Call("SpectrumCondition", lam, t),
                    All("M", Naturals(), Implies(Less(D(2), modulus),
                        new Formula.Not(Call("RateCondition", lam, t, modulus)))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
