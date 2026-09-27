using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PronkoMotzkinRaisingLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/pronko2025motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the periodic Motzkin spin-1 chain with N at least 2 sites, the operators Sigma^+ and Sigma^-, the sums of the products of local powers s_i^{r_i} with r_1 + ... + r_N equal to 1, respectively -1, commute with the periodic Hamiltonian, send each ground state v_m to a nonzero multiple of v_(m+1), respectively v_(m-1), and annihilate v_N, respectively v_(-N). This proves Conjecture 2 of Pronko.",
        H("Raising and lowering operators of the periodic Motzkin chain"),
        Blocks(
            Node("ht", "Heights of the letters", HtFormula(),
                "The letters u, f, d (basis vectors 0, 1, 2 of C^3) have heights 1, 0 and -1: the steps of a Motzkin path.",
                "ht", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sp", "The spin-1 raising matrix", Disp(Equal(F.Id("sp"), Mat3(0, 1, 0, 0, 0, 1, 0, 0, 0))),
                "The basis vectors 0, 1, 2 of C^3 are u, f and d (up, flat, down); s^+ is the 0/1 matrix of eq. spin1rep.",
                "sp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sm", "The spin-1 lowering matrix", Disp(Equal(F.Id("sm"), Mat3(0, 0, 0, 1, 0, 0, 0, 1, 0))),
                "s^- is the 0/1 matrix of eq. spin1rep.",
                "sm", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spow", "Local powers", SpowFormula(),
                "s^r for r = -2, ..., 2, indexed by k = r + 2: s^0 is the identity, s^{±1} = s^±, s^{±2} = (s^±)^2.",
                "spow", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rv", "Exponents", Disp(Equal(Call("rv", F.Id("r")), Subtract(F.Id("r"), D(2)))),
                "The index r = 0, ..., 4 of the local powers stands for the exponent r - 2 = -2, ..., 2.",
                "rv", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("site", "An operator on one site", SiteFormula(),
                "site(i, A) acts as the 3 x 3 matrix A on the i-th tensor factor and as the identity on the others (eq. spmsz).",
                "site", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sig", "The operators Sigma^+ and Sigma^-", SigFormula(),
                "Sig(N, 1) is Sigma^+ and Sig(N, -1) is Sigma^- of eq. Sigmapmsum: the sum, over the exponent vectors r in {-2, ..., 2}^N with r_1 + ... + r_N = e, of the ordered product s_1^{r_1} ... s_N^{r_N}.",
                "Sig", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("height", "The height S^z of a word", HeightFormula(),
                "The eigenvalue of the third component of the total spin on a basis word: the number of u minus the number of d, with ht(u) = 1, ht(f) = 0, ht(d) = -1.",
                "S", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ket", "Two-site basis vectors", Disp(Equal(Call("ket", F.Id("x"), F.Id("y")),
                    Call("single", Seq(Open, F.Id("x"), Comma, F.Id("y"), Close), D(1)))),
                "ket(x, y) is the basis vector |x y> of C^3 (x) C^3: the function on pairs that is 1 at (x, y) and 0 elsewhere.",
                "ket", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("proj", "Half projectors", Disp(Equal(Call("proj", F.Id("w")),
                    Times(new Formula.Fraction(D(1), D(2)), Call("vecMulVec", F.Id("w"), F.Id("w"))))),
                "proj(w) = (1/2) w w^T, one half of the product of w with its transpose (Matrix.vecMulVec, no complex conjugation); for the three real vectors in piProj this is (1/2)|w><w|.",
                "proj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pi", "The local projector Pi", PiFormula(),
                "piProj is Pi = U + D + F of eq. UDF, with U = (1/2)(|uf> - |fu>)(<uf| - <fu|), D = (1/2)(|df> - |fd>)(<df| - <fd|) and F = (1/2)(|ud> - |ff>)(<ud| - <ff|), where u, f, d are the basis vectors 0, 1, 2.",
                "piProj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("twosite", "An operator on two sites", TwoSiteFormula(),
                "twoSite(i, j, P) acts as the 9 x 9 matrix P with its first factor on site i and its second on site j, and as the identity on the other sites.",
                "twoSite", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("h", "The periodic Hamiltonian", HFormula(),
                "H^periodic of eq. Hpbc: Pi on the sites i, i + 1 for i = 1, ..., N - 1 and Pi_{N,1} on the sites N, 1; with the sites numbered 0, ..., N - 1 these are the pairs i, finRotate(N, i) with finRotate the cyclic shift i -> i + 1 mod N.",
                "H", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("v", "The ground states v_m", VFormula(),
                "v_m is the sum of the paths from (0, 0) to (N, m) with steps in {-1, 0, 1} (Conjecture 1): the sum of the basis words of height m.",
                "v", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2", ClaimFormula(),
                "For N at least 2: Sigma^+ and Sigma^- commute with H; for -N <= m < N, Sigma^+ v_m is a nonzero multiple of v_(m+1); for -N < m <= N, Sigma^- v_m is a nonzero multiple of v_(m-1); and Sigma^+ v_N = 0, Sigma^- v_(-N) = 0 (eqs. Sigmavec and SpmH).",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of Conjecture 2", Disp(F.Id("claim")),
                "An ordered product of operators on distinct sites has as entry at a, b the product of the local entries. The entry of s^r at x, y is 1 when ht(x) = ht(y) + r and 0 otherwise, so for given basis words a and b exactly one exponent vector, r_i = ht(a_i) - ht(b_i), gives a nonzero product, and Sig(N, e) has entry 1 at a, b when S(a) = S(b) + e and 0 otherwise; that is, Sigma^± is the sum over m of |v_(m±1)><v_m|. Each of U, D, F pairs two basis states of the same height sum with opposite signs, so every row of Pi sums to zero over each height class; hence every two-site term, and H, annihilate every v_m, and H is symmetric, so v_m^T H = 0 as well. Therefore H Sigma^± = 0 = Sigma^± H. Finally Sigma^± v_m = T_m v_(m±1), where T_m, the number of words of height m, is positive for |m| <= N, while no word has height ±(N + 1).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pronko-2025-motzkin-raising-lowering"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("pronkomotz-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Neg(Formula value) => new Formula.Negate(value);

    private static Formula Mat3(params byte[] e) =>
        Call("matrix", Seq(Open, D(e[0]), Comma, D(e[1]), Comma, D(e[2]), Close),
            Seq(Open, D(e[3]), Comma, D(e[4]), Comma, D(e[5]), Close),
            Seq(Open, D(e[6]), Comma, D(e[7]), Comma, D(e[8]), Close));

    private static Formula SpowFormula() => Disp(And(
        Parenthesized(Equal(Call("spow", D(0)), new Formula.Power(F.Id("sm"), D(2)))),
        And(Parenthesized(Equal(Call("spow", D(1)), F.Id("sm"))),
            And(Parenthesized(Equal(Call("spow", D(2)), D(1))),
                And(Parenthesized(Equal(Call("spow", D(3)), F.Id("sp"))),
                    Parenthesized(Equal(Call("spow", D(4)), new Formula.Power(F.Id("sp"), D(2)))))))));

    private static Formula HtFormula() => Disp(And(Equal(Call("ht", D(0)), D(1)),
        And(Equal(Call("ht", D(1)), D(0)), Equal(Call("ht", D(2)), Neg(D(1))))));

    private static Formula SiteFormula()
    {
        Formula i = F.Id("i"), a = F.Id("a"), b = F.Id("b"), k = F.Id("k"), mat = F.Id("A");
        Formula agree = All("k", Call("Fin", F.Id("N")), Implies(Call("ne", k, i), Equal(Call("a", k), Call("b", k))));
        return Disp(Equal(new Formula.Apply(Call("site", i, mat), [a, b]),
            IfThenElse(agree, new Formula.Apply(mat, [Call("a", i), Call("b", i)]), D(0))));
    }

    private static Formula FiniteSum(Formula index, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula SigFormula()
    {
        Formula r = F.Id("r"), e = F.Id("e"), i = F.Id("i"), n = F.Id("N");
        Formula total = Equal(FiniteSum(i, Call("Fin", n), Call("rv", Call("r", i))), e);
        Formula vectors = Seq(OpenBrace, r, Sp, InMacro, Sp, new Formula.Power(Call("Fin", D(5)), n), Sp, Mid, Sp,
            total, CloseBrace);
        Formula product = Call("prod", Call("ofFn",
            Seq(Open, i, Sp, Mapsto, Sp, Call("site", i, Call("spow", Call("r", i))), Close)));
        return Disp(Equal(Call("Sig", n, e), FiniteSum(r, vectors, product)));
    }

    private static Formula HeightFormula() =>
        Disp(Equal(Call("S", F.Id("a")), FiniteSum(F.Id("i"), Call("Fin", F.Id("N")), Call("ht", Call("a", F.Id("i"))))));

    private static Formula PiFormula()
    {
        Formula U = Call("proj", Subtract(Call("ket", D(0), D(1)), Call("ket", D(1), D(0))));
        Formula Dm = Call("proj", Subtract(Call("ket", D(2), D(1)), Call("ket", D(1), D(2))));
        Formula Fm = Call("proj", Subtract(Call("ket", D(0), D(2)), Call("ket", D(1), D(1))));
        return Disp(Equal(F.Id("piProj"), Add(Add(U, Dm), Fm)));
    }

    private static Formula TwoSiteFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k"), a = F.Id("a"), b = F.Id("b"), p = F.Id("P");
        Formula agree = All("k", Call("Fin", F.Id("N")), Implies(And(Call("ne", k, i), Call("ne", k, j)),
            Equal(Call("a", k), Call("b", k))));
        return Disp(Equal(new Formula.Apply(Call("twoSite", i, j, p), [a, b]),
            IfThenElse(agree, new Formula.Apply(p, [Seq(Open, Call("a", i), Comma, Call("a", j), Close),
                Seq(Open, Call("b", i), Comma, Call("b", j), Close)]), D(0))));
    }

    private static Formula HFormula() => Disp(Equal(Call("H", F.Id("N")),
        FiniteSum(F.Id("i"), Call("Fin", F.Id("N")),
            Call("twoSite", F.Id("i"), Call("finRotate", F.Id("N"), F.Id("i")), F.Id("piProj")))));

    private static Formula VFormula() => Disp(Equal(new Formula.Apply(Call("v", F.Id("N"), F.Id("m")), [F.Id("a")]),
        IfThenElse(Equal(Call("S", F.Id("a")), F.Id("m")), D(1), D(0))));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), m = F.Id("m"), c = F.Id("c");
        Formula sp = Call("Sig", n, D(1)), sm = Call("Sig", n, Neg(D(1))), h = Call("H", n);
        Formula commute = And(Equal(Times(sp, h), Times(h, sp)), Equal(Times(sm, h), Times(h, sm)));
        Formula up = All("m", Integers(), Implies(And(AtMost(Neg(n), m), Less(m, n)),
            Ex("c", Seq(Mathbb, Grp(F.Id("C"))), And(Call("ne", c, D(0)),
                Equal(Call("mulVec", sp, Call("v", n, m)), Times(c, Call("v", n, Add(m, D(1)))))))));
        Formula down = All("m", Integers(), Implies(And(Less(Neg(n), m), AtMost(m, n)),
            Ex("c", Seq(Mathbb, Grp(F.Id("C"))), And(Call("ne", c, D(0)),
                Equal(Call("mulVec", sm, Call("v", n, m)), Times(c, Call("v", n, Subtract(m, D(1)))))))));
        Formula ends = And(Equal(Call("mulVec", sp, Call("v", n, n)), D(0)), Equal(Call("mulVec", sm, Call("v", n, Neg(n))), D(0)));
        return Disp(Iff(F.Id("claim"), All("N", Naturals(), Implies(AtMost(D(2), n),
            And(commute, And(up, And(down, ends)))))));
    }
}
