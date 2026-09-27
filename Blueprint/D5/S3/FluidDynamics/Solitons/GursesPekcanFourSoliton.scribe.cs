using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Solitons;

internal sealed class GursesPekcanFourSolitonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Solitons/GursesPekcanFourSoliton.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FluidDynamics/gurses2025higher");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the Hirota bilinear equation D_x(D_x^3 + a1 D_t + a2 D_y)^(2k+1){f.f} = 0, the four-soliton condition holds identically on the dispersion relation when k = 0 and fails at the wave numbers 1, 3, 4, 5 for every k at least one.",
        H("Four-soliton solutions of D_x(D_x^3 + a1 D_t + a2 D_y)^(2k+1) exist only for k = 0"),
        Blocks(
            Node("hirota-p", "The polynomial of the bilinear operator", HirotaFormula(),
                "For the soliton parameters p = (k, omega, l) of an exponential exp(kx + omega t + l y), the operator D_x(D_x^3 + a1 D_t + a2 D_y)^m has the polynomial k (k^3 + a1 omega + a2 l)^m.",
                "hirotaP", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dispersion", "The dispersion relation", DispersionFormula(),
                "The source writes omega = -(k^3 + a2 l)/a1 for a1 nonzero; the relation k^3 + a1 omega + a2 l = 0 is the same condition and also covers a1 = 0 with a2 nonzero.",
                "dispersion", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("four-sc", "The four-soliton condition", FourScFormula(),
                "The eight terms of the source's display, Hietarinta's form with the first sign fixed, for any function P of the parameters and parameters p_1, ..., p_4. The last factor of the fifth term is P(p_1 + p_2 + p_3 - p_4): the source prints P(p_1 - p_2 + p_3 - p_4), the last factor of the seventh term, while the pair factors of the fifth term belong to the sign pattern (+, +, +, -).",
                "fourSC", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured lemma of Gurses and Pekcan", ClaimDefinitionFormula(),
                "The first conjunct says that for k = 0 the four-soliton condition vanishes at all parameters satisfying the dispersion relation. The second says that for every k at least one there are such parameters at which it does not vanish, so the condition is not satisfied directly.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The four-soliton condition holds only for k = 0", ClaimFormula(),
                "On the dispersion relation a1 omega + a2 l = -k^3, and the map (k, omega, l) to (k, a1 omega + a2 l) is additive, so every value of P at a signed sum of parameters equals x (x^3 + e)^m with x the signed sum of the wave numbers and e minus the signed sum of their cubes. For m = 1 the condition becomes a polynomial identity in the four wave numbers, which holds. For m = 2k + 1 with k at least one, the wave numbers 1, 3, 4, 5 with omega_i = -k_i^3/a1 and l_i = 0 (or omega_i = 0 and l_i = -k_i^3/a2 when a1 = 0) satisfy the dispersion relation, and each of the eight terms is a product of seven factors x (x^3 + e)^m, which collects into 48 g^m F(m) with g = 1360488960000 and F(m) = 13 11^m - 55 (-31)^m + 392 56^m + 525 21^m + 162 18^m - 350 14^m - 567 63^m - 120 (-24)^m. For odd m the positive terms of F(m) are at most 1267 56^m, and 1267 56^m < 567 63^m from m = 7 on by induction; F(3) and F(5) are negative by direct computation. So the condition is negative for every k at least one.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gurses-pekcan-2025-higher-hirota-four-soliton"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("gurses-pekcan-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
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
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Triples() =>
        Seq(Reals(), Sp, F.Times, Sp, Reals(), Sp, F.Times, Sp, Reals());
    private static Formula Parameters() => new Formula.TypeArrow(Call("Fin", D(4)), Triples());
    private static Formula A(byte i) => F.Id(i == 1 ? "alpha1" : "alpha2");
    private static Formula Point(byte i) => new Formula.Subscript(F.Id("p"), D(i));

    private static Formula HirotaFormula()
    {
        Formula k = F.Id("k"), w = F.Id("omega"), l = F.Id("l"), m = F.Id("m");
        Formula inner = Add(Add(Power(k, D(3)), Mul(A(1), w)), Mul(A(2), l));
        Formula value = Mul(k, Power(Parenthesized(inner), m));
        return Disp(Equal(Call("hirotaP", A(1), A(2), m, Parenthesized(Seq(k, Comma, Sp, w, Comma, Sp, l))), value));
    }

    private static Formula DispersionFormula()
    {
        Formula k = F.Id("k"), w = F.Id("omega"), l = F.Id("l");
        Formula body = Equal(Add(Add(Power(k, D(3)), Mul(A(1), w)), Mul(A(2), l)), D(0));
        return Disp(new Formula.Logic(
            Call("dispersion", A(1), A(2), Parenthesized(Seq(k, Comma, Sp, w, Comma, Sp, l))),
            FormulaLogicOperator.Iff, Parenthesized(body)));
    }

    // A signed sum of parameters, from sign entries +1, -1 or 0 per index.
    private static Formula Signed(params int[] signs)
    {
        Formula? acc = null;
        for (var i = 0; i < signs.Length; i++)
        {
            if (signs[i] == 0) continue;
            var point = Point((byte)(i + 1));
            acc = acc is null
                ? (signs[i] > 0 ? point : new Formula.Negate(point))
                : (signs[i] > 0 ? Add(acc, point) : Subtract(acc, point));
        }
        return Call("P", acc!);
    }

    private static Formula Pair(int i, int j, int sign)
    {
        var signs = new int[4];
        signs[i] = 1;
        signs[j] = sign;
        return Signed(signs);
    }

    private static Formula Term(int[] last, params (int I, int J, int Sign)[] pairs)
    {
        Formula product = Pair(pairs[0].I, pairs[0].J, pairs[0].Sign);
        for (var t = 1; t < pairs.Length; t++)
            product = Mul(product, Pair(pairs[t].I, pairs[t].J, pairs[t].Sign));
        return Mul(product, Signed(last));
    }

    private static Formula FourScBody()
    {
        Formula t1 = Term([1, 1, 1, 1], (0, 1, -1), (0, 2, -1), (0, 3, -1), (1, 2, -1), (1, 3, -1), (2, 3, -1));
        Formula t2 = Term([1, -1, -1, -1], (1, 2, -1), (1, 3, -1), (2, 3, -1), (0, 2, 1), (0, 1, 1), (0, 3, 1));
        Formula t3 = Term([1, -1, 1, 1], (0, 2, -1), (0, 3, -1), (2, 3, -1), (0, 1, 1), (1, 2, 1), (1, 3, 1));
        Formula t4 = Term([1, 1, -1, 1], (0, 1, -1), (0, 3, -1), (1, 3, -1), (0, 2, 1), (1, 2, 1), (2, 3, 1));
        Formula t5 = Term([1, 1, 1, -1], (0, 1, -1), (0, 2, -1), (1, 2, -1), (0, 3, 1), (1, 3, 1), (2, 3, 1));
        Formula t6 = Term([1, 1, -1, -1], (0, 1, -1), (2, 3, -1), (0, 2, 1), (0, 3, 1), (1, 2, 1), (1, 3, 1));
        Formula t7 = Term([1, -1, 1, -1], (0, 2, -1), (1, 3, -1), (0, 1, 1), (0, 3, 1), (1, 2, 1), (2, 3, 1));
        Formula t8 = Term([1, -1, -1, 1], (0, 3, -1), (1, 2, -1), (0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1));
        Formula minus = Subtract(Subtract(Subtract(Subtract(t1, t2), t3), t4), t5);
        return Add(Add(Add(minus, t6), t7), t8);
    }

    private static Formula FourScFormula() => Disp(Equal(Call("fourSC", F.Id("P"), F.Id("p")), FourScBody()));

    private static Formula NonzeroAlpha() =>
        NotEqual(Parenthesized(Seq(A(1), Comma, Sp, A(2))), Parenthesized(Seq(D(0), Comma, Sp, D(0))));

    private static Formula OnDispersion() =>
        All("i", Call("Fin", D(4)), Call("dispersion", A(1), A(2), new Formula.Apply(F.Id("p"), [F.Id("i")])));

    private static Formula ClaimBody()
    {
        Formula p = F.Id("p"), k = F.Id("k");
        Formula zero = All("alpha1", Reals(), All("alpha2", Reals(), Implies(NonzeroAlpha(),
            All("p", Parameters(), Implies(OnDispersion(),
                Equal(Call("fourSC", Call("hirotaP", A(1), A(2), D(1)), p), D(0)))))));
        Formula higher = All("alpha1", Reals(), All("alpha2", Reals(), Implies(NonzeroAlpha(),
            All("k", Naturals(), Implies(AtMost(D(1), k),
                Some("p", Parameters(), And(OnDispersion(),
                    NotEqual(Call("fourSC", Call("hirotaP", A(1), A(2), Add(Mul(D(2), k), D(1))), p), D(0)))))))));
        return And(zero, higher);
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
