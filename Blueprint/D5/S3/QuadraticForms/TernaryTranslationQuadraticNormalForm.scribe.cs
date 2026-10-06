using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class TernaryTranslationQuadraticNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary quadratic form on functions over a ternary group, built from a graph and vertex translations, is linearly equivalent to a sum of binary bilinear blocks, one per pair of opposite nonzero characters.",
        H("Ternary translation quadratic forms split into binary bilinear blocks"),
        Blocks(
            Node("translation-form", "The translation quadratic form", "F", FormFormula(),
                "Write ℤ/2ℤ for the binary field and (ℤ/3ℤ)^d, the functions Fin d → ℤ/3ℤ, for the ternary group. For any binary matrix A and a translation δ_u at each index u, the form sums over replicas r and indices u < v. It uses A_uv to weight the product at r and the product at r + δ_u and r + δ_v. For a graph adjacency matrix these are the two replica contributions of each edge; diagonal entries of A are unused.",
                DescribeRole.Definition),
            Node("cut-matrix", "The cut matrix of a character", "C", CutFormula(),
                "For a character t of the ternary group, C_t keeps the entries A_uv whose translations have different values under t and sets the others to zero.",
                DescribeRole.Definition),
            Node("normal-form", "The block normal form", "ternary_translation_quadratic_normal_form", NormalFormFormula(),
                "Let A be symmetric and let P omit zero and contain exactly one of t and −t for every nonzero character t. No restriction on the diagonal of A is needed: F ignores it and every C_t has zero diagonal. Encode x by its sums over replicas at each vertex and, for each t in P, by the two binary coordinates in the basis (1, ω) of the twisted Fourier coefficient χ_t(δ_u) times the transform of x at u, computed in the field with four elements. The first component of E(x) is the constant mode; fst(snd(E(x))(t)) and snd(snd(E(x))(t)) are the two vectors of the t block. The encoding is injective: the constant mode together with one mode from each pair of opposite characters determines every binary coefficient of x by Fourier inversion, because the transform at −t is the Frobenius conjugate of the transform at t. Hence it is a linear equivalence by counting. Expanding each edge term in Fourier modes, the two replica terms of an edge cancel in every mode t with t·δ_u = t·δ_v, since 1 + 1 = 0 in characteristic two, and the remaining cross terms over the pair {t, −t} are the binary bilinear form of C_t in the two coordinates of mode t.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z(byte n) => Seq(Mathbb, Grp(V("Z")), Slash, D(n), Mathbb, Grp(V("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, Formula arg) => Seq(head, Open, arg, Close);
    private static Formula App(Formula head, Formula first, Formula second) =>
        Seq(head, Open, first, Comma, Sp, second, Close);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Not(Formula body) => Seq(Neg, Sp, Parenthesized(body));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Plus2(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Times2(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Dot2(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula FinN(Formula n) => Call("Fin", n);
    private static Formula Bin() => Z(2);
    private static Formula Grp3(Formula d) => Parenthesized(Arrow(FinN(d), Z(3)));
    private static Formula Vec(Formula n) => Arrow(FinN(n), Bin());
    private static Formula Mat(Formula n) => Call("Matrix", FinN(n), FinN(n), Bin());
    private static Formula Pairing(Formula t, Formula delta, Formula u) =>
        SumOver(V("i"), Dot2(App(t, V("i")), App(App(delta, u), V("i"))));

    private static Formula FormFormula()
    {
        Formula n = V("N"), d = V("d"), a = V("A"), delta = DeltaLower, x = V("x"),
            r = V("r"), u = V("u"), v = V("v");
        Formula ru = Plus2(r, App(delta, u)), rv = Plus2(r, App(delta, v));
        Formula edge = Times2(App(a, u, v), Parenthesized(Plus2(
            Dot2(App(x, r, u), App(x, r, v)), Dot2(App(x, ru, u), App(x, rv, v)))));
        Formula body = SumOver(Seq(r, Comma, Sp, u, Sp, Lt, Sp, v), edge);
        return Disp(For(Seq(n, Sp, d), N(), For(a, Mat(n), For(delta, Arrow(FinN(n), Grp3(d)),
            For(x, Arrow(Grp3(d), Vec(n)), Equal(Call("F", a, delta, x), body))))));
    }

    private static Formula CutFormula()
    {
        Formula n = V("N"), d = V("d"), a = V("A"), delta = DeltaLower, t = V("t"),
            u = V("u"), v = V("v");
        Formula cut = Seq(Call("if", Equal(Pairing(t, delta, u), Pairing(t, delta, v)), D(0), App(a, u, v)));
        return Disp(For(Seq(n, Sp, d), N(), For(a, Mat(n), For(delta, Arrow(FinN(n), Grp3(d)),
            For(t, Grp3(d), For(Seq(u, Sp, v), FinN(n),
                Equal(App(Call("C", a, delta, t), u, v), cut)))))));
    }

    private static Formula NormalFormFormula()
    {
        Formula n = V("N"), d = V("d"), a = V("A"), delta = DeltaLower, p = V("P"), t = V("t"),
            u = V("u"), v = V("v"), x = V("x"), e = V("E");
        Formula symmetric = For(Seq(u, Sp, v), FinN(n), Equal(App(a, u, v), App(a, v, u)));
        Formula reps = For(t, Grp3(d), Imp(NotEqual(t, D(0)),
            Parenthesized(IffOf(Member(t, p), Not(Member(Seq(Minus, t), p))))));
        Formula memberType = Seq(OpenBrace, t, Colon, Sp, Grp3(d), Sp, Mid, Sp,
            Member(t, p), CloseBrace);
        Formula target = Times2(Parenthesized(Vec(n)),
            Parenthesized(Arrow(memberType,
                Parenthesized(Times2(Parenthesized(Vec(n)), Parenthesized(Vec(n)))))));
        Formula mode = App(Call("snd", App(e, x)), t);
        Formula block = Dot2(Dot2(App(Call("fst", mode), u),
            App(Call("C", a, delta, t), u, v)), App(Call("snd", mode), v));
        Formula identity = For(x, Arrow(Grp3(d), Vec(n)),
            Equal(Call("F", a, delta, x), SumOver(Member(t, p), SumOver(Seq(u, Comma, v), block))));
        Formula conclusion = Some(e, Call("LinearEquiv", Bin(), Arrow(Grp3(d), Vec(n)), target), identity);
        return Disp(For(Seq(n, Sp, d), N(), For(a, Mat(n), Imp(Parenthesized(symmetric),
            For(delta, Arrow(FinN(n), Grp3(d)), For(p, Call("Finset", Grp3(d)),
                Imp(Not(Member(D(0), p)), Imp(Parenthesized(reps), conclusion))))))));
    }
}
