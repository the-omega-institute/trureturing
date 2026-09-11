using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class A380056Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/A380056.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2025a380056");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A roots-of-unity filter collapses the surviving binomial sum, which is the step "
        + "the two published facts leave open.",
        H("Divisibility at Multiples of Four"),
        Blocks(
            Paragraph(Text(
                "Two facts are taken as hypotheses rather than reproved: a finite formula "
                + "for the even-indexed terms, and the residues of the Euler secant numbers "
                + "modulo five. Both are published; neither implies the conclusion. What is "
                + "proved is the implication, so nothing here asserts that a particular "
                + "sequence satisfies the hypotheses.")),
            Node("binomial_residue_two", "A roots-of-unity filter", FilterFormula(),
                "Two and three have order four modulo five, so the indicator of an index "
                + "congruent to two modulo four is a combination of four powers. The "
                + "binomial theorem then turns each power sum into a closed form, and the "
                + "four closed forms leave one. The finite checks are confined to fixed "
                + "residue facts and do not range over the index.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("surviving_sum", "The surviving terms cancel", SurvivingFormula(),
                "Reducing by the Euler residues leaves the terms whose Euler index is odd, "
                + "together with the endpoint. Reindexing sends those to exactly the "
                + "arguments the filter selects, so their weighted sum is the filtered one, "
                + "and the endpoint contributes the one that cancels it.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("a380056_div_five", "The conjecture, from the two published facts",
                MainFormula(),
                "Substituting the printed formula at twice the index and reducing modulo "
                + "five leaves the surviving sum, which vanishes. The hypotheses are the "
                + "literature's contribution; the cancellation is not among them.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380056-fourth-index-divisible-by-five"),
                    ResolutionKind.Proved)),
            Paragraph(Text(
                "The other conjecture printed on the same entry is untouched, and no claim "
                + "is made about the generating function itself.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a380056-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula FilterFormula() => Universal(Seq(
        D(1), Sp, Leq, Sp, N(), Sp, Rightarrow, Sp,
        SumOver(J(), Call("range", Add(Mul(D(4), N()), D(1)))),
        Bracket(Seq(Mod(J(), D(4)), Sp, Eq, Sp, D(2))), Sp,
        Binom(Mul(D(4), N()), J()), Sp, Eq, Sp, D(1), Sp, InMod(D(5))));

    private static Formula SurvivingFormula() => Universal(Seq(
        D(1), Sp, Leq, Sp, N(), Sp, Rightarrow, Sp,
        SumOver(K(), Call("Icc", D(1), Mul(D(2), N()))),
        Bracket(Seq(K(), Sp, Eq, Sp, Mul(D(2), N()), Sp, Lor, Sp,
            Mod(Sub(Mul(D(2), N()), K()), D(2)), Sp, Eq, Sp, D(1))), Sp,
        Binom(Mul(D(4), N()), Mul(D(2), K())), Sp, Cdot, Sp,
        Pow(D(4), Sub(Mul(D(2), N()), K())), Sp, Eq, Sp, D(0), Sp, InMod(D(5))));

    private static Formula MainFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("E"), Colon, Sp,
        Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Open, Hyp1(), Sp, Land, Sp, Hyp2(), Sp, Land, Sp, Hyp3(), Close, Sp,
        Rightarrow, Sp, Forall, Sp, N(), Comma, Sp, D(1), Sp, Leq, Sp, N(), Sp,
        Rightarrow, Sp, D(5), Sp, Mid, Sp, Call("a", Mul(D(4), N()))));

    private static Formula Hyp1() => Seq(
        Forall, Sp, M(), Comma, Sp, D(1), Sp, Leq, Sp, M(), Sp, Rightarrow, Sp,
        Call("a", Mul(D(2), M())), Sp, Eq, Sp,
        SumOver(K(), Call("Icc", D(1), M())),
        Binom(Mul(D(2), M()), Mul(D(2), K())), Sp, Cdot, Sp,
        Call("E", Sub(M(), K())), Sp, Cdot, Sp, Pow(D(4), Sub(M(), K())));

    private static Formula Hyp2() => Seq(Call("E", D(0)), Sp, Eq, Sp, D(1));

    private static Formula Hyp3() => Seq(
        Forall, Sp, R(), Comma, Sp, D(0), Sp, Lt, Sp, R(), Sp, Rightarrow, Sp,
        Mod(Call("E", R()), D(5)), Sp, Eq, Sp,
        Open, D(1), Sp, Text0("if"), Sp, Mod(R(), D(2)), Sp, Eq, Sp, D(1), Comma, Sp,
        D(0), Sp, Text0("otherwise"), Close);

    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula SumOver(Formula v, Formula s) => Seq(
        new Formula.Subscript(F.Sum, Seq(v, Sp, InMacro, Sp, s)), Sp);
    private static Formula Bracket(Formula b) => Seq(OpenBracket, b, CloseBracket);
    private static Formula Binom(Formula a, Formula b) =>
        Call("choose", a, b);
    private static Formula InMod(Formula m) => Seq(Open, Mathrm, Grp(F.Id("mod")), Sp, m, Close);
    private static Formula Text0(string w) => Seq(Mathrm, Grp(F.Id(w)));
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula R() => F.Id("r");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
