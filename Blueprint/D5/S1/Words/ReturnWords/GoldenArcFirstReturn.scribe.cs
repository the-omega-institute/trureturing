using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class GoldenArcFirstReturnDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent rotation cuts are best displacements.", H("Best displacements"), Blocks(
        Describe.Lean(DescribeId.Create("cassaigne-owner-rotation-gap-best-displacement"),
            DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturn.rotation_gap_best_displacement"),
            H("Every gap is a best displacement"), StatementSource.FromAuthor(Disp(BestDisplacement())),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "For an irrational rotation with at least two cuts, each adjacent gap is a forward or backward displacement no larger than the displacements with smaller positive indices."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("cassaigne-owner-golden-mechanical-slope"),
            DeclarationHandle.Create("D5/S1/Words/ReturnWords/GoldenArcFirstReturn.golden_mechanical_slope_eq_goldenRatio_sub_one"),
            H("The golden mechanical slope"),
            StatementSource.FromAuthor(Disp(Seq(Q("goldenMechanicalSlope"), Eq,
                Q("Real.goldenRatio"), Minus, D(1)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The golden mechanical slope is the golden ratio minus one."))), DescribeRole.Theorem))));

    private static Formula BestDisplacement()
    {
        Formula alpha = Q("alpha"), n = Q("N"), r = Q("r"), a = Q("a"), ell = Q("ell"), d = Q("d");
        Formula cut(Formula index) => Seq(Q("rotationCut"), Sp, alpha, Sp, n, Sp, index);
        Formula displacement(string name, Formula index) => Seq(Q(name), Sp, alpha, Sp, index);
        Formula branch(string name) => Parenthesized(Seq(
            ell, Eq, displacement(name, d), Sp, Land, Sp,
            All(Q("k"), Q("Nat"), Implies(Seq(D(0), Lt, Q("k")),
                Implies(Seq(Q("k"), Lt, d), Seq(ell, Leq, displacement(name, Q("k"))))))));
        Formula body = Seq(
            Q("let"), Sp, a, Colon, Q("Real"), Colon, Eq, cut(Q("r.castSucc")), Semi, Sp,
            Q("let"), Sp, ell, Colon, Q("Real"), Colon, Eq, cut(Q("r.succ")), Minus, a, Semi, Sp,
            Exists, Sp, d, Colon, Q("Nat"), Comma, Sp, D(0), Lt, d, Sp, Land, Sp,
            Parenthesized(Seq(branch("forwardDisplacement"), Sp, Lor, Sp, branch("backwardDisplacement"))));
        return All(alpha, Q("Real"), All(n, Q("Nat"), Seq(
            OpenBracket, Q("Fact"), Sp, Parenthesized(Seq(Q("Irrational"), Sp, alpha)), CloseBracket, Comma, Sp,
            OpenBracket, Q("NeZero"), Sp, n, CloseBracket, Comma, Sp,
            Implies(Seq(D(1), Lt, n), All(r, Seq(Q("Fin"), Sp, n), body)))));
    }
    private static Formula Q(string name) => Seq(Operatorname, Grp(Seq([.. name.Split('.').SelectMany((part, index) => index == 0 ? new Formula[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) })])));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Implies(Formula premise, Formula conclusion) => Seq(Parenthesized(premise), Rightarrow, conclusion);
}
