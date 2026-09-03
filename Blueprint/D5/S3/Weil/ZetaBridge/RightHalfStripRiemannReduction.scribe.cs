using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RightHalfStripRiemannReductionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction."
            + "golden_right_half_strip_implies_rh";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right half-strip zero-freeness implies the Riemann hypothesis by zeta reflection.",
        H("Right Half-Strip Riemann Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("right-half-strip-zero-freeness-implies-rh"),
            DeclarationHandle.Create(Declaration),
            H("Right half-strip zero-freeness implies the Riemann hypothesis"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The zeta functional equation reflects every zero strictly left of the "
                        + "critical line and inside the critical strip into the open right "
                        + "half-strip. The standard nonvanishing theorem excludes real part "
                        + "at least one.")),
                Paragraph(Text(
                    "For nonpositive real part, the same functional equation and the "
                        + "nonvanishing of the gamma and exponential factors force a trivial "
                        + "zeta zero. This is a pure Mathlib reduction with no golden structure; "
                        + "it does not assert either premise or the Riemann hypothesis "
                        + "unconditionally."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula rho = F.Id("rho");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula realPart = Seq(Re, Sp, Open, rho, Close);
        Formula rightHalfStripExclusion = ForAll(
            [Bound("rho", complex)],
            Implies(
                Equal(Call("riemannZeta", rho), D(0)),
                Implies(
                    Less(half, realPart),
                    Implies(Less(realPart, D(1)), F.Id("False")))));

        return Disp(Implies(
            rightHalfStripExclusion,
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis")))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
