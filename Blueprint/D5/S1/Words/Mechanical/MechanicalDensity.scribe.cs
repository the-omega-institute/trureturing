using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "General discrepancy and density for lower mechanical words.",
        H("Discrepancy and Density of Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "For every real slope alpha in the half-open interval from zero to one, every real "
                + "intercept rho, and every window start, the lower mechanical true count differs "
                + "from its expected count by strictly less than one. Dividing by the window length "
                + "then gives the density alpha at every fixed start; no irrationality assumption is used.")),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-window-discrepancy"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy"),
                H("Every lower mechanical window has discrepancy below one"),
                StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Relation(
                    new Formula.Absolute(Subtract(
                        Call("windowTrueCount", F.Id("alpha"), F.Id("rho"), F.Id("i"), F.Id("n")),
                        Multiply(F.Id("n"), F.Id("alpha")))),
                    FormulaRelationOperator.LessThan,
                    Num(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing endpoint-floor telescope rewrites the count difference as the "
                    + "difference of two fractional parts. Nonnegativity and strict upper bounds "
                    + "for those fractional parts give both sides of the absolute-value inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-window-density"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density"),
                H("Every fixed-start lower mechanical density tends to the slope"),
                StatementSource.FromAuthor(FormulaDsl.Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty),
                    Frac, Grp(Call("windowTrueCount", F.Id("alpha"), F.Id("rho"), F.Id("i"), F.Id("n"))),
                    F.Id("n"), Eq, F.Id("alpha"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive window lengths, the discrepancy inequality places the quotient "
                    + "between alpha minus 1 over n and alpha plus 1 over n. Both bounds converge "
                    + "to alpha, so the squeeze theorem proves the fixed-start density limit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalBalance")),
        ]));
}
