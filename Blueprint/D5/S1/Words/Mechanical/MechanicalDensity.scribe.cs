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
                DescribeRole.Theorem),
            Paragraph(Text(
                "Application to complementary-width circular windows. Take an arbitrary real "
                + "slope alpha strictly between zero and one, initial phase u and window centre c. "
                + "Set the width w to one minus alpha, the left endpoint a to c minus w over two, "
                + "and the mechanical intercept rho to u minus a. A positive integer time k is a "
                + "hit exactly when the fractional part of u plus k times alpha minus a is less "
                + "than w. This defines a left-closed, right-open circular window. Let H(N) count "
                + "hits at precisely times one through N, with an empty count when N is zero.")),
            Paragraph(Text(
                "The lower mechanical letter at time k is the floor increment from rho plus "
                + "k times alpha to rho plus (k plus one) times alpha. It is either zero or one, "
                + "and equals one exactly when the starting fractional part is at least one "
                + "minus alpha. Thus a hit is the complement of a true letter. Equality at the "
                + "carry threshold is excluded from the window. The exact count correspondence is "),
                Math(Equal(Call("H", F.Id("N")), Subtract(F.Id("N"),
                    Call("windowTrueCount", F.Id("alpha"), F.Id("rho"), Num(1), F.Id("N"))))),
                Text(". The start index is one, rather than zero.")),
            Paragraph(Text(
                "Apply the discrepancy result with this intercept, start index one and length N. "
                + "The hit discrepancy is the negative of the true-letter discrepancy, so "),
                Math(new Formula.Relation(
                    new Formula.Absolute(Subtract(Call("H", F.Id("N")),
                        Multiply(F.Id("N"), F.Id("w")))),
                    FormulaRelationOperator.LessThan, Num(1))),
                Text(" for every natural N, including zero. The endpoint-floor identity in "),
                Ref("D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor"),
                Text(" expresses that discrepancy exactly as "),
                Math(Equal(
                    Subtract(Call("H", F.Id("N")), Multiply(F.Id("N"), F.Id("w"))),
                    Subtract(
                        Call("fract", Add(F.Id("rho"),
                            Multiply(Add(F.Id("N"), Num(1)), F.Id("alpha")))),
                        Call("fract", Add(F.Id("rho"), F.Id("alpha")))))),
                Text(". Both fractional parts lie in the half-open unit interval.")),
            Paragraph(Text(
                "For positive N, division gives frequency error strictly below one over N, "
                + "uniformly in the initial phase, window centre and slope subject to this width "
                + "relation. In particular the frequency tends to w. Taking alpha to be the "
                + "golden ratio minus one gives width two minus the golden ratio. Taking a "
                + "fractional part before the window test gives the identical predicate because "),
                Math(Equal(
                    Call("fract", Subtract(Call("fract", F.Id("x")), F.Id("a"))),
                    Call("fract", Subtract(F.Id("x"), F.Id("a"))))),
                Text(". No irrationality premise is needed. The conclusion uses width one minus "
                    + "alpha and does not classify arbitrary independent window widths, certify "
                    + "floating-point evaluation or supply a physical interpretation."))),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalBalance")),
        ]));
}
