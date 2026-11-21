using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtLogSquareGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithm-squared savings for the integrated Mangoldt remainder",
        H("The real-axis gap at the critical coefficient"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-eventually-log-squared-gap"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap"),
            H("A squared-logarithm criterion for the Riemann hypothesis"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U and M is firstLiMass. The threshold may depend on "
                    + "the real coefficient c. The inequality holds at every real x above that threshold.")),
                Paragraph(Text(
                    "Write y = log x, q = exp(−y/2), h = yq/4 and d(t) = M − K(t). "
                    + "ActualKernelCusp.cusp_quadratic_limit gives d(t)/(t log(1/t)) → 1/2 "
                    + "as t decreases to zero. Since log(1/h)/y → 1/2, the quotient d(h)/(qy²) tends to 1/16.")),
                Paragraph(Text(
                    "Under RH the positive cosine weights give the lower bound 2d(h) − 4d(y) for "
                    + "the second difference of K. The midpoint inequality for the Mangoldt ramps "
                    + "bounds that difference from above. After division by qy² its exponential term "
                    + "tends to 1/16, while the residual terms tend to zero. Thus every c below "
                    + "(2/16 − 1/16)/4 gives the asserted eventual saving. The endpoint is not asserted.")),
                Paragraph(Text(
                    "Conversely, c = 1/128 gives a gap tending to positive infinity. "
                    + "MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop then gives RH. "
                    + "The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7069599052."))),
            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), Real, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ImpliesClaim(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Claim()
    {
        var x = F.Id("x");
        var remainder = new Formula.FunctionCall(FormulaIdentifier.Create("U"), [x]);
        var c = F.Id("c");
        var log = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [x]);
        var bound = Subtract(Multiply(F.Id("firstLiMass"), Seq(Sqrt, Grp(x))),
            Multiply(c, new Formula.Power(log, D(2))));
        var tail = Bind(FormulaQuantifier.ForAll, "x",
            ImpliesClaim(Le(F.Id("T"), x), Le(remainder, bound)));
        var strict = new Formula.Relation(c, FormulaRelationOperator.LessThan,
            new Formula.Fraction(D(1), D(64)));
        var limit = Bind(FormulaQuantifier.ForAll, "c", ImpliesClaim(strict,
            Bind(FormulaQuantifier.Exists, "T", tail)));
        return Disp(new Formula.Logic(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            FormulaLogicOperator.Iff, limit));
    }
}
