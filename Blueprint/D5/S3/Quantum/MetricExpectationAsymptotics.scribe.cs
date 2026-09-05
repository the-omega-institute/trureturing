using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MetricExpectationAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/MetricExpectationAsymptotics."
            + "metric_expectation_closed_form_asymptotics";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Abstract incomplete-Gamma endpoint laws imply the stated closed-form asymptotics.",
        H("Metric Expectation Asymptotics"),
        Blocks(Describe.Lean(
            DescribeId.Create("incomplete-gamma-endpoint-laws-control-the-closed-form"),
            DeclarationHandle.Create(Declaration),
            H("Incomplete-Gamma endpoint laws control the closed form"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a positive real function on nonnegative arguments. Assume G "
                        + "tends to a nonzero value g0 at zero from the right and that "
                        + "sqrt(x) exp(x) G(x) tends to one at infinity.")),
                Paragraph(Text(
                    "For the source's displayed closed form, the normalized expression tends "
                        + "to one at zero from the right, its first relative correction tends "
                        + "to (4 / sqrt(2)) / g0, and the unnormalized closed form tends to "
                        + "one at infinity.")),
                Paragraph(Text(
                    "The atom does not specify the conditional probability law needed to "
                        + "derive the claimed exact expectation. Pinned Mathlib also has no "
                        + "upper incomplete-Gamma API with the required endpoint theorems. "
                        + "The formal statement therefore parameterizes that factor and makes "
                        + "its two standard asymptotic laws explicit; it does not claim the "
                        + "expectation identity itself.")),
                Paragraph(Text(
                    "The proof uses Real.tendsto_exp_nhds_zero_nhds_one, Tendsto.inv0, "
                        + "tendsto_pow_atTop, Tendsto.const_mul_atTop, const_div_atTop, and the "
                        + "real square-root identities. Every division is protected by the "
                        + "nonzero endpoint or strict positivity hypotheses."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula upperGammaHalf = F.Id("G");
        Formula gammaAtZero = F.Id("g0");
        Formula closedForm = Call("metricExpectationClosedForm", upperGammaHalf);
        Formula correction = Call("normalizedCorrection", upperGammaHalf);
        Formula assumptions = All(
            NotEqual(gammaAtZero, D(0)),
            Call("positiveOnNonnegative", upperGammaHalf),
            Call("tendstoAtZeroRight", upperGammaHalf, gammaAtZero),
            Call("standardUpperGammaHalfTail", upperGammaHalf));
        Formula correctionLimit = Call(
            "div",
            Call("div", D(4), Call("sqrt", D(2))),
            gammaAtZero);
        Formula conclusions = All(
            Call("tendstoAtZeroRight", Call("normalizedClosedForm", upperGammaHalf), D(1)),
            Call("tendstoAtZeroRight", correction, correctionLimit),
            Call("tendstoAtTop", closedForm, D(1)));

        return Disp(ForAll(
            [
                Bound("G", new Formula.TypeArrow(real, real)),
                Bound("g0", real),
            ],
            Implies(assumptions, conclusions)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
}
