using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtUniformFejerGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform Fejér bound for the complete integrated Mangoldt remainder",
        H("The limiting coefficient on a common real tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-eventually-uniform-fejer-gap"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap.rh_iff_eventually_uniform_fejer_gap"),
            H("The squared logarithm and the logarithmic correction"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U and M is firstLiMass. One nonnegative constant C "
                    + "and one real threshold serve every larger real x. The second correction uses "
                    + "the logarithm of the logarithm.")),
                Paragraph(Text(
                    "Put y = log x and q = exp(−y/2). For every amplitude b between zero and one half, "
                    + "the step t = byq satisfies t ≤ 1/2 and yt ≤ 1 on a tail independent of b. "
                    + "ActualKernelCusp.cusp_remainder_bound bounds the quadratic remainder by 2t². "
                    + "Expanding log t gives the common cusp lower bound. A second-order estimate for "
                    + "the two exponentials at the midpoint makes its error at most qby.")),
                Paragraph(Text(
                    "For N equally spaced phases the ordered-pair amplitudes are |j−k|/(2N). "
                    + "Their mean is (1−1/N²)/6 and their mean square is (1−1/N²)/24. The positive "
                    + "Fejér phase comparison then gives the factor 1−1/N² on the quadratic and "
                    + "logarithmic terms. With y fixed on the common tail, send N to infinity. "
                    + "The remaining linear and constant errors are absorbed by C log x.")),
                Paragraph(Text(
                    "In reverse, log(y)/y and 1/y tend to zero. The two corrections are eventually "
                    + "smaller than the margin for any fixed coefficient below 1/48. "
                    + "MangoldtFejerGap.rh_iff_eventually_fejer_gap gives RH. "
                    + "The derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7070606425."))),
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
        var c = F.Id("C");
        var y = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [x]);
        var logY = new Formula.FunctionCall(FormulaIdentifier.Create("log"), [y]);
        var quadratic = new Formula.Fraction(new Formula.Power(y, D(2)), D(4, 8));
        var correction = new Formula.Fraction(Multiply(y, logY), D(1, 2));
        var bound = Add(Add(Subtract(Multiply(F.Id("firstLiMass"), Seq(Sqrt, Grp(x))),
            quadratic), correction), Multiply(c, y));
        var tail = Bind(FormulaQuantifier.ForAll, "x",
            ImpliesClaim(Le(F.Id("T"), x), Le(remainder, bound)));
        var limit = Bind(FormulaQuantifier.Exists, "C", new Formula.Logic(Le(D(0), c),
            FormulaLogicOperator.And, Bind(FormulaQuantifier.Exists, "T", tail)));
        return Disp(new Formula.Logic(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            FormulaLogicOperator.Iff, limit));
    }
}
