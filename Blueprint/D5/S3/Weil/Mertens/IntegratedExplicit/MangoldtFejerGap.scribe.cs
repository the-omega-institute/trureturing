using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtFejerGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fejér averages for the integrated Mangoldt remainder",
        H("A family of midpoint inequalities"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-iff-eventually-fejer-gap"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap.rh_iff_eventually_fejer_gap"),
            H("A squared-logarithm saving for every coefficient below one forty-eighth"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U and M is firstLiMass. For each real c below "
                    + "1/48, the threshold may depend on c. The estimate holds for all real x past it.")),
                Paragraph(Text(
                    "Write y = log x, q = exp(−y/2), and d(t) = M − K(t). Use the N equally spaced "
                    + "phases indexed by j from 0 to N−1. The sum of cos((j−k)θ) over all ordered "
                    + "pairs is the squared modulus of the sum of their complex exponentials, by the frozen FejerNearCollisionBound pair-cosine identity. Under RH "
                    + "the spectral weights are positive. The square therefore bounds the combined "
                    + "midpoint defects in terms of the same central deficit d(y).")),
                Paragraph(Text(
                    "For each pair take the step byq with b = |j−k|/(2N). After division by qy², "
                    + "the cusp term tends to b/2 and the arithmetic curvature contributes at most b². "
                    + "The explicit-formula residual vanishes at this scale. Summing the first and second "
                    + "distance moments gives the coefficient (1−1/N²)/48.")),
                Paragraph(Text(
                    "For c below 1/48, choose a finite N with c below this coefficient before taking "
                    + "the real tail. For the converse, restrict the coefficients to c below 1/64 and apply "
                    + "MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap. Its converse uses c = 1/128 to force divergence of the critical gap. "
                    + "The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7070009503."))),
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
            new Formula.Fraction(D(1), D(4, 8)));
        var limit = Bind(FormulaQuantifier.ForAll, "c", ImpliesClaim(strict,
            Bind(FormulaQuantifier.Exists, "T", tail)));
        return Disp(new Formula.Logic(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            FormulaLogicOperator.Iff, limit));
    }
}
