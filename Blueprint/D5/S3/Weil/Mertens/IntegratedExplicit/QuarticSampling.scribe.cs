using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class QuarticSamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Testing the Riemann hypothesis at fourth powers",
        H("A sparse test for the integrated Mangoldt remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("quartic-sampling"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_eventually_quartic_samples"),
            H("The fourth-power sampling criterion"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The remainder U is CompleteMertensPeak.U with its inclusive natural-floor sum. "
                    + "Under RH the normalized remainder G is eventually smaller in absolute value than one, "
                    + "since its limiting envelope is at most the first Li mass, which is less than one. "
                    + "Substitution of 4 log n gives the strict bound at all sufficiently large fourth powers.")),
                Paragraph(Text(
                    "Conversely, put a = n⁴ and b = (n+1)⁴. Each Mangoldt ramp is a nonnegative multiple "
                    + "of the maximum of an affine function and zero, so the complete ramp sum lies below its "
                    + "endpoint chord. The nonlinear centering contributes at most (b−a)²/a. This follows "
                    + "by subtracting the tangent of z log z at a, then bounding the excess at b using "
                    + "log(b/a) ≤ b/a−1. For n ≥ 1 the gap is at most 15n³ and (n+1)² ≤ 4n². "
                    + "The sampled bounds therefore imply U(x) ≤ 229n² between adjacent samples.")),
                Paragraph(Text(
                    "Those intervals cover the entire tail. The normalized arithmetic kernel is eventually "
                    + "at most 230 after including the trivial-zero correction. Its affine-tail implication "
                    + "gives RH. The resulting equivalence leaves the arithmetic sample inequality to be proved."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var n = F.Id("n");
        var threshold = F.Id("N");
        Formula Power(int d) => F.Seq(n, F.Caret, F.Grp(F.D(d)));
        var sample = new Formula.Relation(new Formula.Apply(F.Id("U"), [Power(4)]),
            FormulaRelationOperator.LessThan, Power(2));
        var tail = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), natural,
            new Formula.Logic(new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies, sample));
        return F.Disp(new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("N"), natural, tail)));
    }
}
