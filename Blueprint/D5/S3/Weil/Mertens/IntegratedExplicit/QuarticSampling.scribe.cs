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
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quartic-power-windows"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_power_windows"),
                H("Finite fourth-power samples on arbitrarily late closed windows"),
                StatementSource.FromAuthor(Window()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Y ≥ 2 and Z ≥ Y, S(Y,Z) consists of Y, Z and every "
                    + "natural fourth power n⁴ with Y ≤ n⁴ ≤ Z. These finitely many samples allow "
                    + "arbitrary real endpoints. The window may depend on the exponent loss and the "
                    + "requested lower bound on its starting point.")),
                    Paragraph(Text("For each x in the window, clip the fourth-power cell containing x "
                        + "to the window. Both ends of the clipped interval belong to S(Y,Z). "
                        + "Its chord error is at most 225√x and each sampled power bound is at most "
                        + "16xᵖ for 1/2 ≤ p ≤ 1. This gives U(x) ≤ 241xᵖ throughout the window. "
                        + "Choose a smaller positive loss and move the window far enough to absorb 241. "
                        + "The whole-window power criterion then gives RH. The forward implication "
                        + "restricts that criterion to the sample points."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quartic-integer-blocks"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.rh_iff_quartic_integer_blocks"),
                H("Sampling on finite integer blocks"), StatementSource.FromAuthor(IntegerBlocks()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For each positive exponent loss and each natural threshold A, the test asks for a "
                    + "natural k at least max(A,2). At this k it tests all fourth powers n⁴ with integer "
                    + "root between k³ and k⁴, including both boundary roots. Under RH the strict "
                    + "quartic tail estimate supplies the tests for every sufficiently large k.")),
                    Paragraph(Text("Conversely, choose the real window with left end k¹² and power "
                        + "exponent 4/3. Its right end is k¹⁶. The boundary roots are k³ and k⁴, "
                        + "and monotonicity of the fourth power places every interior sample root "
                        + "between them. Such windows start arbitrarily far out, so they satisfy "
                        + "the closed-window criterion at every positive loss."))), DescribeRole.Theorem))));

    private static Formula Window()
    {
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var b = F.Id("b");
        var k = F.Id("k");
        var y = F.Id("Y");
        var t = F.Id("t");
        Formula Bind(FormulaQuantifier q, string name, Formula body) =>
            new Formula.Bind(q, FormulaIdentifier.Create(name), reals, body);
        Formula Le(Formula a, Formula z) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, z);
        Formula Lt(Formula a, Formula z) => new Formula.Relation(a, FormulaRelationOperator.LessThan, z);
        Formula Implies(Formula a, Formula z) => new Formula.Logic(a, FormulaLogicOperator.Implies, z);
        Formula Power(Formula x, Formula e) => F.Seq(x, F.Caret, F.Grp(e));
        Formula At(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
        var p = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)), F.Plus, k);
        var sample = F.Seq(t, F.Sp, F.InMacro, F.Sp, At("S", y, Power(y, b)));
        var tests = Bind(FormulaQuantifier.ForAll, "t", Implies(sample, Le(At("U", t), Power(t, p))));
        var late = Bind(FormulaQuantifier.ForAll, "R", Bind(FormulaQuantifier.Exists, "Y",
            new Formula.Logic(Le(At("max", F.Id("R"), F.D(2)), y), FormulaLogicOperator.And, tests)));
        var right = Bind(FormulaQuantifier.ForAll, "k", Implies(Lt(F.D(0), k), late));
        return F.Disp(Bind(FormulaQuantifier.ForAll, "b", Implies(Lt(F.D(1), b),
            new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff, right))));
    }

    private static Formula IntegerBlocks()
    {
        var natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var k = F.Id("k");
        var n = F.Id("n");
        var loss = F.Id("e");
        Formula Power(Formula x, Formula e) => F.Seq(x, F.Caret, F.Grp(e));
        Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
        Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
        Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
        Formula Bind(FormulaQuantifier q, string name, Formula domain, Formula body) =>
            new Formula.Bind(q, FormulaIdentifier.Create(name), domain, body);
        var x = Power(n, F.D(4));
        var degree = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)), F.Plus, loss);
        var sample = Le(new Formula.Apply(F.Id("U"), [x]), Power(F.Seq(F.Open, x, F.Close), degree));
        var roots = And(Le(Power(k, F.D(3)), n), Le(n, Power(k, F.D(4))));
        var block = Bind(FormulaQuantifier.ForAll, "n", natural, Implies(roots, sample));
        var threshold = new Formula.FunctionCall(FormulaIdentifier.Create("max"), [F.Id("A"), F.D(2)]);
        var late = Bind(FormulaQuantifier.ForAll, "A", natural,
            Bind(FormulaQuantifier.Exists, "k", natural, And(Le(threshold, k), block)));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, loss);
        var right = Bind(FormulaQuantifier.ForAll, "e", reals, Implies(positive, late));
        return F.Disp(new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff, right));
    }

    private static Formula Claim()
    {
        var natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var n = F.Id("n");
        var threshold = F.Id("N");
        Formula Power(byte d) => F.Seq(n, F.Caret, F.Grp(F.D(d)));
        var sample = new Formula.Relation(new Formula.Apply(F.Id("U"), [Power(4)]),
            FormulaRelationOperator.LessThan, Power(2));
        var tail = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), natural,
            new Formula.Logic(new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies, sample));
        return F.Disp(new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("N"), natural, tail)));
    }
}
