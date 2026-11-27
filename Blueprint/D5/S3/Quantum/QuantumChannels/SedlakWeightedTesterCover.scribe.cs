using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SedlakWeightedTesterCoverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An effect-weighted joint cover bounds the incompatibility of finite one-step testers.",
        H("Effect-weighted tester incompatibility"),
        Blocks(
            Paragraph(Text(
                "Let A and B be finite one-step testers with positive output dimension and input density matrices "
                + "ρ and σ. The effects are positive semidefinite and their respective sums are I ⊗ ρ and I ⊗ σ.")),
            Describe.Lean(DescribeId.Create("weighted-joint-cover"),
                DeclarationHandle.Create(Module + ".weightedJointCover"),
                H("Positive weighted joint cover"), Hand(CoverFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose nonnegative upper bounds αⱼ and βₖ in the positive operator order for the effects. "
                    + "Their totals a and b are positive. The cover entries use the normalized weights βₖ/b and "
                    + "αⱼ/a to distribute the two effects before subtracting the symmetrized product. "
                    + "Completing a positive sandwich with the opposite lifted normalization state proves "
                    + "marginal domination. The displayed H is the input normalization of the joint sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robustness-operator-norm"),
                DeclarationHandle.Create(Module + ".opNormRobustnessBound"),
                H("Overlap and operator-norm bound"), Hand(RobustnessFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the Euclidean operator norm of each effect for its weight. A positive effect is bounded "
                    + "in operator order by its operator norm times the identity. At ε = δ/(a + b), the cover has "
                    + "normalization trace t. Dividing the cover and using its marginal slacks yields a feasible "
                    + "mixing weight 1 − 1/t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proportional-refinement"),
                DeclarationHandle.Create(Module + ".sum_effect_norm_refinement"),
                H("Invariance under proportional effect refinement"), Hand(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each effect Aⱼ, take finitely many nonnegative real coefficients θⱼₗ summing to one. "
                    + "Absolute homogeneity of the operator norm preserves the total when Aⱼ is replaced by "
                    + "the family θⱼₗ Aⱼ. The resulting denominator is the same for either tester before and "
                    + "after proportional refinements."))),
                DescribeRole.Theorem))));

    private static Formula CoverFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var j = F.Id("j");
        var k = F.Id("k");
        var x = Sub(F.Id("A"), j);
        var y = Sub(F.Id("B"), k);
        var scaleA = Par(Seq(D(1), Plus, a, Sq(Varepsilon)));
        var scaleB = Par(Seq(D(1), Plus, b, Sq(Varepsilon)));
        return new Formula.Aligned([
            Seq(D(0), Amp, Leq, Varepsilon, Leq, Min, Par(Seq(Inv(a), Comma, Inv(b)))),
            Seq(Sub(F.Id("C"), Seq(j, k)), Amp, Eq, scaleA, Div(Sub(Beta, k), b), x, Plus,
                scaleB, Div(Sub(Alpha, j), a), y, Minus, Varepsilon, Par(Seq(x, y, Plus, y, x))),
            Seq(F.Id("H"), Amp, Eq, scaleA, Rho, Plus, scaleB, SigmaLower, Minus, Varepsilon,
                Par(Seq(Rho, SigmaLower, Plus, SigmaLower, Rho))),
        ]);
    }

    private static Formula RobustnessFormula()
    {
        var j = F.Id("j");
        var k = F.Id("k");
        var t = F.Id("t");
        var r = new Formula.Apply(Sub(F.Id("R"), F.Id("t")), [F.Id("A"), F.Id("B")]);
        return new Formula.Aligned([
            Seq(DeltaLower, Amp, Eq, Re, Sp, new Formula.Apply(
                Seq(Operatorname, Grp(F.Id("tr"))), [Seq(Rho, SigmaLower)])),
            Seq(F.Id("a"), Amp, Eq, Sub(Sum, j), new Formula.Norm(Sub(F.Id("A"), j)), Quad, Sp,
                F.Id("b"), Eq, Sub(Sum, k), new Formula.Norm(Sub(F.Id("B"), k))),
            Seq(t, Amp, Eq, D(2), Minus, Div(Sq(DeltaLower), Seq(F.Id("a"), Plus, F.Id("b")))),
            Seq(r, Amp, Leq, Sp, D(1), Minus, Inv(t)),
        ]);
    }

    private static Formula RefinementFormula()
    {
        var j = F.Id("j");
        var l = F.Id("l");
        var a = Sub(F.Id("A"), j);
        return Seq(Sub(Sum, Seq(j, Comma, l)), new Formula.Norm(Seq(Sub(Theta, Seq(j, l)), a)),
            Eq, Sub(Sum, j), new Formula.Norm(a));
    }

    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Inv(Formula value) => new Formula.Power(value, Seq(Minus, D(1)));
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static StatementSource Hand(Formula formula) => StatementSource.FromAuthor(Disp(formula));
}
