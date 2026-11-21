using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimePowerFifthCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebyshev prime powers through the fifth root",
        H("The sixth-root correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-exponent-sum"),
                DeclarationHandle.Create(Owner + ".psi_sub_roots_eq_sum"),
                H("The common finite exponent sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t ≥ 2 and N at least the floor of log(t)/log(2), the square, cube and fifth "
                    + "cutoffs combine into a sum over exponents six through N. Each θ(t^(1/k)) is "
                    + "weighted by one minus the number of divisors of k among 2, 3 and 5. "
                    + "The coefficients at exponents two through five vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixth-root-correction"),
                DeclarationHandle.Create(Owner + ".abs_psi_sub_roots_add_theta_sixth_le"),
                H("The signed sixth-root contribution"),
                StatementSource.FromAuthor(F.Disp(SixthRootCorrection())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R(t) be ψ(t)−θ(t)−ψ(t^(1/2))−ψ(t^(1/3))−ψ(t^(1/5)).")),
                    Paragraph(Text(
                        "Use Mathlib's finite Chebyshev decomposition at each root. On a common exponent "
                        + "interval, the sum at the d-th root contains exactly the exponents divisible by d. "
                        + "The coefficient of θ(t^(1/k)) in R(t) is one minus the number of divisors of k "
                        + "among 2, 3 and 5. It vanishes at 2, 3, 4 and 5, and equals −1 at 6.")),
                    Paragraph(Text(
                        "From exponent seven onward its absolute value is at most two. Chebyshev's "
                        + "linear upper bound for θ gives a bound of log(4) times t^(1/7) per term "
                        + "before multiplying by the coefficient. There are at most log(t)/log(2) terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-sixth-root-bound"),
                DeclarationHandle.Create(Owner + ".exists_abs_psi_sub_roots_le"),
                H("A uniform bound for real cutoffs"),
                StatementSource.FromAuthor(F.Disp(UniformBound())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inequality log(t) ≤ 42 t^(1/42) brings the tail to sixth-root scale. "
                    + "The triangle inequality and the linear upper bound for θ then give "
                    + "the constant log(4)+168 for every real cutoff t ≥ 2."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [x]);

    private static Formula Root(Formula t, byte d) =>
        new Formula.Power(t, new Formula.Fraction(F.D(1), F.D(d)));

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula ForCutoffs(Formula t, Formula estimate) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"),
            F.Seq(F.Mathbb, F.Grp(F.Id("R"))),
            new Formula.Logic(Le(F.D(2), t), FormulaLogicOperator.Implies, estimate));

    private static Formula SixthRootCorrection()
    {
        var t = F.Id("t");
        var sixth = new Formula.Apply(F.Theta, [Root(t, 6)]);
        var corrected = F.Seq(Call("R", t), F.Plus, sixth);
        var tail = Multiply(Multiply(F.D(4), Call("log", t)), Root(t, 7));
        return ForCutoffs(t, Le(new Formula.Absolute(corrected), tail));
    }

    private static Formula UniformBound()
    {
        var t = F.Id("t");
        var c = F.Id("C");
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, c);
        var bound = Le(new Formula.Absolute(Call("R", t)), Multiply(c, Root(t, 6)));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("C"),
            F.Seq(F.Mathbb, F.Grp(F.Id("R"))),
            new Formula.Logic(positive, FormulaLogicOperator.And, ForCutoffs(t, bound)));
    }
}
