using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class TwoHarmonicBoundaryBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three boundary values of a positive Laplace transform give a lower bound at zero frequency.",
        H("Two-harmonic boundary budget"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-harmonic-boundary-budget"),
            DeclarationHandle.Create("D5/S3/Analytic/Laplace/TwoHarmonicBoundaryBudget.two_harmonic_boundary_budget"),
            H("Lower bound from the first two harmonics"),
            StatementSource.FromAuthor(BoundaryBound()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let μ be a positive measure on the real line and let γ be real. "
                    + "For every σ > 0 assume that y ↦ exp(−σy) is μ-integrable. "
                    + "Define A(σ,t) as σ times the integral of exp(−(σ+it)y) against μ. "
                    + "Assume the three right-hand limits in the display, with complex values "
                    + "z₀, z₁ and z₂.")),
                Paragraph(Text("Conjugacy supplies the negative frequencies. Apply boundary Gram "
                    + "positivity at 0, γ and 2γ with coefficients u, vw and uw², where w has "
                    + "unit norm. When a = ‖z₁‖ is positive, choose w so that wz₁ = −a. "
                    + "Writing b = ‖z₂‖ and λ for the displayed lower bound, the choice "
                    + "u = λ and v = 2a gives the estimate by λ² + bλ = 2a². For a = 0, "
                    + "the middle coefficient alone gives the bound. For z₂ = 0, the lower "
                    + "bound simplifies to √2 ‖z₁‖."))),
            DescribeRole.Theorem))));

    private static Formula BoundaryBound()
    {
        var sigma = F.SigmaLower;
        var gamma = F.GammaLower;
        var zero = F.D(0);
        var two = F.D(2);
        var z0 = new Formula.Subscript(F.Id("z"), zero);
        var z1 = new Formula.Subscript(F.Id("z"), F.D(1));
        var z2 = new Formula.Subscript(F.Id("z"), two);
        var y = F.Id("y");
        var density = F.Seq(y, F.Sp, F.Mapsto, F.Sp, F.Exp, F.Open, F.Minus,
            Multiply(sigma, y), F.Close);
        var l1 = new Formula.Apply(new Formula.Power(F.Id("L"), F.D(1)), [F.Mu]);
        var integrable = F.Seq(F.Forall, F.Sp, sigma, F.Sp, F.Gt, F.Sp, zero, F.Comma,
            F.Quad, F.Open, density, F.Close, F.Sp, F.InMacro, F.Sp, l1);
        var rightLimit = new Formula.Subscript(F.Lim, F.Seq(sigma, F.To, new Formula.Power(zero, F.Plus)));
        Formula Limit(Formula t, Formula z) => new Formula.Relation(
            F.Seq(rightLimit, F.Sp, new Formula.Apply(F.Id("A"), [sigma, t])),
            FormulaRelationOperator.Equal, z);

        var a = new Formula.Norm(z1);
        var b = new Formula.Norm(z2);
        var radicand = Add(new Formula.Power(b, two), Multiply(F.D(8), new Formula.Power(a, two)));
        var numerator = F.Seq(F.Sqrt, F.Grp(radicand), F.Sp, F.Minus, F.Sp, b);
        var bound = new Formula.Relation(new Formula.Fraction(numerator, two),
            FormulaRelationOperator.LessThanOrEqual, F.Seq(F.Re, F.Open, z0, F.Close));
        return F.Disp(new Formula.Aligned([
            integrable,
            F.Seq(Limit(zero, z0), F.Comma, F.Quad, Limit(gamma, z1), F.Comma, F.Quad,
                Limit(Multiply(two, gamma), z2)),
            F.Seq(F.Longrightarrow, F.Sp, bound)
        ]));
    }
}
