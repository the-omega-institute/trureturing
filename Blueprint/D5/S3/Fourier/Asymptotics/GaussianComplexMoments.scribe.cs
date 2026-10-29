using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class GaussianComplexMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit complex moments of an arbitrary real Gaussian density are obtained from its entire moment generating function.",
        H("Complex Moments of a Real Gaussian Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-complex-monomial-integrability"),
                DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_monomial_integrable"),
                H("Integrability of every tilted monomial"),
                StatementSource.FromAuthor(IntegrabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real mean, positive real variance, natural degree and complex tilt, the corresponding complex Gaussian density monomial is Bochner integrable. The statement carries no moment or integrability premise beyond positivity of the variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-complex-moment-zero"),
                DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_zero"),
                H("Zeroth tilted moment"),
                StatementSource.FromAuthor(MomentFormula("zero", F.D(0), Call("gaussianMGF", F.Id("mu"), F.Id("v"), F.Id("z")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral of the tilted Gaussian density equals the explicit entire Gaussian moment generating function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-complex-moment-one"),
                DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_one"),
                H("First tilted moment"),
                StatementSource.FromAuthor(MomentFormula("one", F.D(1), Call("mul", Call("tiltedMean", F.Id("mu"), F.Id("v"), F.Id("z")), Call("gaussianMGF", F.Id("mu"), F.Id("v"), F.Id("z"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiating the entire Gaussian moment generating function once gives the exact first tilted moment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-complex-moment-two"),
                DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianComplexMoments.density_moment_two"),
                H("Second tilted moment"),
                StatementSource.FromAuthor(MomentFormula("two", F.D(2), Call("mul", Call("add", Call("pow", Call("tiltedMean", F.Id("mu"), F.Id("v"), F.Id("z")), F.D(2)), F.Id("v")), Call("gaussianMGF", F.Id("mu"), F.Id("v"), F.Id("z"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A second differentiation gives the exact second tilted moment, including the variance correction term."))),
                DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula C => F.Id("C");
    private static Formula N => F.Id("N");
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula IntegrabilityFormula()
    {
        var mu = F.Id("mu");
        var v = F.Id("v");
        var n = F.Id("n");
        var z = F.Id("z");
        return F.Disp(All("mu", R, All("v", R, Imp(F.Seq(F.D(0), F.Lt, F.Sp, v),
            All("n", N, All("z", C, Call("Integrable", Call("densityMonomial", mu, v, n, z))))))));
    }

    private static Formula MomentFormula(string _, Formula degree, Formula rhs)
    {
        var mu = F.Id("mu");
        var v = F.Id("v");
        var z = F.Id("z");
        var integrand = Call("densityMonomial", mu, v, degree, z);
        return F.Disp(All("mu", R, All("v", R, Imp(F.Seq(F.D(0), F.Lt, F.Sp, v),
            All("z", C, Eq(Call("integral", integrand), rhs))))));
    }
}
