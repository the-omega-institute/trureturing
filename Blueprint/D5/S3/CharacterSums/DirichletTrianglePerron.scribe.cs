using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletTrianglePerronDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletTrianglePerron.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laplace and Perron formulas for triangular character sums",
        H("Triangular smoothing of the Mangoldt coefficients"),
        Blocks(
            Paragraph(Text("For a complex Dirichlet character χ modulo q, define Sχ(x) as the "
                + "sum of Λ(n)χ(n)(1−n/x) over 1 ≤ n ≤ floor(x). An entering integer has zero "
                + "weight. Write hχ(s) for the logarithmic derivative of L(s,χ). Principal "
                + "characters and imprimitive characters are included. Let Kχ(x,c,t) be "
                + "−hχ(c+it)x^(c+it)/((c+it)(c+1+it)).")),
            Entry("laplace-integrability", "characterTriangle_laplace_integrable",
                "Absolute convergence of the Laplace transform",
                Call("IntegrableOn", Call("Lkernel", F.Id("s")), Call("Ioi", F.D(0))),
                "For every modulus q, every χ and Re(s)>1, the function "
                + "y ↦ exp(−sy)Sχ(exp(y)) is integrable on y>0. This assertion does not "
                + "require q to be positive. Multiply the individual Mangoldt ramp at "
                + "exp(y) by n exp(−y). At σ=Re(s), the integral of its norm is the real "
                + "part of its positive Laplace transform. The von Mangoldt Dirichlet "
                + "series at σ makes these integrals summable. The bound |χ(n)|≤1 "
                + "preserves absolute summability. Tonelli controls the infinite sum."),
            Entry("laplace-identity", "characterTriangle_laplace",
                "The Laplace identity for every character",
                Eq(Laplace(), new Formula.Fraction(
                    new Formula.Negate(Call("hchi", F.Id("s"))),
                    Mul(F.Id("s"), Add(F.Id("s"), F.D(1))))),
                "For q>0 and Re(s)>1 the displayed integral is −hχ(s)/(s(s+1)). "
                + "The single atom is evaluated by the Mangoldt ramp transform at s+1, "
                + "multiplied by n. Absolute convergence justifies the exchange with "
                + "the series. Its coefficient series is the character twist of Λ, "
                + "whose sum is the negative logarithmic derivative of the L-function. "
                + "Positive modulus is required by the L-function interface."),
            Entry("vertical-integrability", "trianglePerronIntegrand_integrable",
                "Absolute convergence on every vertical line to the right of one",
                Call("Integrable", Call("Kchi", F.Id("x"), F.Id("c"))),
                "For q>0, x≥0 and c>1, Kχ(x,c,·) is integrable on the whole real line. "
                + "Use the absolutely convergent coefficient series on Re(s)=c. The "
                + "norm of each Dirichlet term is independent of the imaginary part. "
                + "The integrable smoothed Perron kernel makes the term norm integrals "
                + "summable. Division by x changes the linear smoothing to triangular "
                + "smoothing and preserves integrability."),
            Entry("perron-identity", "characterTriangle_perron",
                "The classical Perron formula with triangular weight",
                Eq(Call("Schi", F.Id("x")),
                    Mul(new Formula.Fraction(F.D(1), Mul(F.D(2), F.Pi)), Perron())),
                "For q>0, x≥0 and c>1, Sχ(x) equals (2π)⁻¹ times the integral of "
                + "Kχ(x,c,t) over the real line. This is the triangular form of the "
                + "classical smoothed Perron formula. Apply the existing general "
                + "L-series formula to χ(n)Λ(n), then divide by x and use "
                + "x^(s+1)=x x^s. The positive endpoint allows this division and "
                + "the complex power identity. The result includes 0≤x≤1 and the "
                + "line c=2. At x=0 the kernel and the finite sum both vanish. "
                + "The separate integrability statement supplies absolute "
                + "convergence of the displayed integral."),
            Entry("integer-endpoint", "characterTriangle_nat",
                "Agreement with the character sieve at integer endpoints",
                Eq(Call("Schi", F.Id("p")), Call("Mchi", F.Id("p"))),
                "For every natural p and character χ modulo p, Sχ(p) equals "
                + "smoothedCharacterSum p χ. The latter sums over n<p. The term at "
                + "n=0 vanishes because Λ(0)=0, and the term at n=p vanishes because "
                + "its triangular weight is zero. The equality includes p=0."))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula Laplace() => F.Seq(
        F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(F.Infty), F.Sp,
        Mul(Call("exp", new Formula.Negate(Mul(F.Id("s"), F.Id("y")))),
            Call("Schi", Call("exp", F.Id("y")))), F.Sp, F.Id("d"), F.Id("y"));

    private static Formula Perron() => F.Seq(
        F.Int, F.Underscore, F.Grp(new Formula.Negate(F.Infty)),
        F.Caret, F.Grp(F.Infty), F.Sp,
        Call("Kchi", F.Id("x"), F.Id("c"), F.Id("t")), F.Sp, F.Id("d"), F.Id("t"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Mul(Formula left, Formula right) => Multiply(left, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
