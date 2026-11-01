using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FourPathQuadraticMajorantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic majorant for the four-path record at every complex pair.",
        H("Four-path quadratic majorant"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-path-quadratic-majorant"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FourPathQuadraticMajorant.four_path_quadratic_majorant"),
            H("The complete complex quadratic majorant"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The variables xi and eta range independently over all complex numbers. The constants are the actual cosine and sine of pi/8; i denotes the imaginary unit and norm denotes complex modulus. The estimate includes the zero pair, both coordinate axes, every relative phase and every scale.")),
                Paragraph(Text("For nonnegative u and v with u squared plus v squared equal to two, the paired response u+v is at most 2-(u squared-v squared) squared/16. Applying this estimate to the two pairs of norms retains separate deficits in the real and imaginary parts of xi times the conjugate of eta.")),
                Paragraph(Text("After normalization, put p=|xi| squared, q=|eta| squared, x=Re(xi conjugate(eta)), y=Im(xi conjugate(eta)), a=sqrt(c squared p+s squared q), m=cp+sq and L=sqrt(2+4a squared+4sqrt(2)m). Then x squared+y squared=pq. The two deficits are x squared/sqrt(2) and y squared/(8a cubed).")),
                Paragraph(Text("The difference sqrt(2)+2a-L equals 4sqrt(2)(c-s) squared pq divided by (a+m)(sqrt(2)+2a+L). Lower bounds on this positive denominator make the difference at most each of pq/sqrt(2) and pq/(8a cubed). The second bound uses m at least 9a/10 and positivity on [0,15/16] of the concave polynomial 19sqrt(2)/5+361t/50-32(sqrt(2)-1)t squared. Combining the complementary deficits gives the required bound by L. Squaring and homogeneous rescaling prove the displayed inequality.")),
                Paragraph(Text("This estimate is the pointwise analytic ingredient in the four-path full-record recovery bound. It does not assert a channel diamond optimum or an attaining feedback protocol."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);
    private static Formula Sq(Formula value) => new Formula.Power(value, Num(2));
    private static Formula Norm(Formula value) => Call("norm", value);

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula xi = F.Id("xi"), eta = F.Id("eta");
        Formula angle = Div(Pi, Num(8));
        Formula c = Call("cos", angle), s = Call("sin", angle);
        Formula r = Call("sqrt", Num(2));
        Formula imaginary = F.Id("i");
        Formula first = Div(Add(Norm(Add(xi, eta)), Norm(Sub(xi, eta))), r);
        Formula realPart = Mul(c, xi), imaginaryPart = Mul(Mul(imaginary, s), eta);
        Formula left = Sq(Add(Add(first, Norm(Add(realPart, imaginaryPart))),
            Norm(Sub(realPart, imaginaryPart))));
        Formula right = Add(Mul(Sq(Add(r, Mul(Num(2), c))), Sq(Norm(xi))),
            Mul(Sq(Add(r, Mul(Num(2), s))), Sq(Norm(eta))));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("xi"), complex),
             new Formula.BoundVariable(FormulaIdentifier.Create("eta"), complex)],
            new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right)));
    }
}
