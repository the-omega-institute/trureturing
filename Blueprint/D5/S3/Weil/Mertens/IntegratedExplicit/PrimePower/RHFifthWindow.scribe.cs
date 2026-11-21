using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RHFifthWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fifth-root coefficient in RH prime windows",
        H("Fifth-root correction at both endpoints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fifth-prime-power-window"),
                DeclarationHandle.Create(Owner + ".prime_window_fifth_of_rh"),
                H("A uniform remainder at the third-power decay rate"),
                StatementSource.FromAuthor(WindowEstimate()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R(a,B) be the signed error in the cube and square correction. "
                        + "Start with the integral of the negative part of the prime-only tail divided by sqrt(x). "
                        + "Subtract 2 log(B/a), the ordinary zero primitive at B minus its value at a, "
                        + "the cube term, and the square-cutoff primitive at B minus its value at a. "
                        + "Both spectral primitives use the actual zero occurrences with multiplicity.")),
                    Paragraph(Text("The Chebyshev difference after subtraction of the square, cube and fifth "
                        + "cutoffs is of sixth-root order by finite prime-power cancellation. "
                        + "After tail integration against t^(-2) and multiplication by sqrt(x), "
                        + "this error is of order x^(-1/3). The fifth uncentered root contributes "
                        + "(5/4)x^(-3/10). The centered fifth root contributes at order x^(-2/5) under RH.")),
                    Paragraph(Text("Eventual positivity permits the use of the signed prime-only density. "
                        + "Integrating the fifth-root density on the same log interval gives 25/6 times "
                        + "the negative three-tenths power difference. Integrating the remaining "
                        + "majorant gives the negative one-third power difference. Both terms vanish at B=a."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Difference(Formula a, Formula b, Formula numerator, Formula denominator)
    {
        var power = new Formula.Negate(new Formula.Fraction(numerator, denominator));
        return Subtract(new Formula.Power(a, power), new Formula.Power(b, power));
    }

    private static Formula WindowEstimate()
    {
        var a = F.Id("a");
        var b = F.Id("B");
        var threshold = F.Id("T");
        var k = F.Id("K");
        var residual = new Formula.FunctionCall(FormulaIdentifier.Create("R"), [a, b]);
        var fifth = Multiply(new Formula.Fraction(F.Seq(F.D(2), F.D(5)), F.D(6)),
            Difference(a, b, F.D(3), F.Seq(F.D(1), F.D(0))));
        var error = Multiply(k, Difference(a, b, F.D(1), F.D(3)));
        var bound = Le(new Formula.Absolute(Subtract(residual, fifth)), error);
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, k);
        return F.Disp(Imp(F.Id("RH"), Exists("T", Exists("K",
            And(Le(F.D(2), threshold), And(positive, All("a", All("B",
                Imp(And(Le(threshold, a), Le(a, b)), bound)))))))));
    }
}
