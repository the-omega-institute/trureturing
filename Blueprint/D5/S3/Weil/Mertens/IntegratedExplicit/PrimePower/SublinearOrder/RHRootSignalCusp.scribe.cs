using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootSignalCuspDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootSignalCusp";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic cusp of the centered root spectrum",
        H("The logarithmic cusp of the centered root spectrum"),
        Blocks(Describe.Lean(DescribeId.Create("root-signal-symmetric-cusp"),
            DeclarationHandle.Create(Owner + ".root_signal_symmetric_cusp"),
            H("The symmetric difference at the origin"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For r greater than one, put s(r)=1/2−1/(2r) and "
                    + "c=(Euler's constant−1+log(2π))/2. The centered signal S(r,u) is the "
                    + "real part of the root series divided by s(r), with each actual zero "
                    + "included according to its analytic multiplicity.")),
                Paragraph(Text("For a zero of ordinate γ, the symmetric difference multiplies "
                    + "the real coefficient by 2(cos(γh/r)−1). Subtract the reference coefficient "
                    + "−r/(1/4+γ²). The correction has another quadratic denominator in γ, "
                    + "so its second ordinate moment is bounded by the total reciprocal-square "
                    + "mass. This gives a quadratic bound for the correction series.")),
                Paragraph(Text("The reference series equals the actual cosine kernel difference "
                    + "at h/r, scaled by −2r/s(r). Substituting the kernel expansion gives both "
                    + "cusp coefficients. The estimate describes the symmetric difference about "
                    + "the origin. The sharp uniform modulus over arbitrary starting points is open."))),
            DescribeRole.Theorem))));

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Reals(), body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Reals(), body);

    private static Formula Statement()
    {
        var r = Id("r");
        var h = Id("h");
        var bound = Id("C");
        var zero = Num(0);
        var two = Num(2);
        var bilat = Subtract(Add(Call("S", r, h), Call("S", r, new Formula.Negate(h))),
            Multiply(two, Call("S", r, zero)));
        var logarithms = Subtract(Add(Call("log", new Formula.Fraction(Num(1), h)),
            Call("log", r)), Multiply(two, Id("c")));
        var leading = Multiply(new Formula.Fraction(h, Call("s", r)), logarithms);
        var estimate = Le(new Formula.Absolute(Subtract(bilat, leading)),
            Multiply(bound, Multiply(h, h)));
        var increments = All("h", Imp(And(Lt(zero, h), Le(h, new Formula.Fraction(r, two))),
            estimate));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(Num(1), r),
            Exists("C", And(Lt(zero, bound), increments))))));
    }
}
