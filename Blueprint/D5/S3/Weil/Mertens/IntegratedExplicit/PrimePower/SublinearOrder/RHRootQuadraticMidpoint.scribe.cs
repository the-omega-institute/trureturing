using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootQuadraticMidpointDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuadraticMidpoint";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic midpoint remainder of the exponential root average",
        H("Pairing the weighted modes"),
        Blocks(Describe.Lean(DescribeId.Create("root-signal-exponential-midpoint-quadratic"),
            DeclarationHandle.Create(Owner + ".root_signal_exponential_midpoint_quadratic"),
            H("Uniform midpoint estimate and signed origin bound"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let S be the centered root spectrum with every actual zero "
                    + "occurrence. For s(r)=1/2−1/(2r), let M(r,u,L) be the average of "
                    + "S(r,u+t) on [0,L] with density proportional to exp(−s(r)t), minus "
                    + "S(r,u+L/2). Put c=(Euler's constant−1+log(2π))/2. The profile "
                    + "G(r,L) is L/(8s(r)) times log(1/L)+log(2r)−2c+1/2, and "
                    + "E(C,L)=C L².")),
                Paragraph(Text("For frequency ω and half-displacement h, put q=1−cos(ωh). "
                    + "The half-pair multiplier is −cosh(sh)q−i sinh(sh)sin(ωh). Its squared "
                    + "norm is q²+2q sinh²(sh), so its norm is at most q+sinh²(sh). The sum "
                    + "of the q terms is bounded by the full cosine kernel, and the sum "
                    + "of the frequency-independent terms is bounded by the absolute "
                    + "coefficient mass times sinh²(sh). This controls every starting point.")),
                Paragraph(Text("At center zero, the paired integrand is the symmetric "
                    + "increment times cosh(sh) minus the odd increment times sinh(sh). "
                    + "The symmetric cusp and the linear odd-increment bound give the signed "
                    + "lower comparison. The centered denominator is the integral of 2 cosh(sh) "
                    + "on [0,L/2], which differs from L by at most L³ on the stated range. "
                    + "Integrating the cusp profile gives the 1/2 in G."))),
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
        var u = Id("u");
        var width = Id("L");
        var constant = Id("C");
        var leading = Call("G", r, width);
        var error = Call("E", constant, width);
        var half = new Formula.Fraction(width, Num(2));
        var centeredStart = Subtract(Num(0), half);
        var upper = All("u", Le(new Formula.Absolute(Call("M", r, u, width)), Add(leading, error)));
        var lower = Le(Subtract(leading, error), Call("M", r, centeredStart, width));
        var widths = All("L", Imp(And(Lt(Num(0), width),
            Le(width, new Formula.Fraction(Num(1), Num(4)))), And(upper, lower)));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(Num(1), r),
            Exists("C", And(Lt(Num(0), constant), widths))))));
    }
}
