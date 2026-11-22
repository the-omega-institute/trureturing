using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class JSpatialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed J chart regularization and spatial displacement",
        H("Signed J chart regularization and spatial displacement"),
        Blocks(
            Describe.Lean(DescribeId.Create("g"), DeclarationHandle.Create(Prefix + "G"),
                H("Signed chart denominator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean labels e and f and complex u and v, G(e,f,u,v) is "
                    + "u − v for equal labels and 1 − uv for mixed labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-j"), DeclarationHandle.Create(Prefix + "rationalJ"),
                H("Rational J factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean e and f and complex u, v and r, rationalJ equals "
                    + "Qconstant(e,f,r) + jN(e,f,u,v,r)/(2G(e,f,u,v)²). The offset is 0 for (++), "
                    + "and r/2 for the other three sign pairs. The numerator jN is "
                    + "u h(e,u,r)b(v) + v b(u)h(f,v,r) for equal labels. For (+−) it is "
                    + "−(h(e,u,r)b(v) + uv b(u)h(f,v,r)), and for (−+) it is "
                    + "−(uv h(e,u,r)b(v) + b(u)h(f,v,r))."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cauchy"), DeclarationHandle.Create(Prefix + "cauchy"),
                H("Signed Cauchy subtraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean e and f and complex u and v, cauchy(e,f,u,v) "
                    + "is ρ(e,f,u,v)/(2G(e,f,u,v)²). Its numerator is u + v for equal labels "
                    + "and −(1 + uv) for mixed labels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chart-j"), DeclarationHandle.Create(Prefix + "chartJ"),
                H("J expressed in the rational chart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chart evaluates the product of the two original signed sources times "
                    + "the difference rationalJ(e,f,u,v,r) − correction(r), then subtracts cauchy(e,f,u,v). "
                    + "On ‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1 with G ≠ 0, the root-square and source "
                    + "normalization identities reduce this expression to the regular candidateJ."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-j-chart-algebra"),
                DeclarationHandle.Create(Prefix + "regularJ_chart_algebra"),
                H("Regular J for normalized chart roots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let e and f be Boolean labels and let u, v, r, me, mf, U and V be "
                        + "complex, with me and mf denoting the two source factors. Assume "
                        + "U² b(u) = h(e,u,r), V² b(v) = h(f,v,r), me b(u) U = 1 and mf b(v) V = 1. "
                        + "The equality holds on this domain with b(u) ≠ 0, b(v) ≠ 0, U ≠ 0, V ≠ 0, "
                        + "G(e,f,u,v) ≠ 0 and U + V ≠ 0.")),
                    new DocumentBlock.DisplayFormula(RegularJChartIdentity())),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("candidate-j-original-displacement"),
                DeclarationHandle.Create(Prefix + "candidateJ_original_displacement"),
                H("Signed J displacement with the original source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all Boolean e and f, complex u and v, and real 0 < r < 1 with "
                        + "‖u‖ + √r < 1 and ‖v‖ + √r < 1, set x = (r : ℂ), "
                        + "λ = shiftedCentralDerivative(x,0)/period(x), and C(u,v) = candidateJ(e,f,u,v,x). "
                        + "The sum modeScale(f,v)L(e,C(·,v),u) + modeScale(e,u)L(f,C(u,·),v) equals "
                        + "(1 − x) sourceMode(e,u,x) sourceMode(f,v,x) "
                        + "[modeA(e,u,x)modeH(f,v,x,λ) + modeH(e,u,x,λ)modeA(f,v,x)]/2 "
                        + "+ modeB(e)modeB(f).")),
                    Paragraph(Text("Off the chart pole, the rational derivative gives A(e)D(f) + D(e)A(f) "
                        + "− 2A(e)A(f), with the D factor −ru/h(e,u,r) for the positive label and +ru/h(e,u,r) "
                        + "for the negative label. The period correction converts this to the "
                        + "A and H sum. The spatial operator on cauchy gives −modeB(e)modeB(f), so the "
                        + "subtraction contributes +modeB(e)modeB(f). This is 1/4 for equal labels and "
                        + "−1/4 for mixed labels.")),
                    Paragraph(Text("For mixed labels, ‖uv‖ < 1 excludes chart poles. For equal labels, joint "
                        + "analyticity of the regular candidate makes its two complex partial derivatives "
                        + "continuous at u = v. With the second coordinate fixed, the equation extends "
                        + "to the diagonal by continuity from the punctured first-coordinate disk."))),
                DescribeRole.Theorem))));

    private static Formula RegularJChartIdentity()
    {
        var e = Id("e");
        var f = Id("f");
        var u = Id("u");
        var v = Id("v");
        var r = Id("r");
        var sourceProduct = Multiply(Id("me"), Id("mf"));
        var rootSumSquared = new Formula.Power(Add(Id("U"), Id("V")), Num(2));
        var numerator = Multiply(new Formula.Power(r, Num(2)), new Formula.Apply(FormulaDsl.Rho, [e, f, u, v]));
        var denominator = Multiply(Multiply(Multiply(Num(4), Call("b", u)), Call("b", v)), rootSumSquared);
        return Equal(
            Subtract(Multiply(sourceProduct, Call("rationalJ", e, f, u, v, r)), Call("cauchy", e, f, u, v)),
            Multiply(sourceProduct, Add(new Formula.Fraction(r, Num(4)), new Formula.Fraction(numerator, denominator))));
    }
}
