using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StaticExchange;

internal sealed class DipoleTwoDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/StaticExchange/DipoleTwoDistance.";

    private static Formula At(string name, params Formula[] argument) =>
        Seq(F.Id(name), Open, Seq(argument), Close);

    private static Formula Minor()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var a = F.Id("a");
        var b = F.Id("b");
        return Disp(Seq(D(0), Lt, x, Lt, y, Sp, Land, Sp, D(0), Lt, a, Lt, b, Sp, Rightarrow, Sp,
            At("q", x,a), At("q", y,b), Sp, Lt, Sp, At("q", x,b), At("q", y,a)));
    }

    private static Formula Readout()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var Ux = At("U", x);
        var Uy = At("U", y);
        var Vx = At("V", x);
        var Vy = At("V", y);
        var s = F.Id("s");
        var t = F.Id("t");
        var i = F.Id("i");
        var j = F.Id("j");
        var pi = At("p", i);
        var gi = At("g", i);
        var conditions = Seq(D(0), Lt, x, Lt, y, Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, D(0), Sp, Le, Sp, pi, Sp, Land, Sp, D(0), Lt, gi, Close, Sp, Land, Sp,
            Open, Exists, Sp, i, Comma, j, Colon, D(0), Lt, pi, Sp, Land, Sp,
            D(0), Lt, At("p", j), Sp, Land, Sp, gi, Lt, At("g", j), Close);
        var map = Seq(Open, s, Comma, t, Close, Sp, Mapsto, Sp, Open,
            s, Ux, Plus, t, Vx, Comma, s, Uy, Plus, t, Vy, Close);
        return Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, conditions, RowBreak, Amp, Rightarrow, Sp,
            Ux, Vy, Sp, Lt, Sp, Vx, Uy, Sp, Land, Sp,
            Mathrm, Grp(F.Id("Injective")), Open, map, Close, End, Grp(F.Id("aligned"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed finite spectrum with positive scales and nonnegative weights, two ordered positive distances identify the coefficients of the second and fourth responses whenever two distinct scales have positive weight.",
        H("Two distances identify two dipole response coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("radial-profile"), DeclarationHandle.Create(Prefix + "profile"),
                H("Normalized radial profile"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At s the profile q equals (1+s+s²/3) exp(−s). Its value at zero is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-minor"), DeclarationHandle.Create(Prefix + "profile_minor"),
                H("Strict ordering at two scales"), StatementSource.FromAuthor(Minor()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<a<b the ratio q(bt)/q(at) strictly decreases for positive t. Its denominator stays positive. After canceling positive exponential and denominator factors, the derivative has the sign of minus t(b−a) times a polynomial with positive coefficients in a, b and t. Multiplying the resulting ratio inequality at x and y by the two positive denominators gives the displayed minor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-moment"), DeclarationHandle.Create(Prefix + "moment"),
                H("Spectral moment response"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite list of scales gᵢ and weights pᵢ the order-k response at t is the sum of pᵢ gᵢᵏ q(tgᵢ). Write U and V for orders two and four."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spectral-separation"), DeclarationHandle.Create(Prefix + "finite_spectral_separation"),
                H("Strict determinant and uniqueness of the coefficients"), StatementSource.FromAuthor(Readout()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume every spectral scale is positive, all weights are nonnegative and two distinct scales have positive weight. For any 0<x<y the signed determinant has the displayed strict ordering. Thus the two real linear coefficients in sU+tV are uniquely determined by the readings at x and y.")),
                    Paragraph(Text("Expand twice the positive difference V(x)U(y)−U(x)V(y) as a double sum over pairs of scales. In each summand the difference of squared scales and the corresponding difference of profile products have the same sign. Their product is multiplied by nonnegative weights. A positively weighted pair of unequal scales contributes strictly. Eliminating each coefficient using the nonzero determinant gives injectivity."))), DescribeRole.Theorem))));
}
