using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusDyadicUnitWeightParsevalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval";
    private const string PartialSum = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence";
    private const string LineFourier = "D5/S3/Weil/ZetaGamma/FormCore/LineFourier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconditional unit-weight Parseval for the literal signed dyadic Möbius difference.",
        H("Unit-weight Parseval for the signed dyadic Möbius difference"),
        Blocks(
            Paragraph(Text("Let μ be the ordinary arithmetic Möbius function. For real x > 1, "
                + "S(x) is the finite weighted sum mobiusPartialSum from "), Ref(PartialSum),
                Text(". The natural-floor cutoffs give the signed difference by cancelling the common prefix.")),
            new DocumentBlock.DisplayFormula(F.Disp(SignedDifference())),
            Describe.Lean(
                DescribeId.Create("dyadic-mellin-symbol"),
                DeclarationHandle.Create(Owner + ".mobiusDyadicMellinSymbol"),
                H("Mellin symbol and its value at zero"),
                StatementSource.FromAuthor(F.Disp(MellinSymbol())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here s is complex and 2 to the power s means exp((log 2)s). "
                    + "The reciprocal uses the Lean convention 0⁻¹ = 0. Near zero, "
                    + "sζ(1+s) extends holomorphically with value 1. Therefore the reciprocal "
                    + "ζ(1+s)⁻¹ tends to 0, and (1−2ˢ)/s tends to −log 2. The product has "
                    + "removable value log 2 as a complex number."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unit-weight-parseval"),
                DeclarationHandle.Create(Owner + ".mobiusDyadicDifference_unitWeight_parseval"),
                H("Integrability and Parseval at unit weight"),
                StatementSource.FromAuthor(F.Disp(Parseval())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both L¹ assertions use Lebesgue measure on the displayed domains. "
                        + "The time density includes x⁻¹. The frequency integral uses dξ "
                        + "with angular frequency 2πξ, so the displayed equality has unit prefactor.")),
                    Paragraph(Text(
                        "For Re(s) > 0, the half-line Mellin transform with kernel x⁻ˢ⁻¹ sends S "
                        + "to ζ(1+s)⁻¹/s. Centering S by subtracting 1 gives "
                        + "(ζ(1+s)⁻¹−1)/s. The centered sum vanishes on (1,2), so dilating "
                        + "it by 2 multiplies this transform by 2ˢ after changing variables. "
                        + "Subtracting the dilated transform gives the displayed symbol.")),
                    Paragraph(Text(
                        "For δ > 0, the function of u given by exp(−δu)D(exp u) on u ≥ 0 "
                        + "and zero on u < 0 is in L¹ and L². Its Fourier transform with "
                        + "phase exp(−2πiuξ) is H(δ+2πiξ). Apply normalized Plancherel "
                        + "and take δ = 1/(n+1) down to zero. The squared time densities "
                        + "increase pointwise. On 0 ≤ δ ≤ 1 the squared symbol is dominated "
                        + "by C²(1+|2πξ|)⁻³ᐟ², which is integrable. Monotone convergence "
                        + "on the time side and dominated convergence on the frequency side "
                        + "give finite equal masses. The substitution x = exp u turns du "
                        + "into dx/x on x > 1."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(PartialSum)),
            DocumentEdge.Dependency.Create(GidRef.Create(LineFourier))
        ]));

    private static Formula SignedDifference()
    {
        var x = F.Id("x");
        var n = F.Id("n");
        var floorX = F.Seq(F.Lfloor, F.Sp, x, F.Rfloor, F.Underscore, F.Grp(F.Plus));
        var floorTwiceX = F.Seq(F.Lfloor, F.D(2), x, F.Rfloor, F.Underscore, F.Grp(F.Plus));
        var coefficient = F.Seq(F.Frac, F.Grp(Call(F.Mu, n)), F.Grp(n));
        return F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            Call(F.Id("S"), x), F.Eq,
            F.Sum, F.Underscore, F.Grp(F.D(1), F.Leq, F.Sp, n, F.Leq, floorX), F.Thin, coefficient,
            F.RowBreak,
            Call(F.Id("D"), x), F.Eq,
            Call(F.Id("S"), x), F.Minus, Call(F.Id("S"), F.Seq(F.D(2), x)), F.Eq,
            F.Minus, F.Sum, F.Underscore, F.Grp(floorX, F.Lt, n, F.Leq, floorTwiceX),
            F.Thin, coefficient,
            F.End, F.Grp(F.Id("gathered")));
    }

    private static Formula MellinSymbol()
    {
        var s = F.Id("s");
        var reciprocal = F.Seq(Call(F.Zeta, F.Seq(s, F.Plus, F.D(1))),
            F.Caret, F.Grp(F.Minus, F.D(1)));
        return F.Seq(F.Forall, F.Sp, s, F.InMacro, F.Mathbb, F.Grp(F.Id("C")), F.Comma,
            Call(F.Id("H"), s), F.Eq, F.Begin, F.Grp(F.Id("cases")),
            F.Log, F.Sp, F.D(2), F.Comma, F.Amp, s, F.Eq, F.D(0), F.RowBreak,
            F.Frac, F.Grp(
                F.Open, F.D(1), F.Minus, F.D(2), F.Caret, F.Grp(s), F.Close,
                F.Open, reciprocal, F.Minus, F.D(1), F.Close), F.Grp(s),
            F.Comma, F.Amp, s, F.Neq, F.D(0), F.End, F.Grp(F.Id("cases")));
    }

    private static Formula Parseval()
    {
        var x = F.Id("x");
        var xi = F.Xi;
        var time = F.Seq(Call(F.Id("D"), x), F.Caret, F.Grp(F.D(2)), F.Thin,
            x, F.Caret, F.Grp(F.Minus, F.D(1)));
        var frequency = F.Seq(F.Left, F.Vert, F.Sp,
            Call(F.Id("H"), F.Seq(F.D(2), F.Pi, F.Sp, F.Id("i"), xi)),
            F.Right, F.Vert, F.Caret, F.Grp(F.D(2)));
        var xDomain = F.Seq(F.Open, F.D(1), F.Comma, F.Infty, F.Close);
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var dx = F.Seq(F.Mathrm, F.Grp(F.Id("d")), x);
        var dxi = F.Seq(F.Mathrm, F.Grp(F.Id("d")), xi);
        var l1 = F.Seq(F.Id("L"), F.Caret, F.Grp(F.D(1)));
        return F.Seq(F.Begin, F.Grp(F.Id("gathered")),
            F.Open, x, F.Mapsto, F.Sp, time, F.Close, F.InMacro, F.Sp, Call(l1, xDomain, dx),
            F.Sp, F.Land, F.RowBreak,
            F.Open, xi, F.Mapsto, frequency, F.Close, F.InMacro, F.Sp, Call(l1, reals, dxi),
            F.Sp, F.Land, F.RowBreak,
            F.Int, F.Underscore, F.Grp(xDomain), F.Thin, time, F.Thin, dx, F.Eq,
            F.Int, F.Underscore, F.Grp(reals), F.Thin, frequency, F.Thin, dxi,
            F.End, F.Grp(F.Id("gathered")));
    }

    private static Formula Call(Formula head, params Formula[] arguments) =>
        new Formula.Apply(head, [.. arguments]);
}
