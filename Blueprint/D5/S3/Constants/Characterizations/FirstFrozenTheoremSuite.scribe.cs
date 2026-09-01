using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Characterizations;

internal sealed class FirstFrozenTheoremSuiteDocument
    : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Constants/Characterizations/FirstFrozenTheoremSuite."
            + "first_frozen_theorem_suite";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten classical completion identities are assembled from their canonical proofs.",
        H("First Frozen Theorem Suite"),
        Blocks(Describe.Lean(
            DescribeId.Create("first-frozen-theorem-suite"),
            DeclarationHandle.Create(Gid),
            H("Ten classical completion identities"),
            StatementSource.FromAuthor(SuiteFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The theorem reuses the repository owners of seven clauses and proves the "
                        + "Gaussian Mellin and completed-tail clauses from pinned Mathlib "
                        + "integral identities.")),
                Paragraph(Text(
                    "The source's explicit Golden exponent is positive and strictly increasing "
                        + "with finite sublevel sets. Its bounded counting-density estimate is "
                        + "the sole parameterized premise; the general spectral continuation "
                        + "theorem then gives meromorphicity and residue one over square root "
                        + "five."))),
            DescribeRole.Theorem))));

    private static Formula SuiteFormula()
    {
        Formula a = F.Id("a");
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula p = F.Id("p");
        Formula ell = F.Id("ell");
        Formula y = F.Id("y");
        Formula pi = Pi;
        Formula varphi = Varphi;

        Formula fourier = Seq(
            Call("Fourier", Call("Gaussian", a)), Sp, Eq, Sp, Call("Gaussian", a),
            Sp, Iff, Sp, a, Sp, Eq, Sp, pi);
        Formula gaussianMellin = Seq(
            D(2), Call("MellinGaussian", s), Sp, Eq, Sp,
            pi, Caret, Grp(Minus, s, Sp, Slash, Sp, D(2)),
            Call("Gamma", Seq(s, Sp, Slash, Sp, D(2))));
        Formula exponentialFlow = Seq(
            Forall, Sp, y, Comma, Sp, Call("E", y), Sp, Eq, Sp, Call("exp", y));
        Formula goldenFixedPoint = Seq(
            Forall, Sp, y, Gt, D(0), Comma, Sp,
            Open, y, Sp, Eq, Sp, D(1), Sp, Plus, Sp, Fraction(D(1), y), Close,
            Sp, Iff, Sp, y, Sp, Eq, Sp,
            Fraction(Grp(D(1), Sp, Plus, Sp, Sqrt, Grp(D(5))), D(2)));
        Formula localPrecision = Seq(
            Forall, Sp, ell, Comma, Sp,
            Call("exp", Seq(Minus, ell)), Sp, Eq, Sp, p, Caret, Grp(Minus, D(1)),
            Sp, Iff, Sp, ell, Sp, Eq, Sp, Call("log", p));
        Formula eulerResidual = Seq(
            Call("H", F.Id("n")), Sp, Minus, Sp, Call("log", F.Id("n")), Sp, Minus, Sp,
            F.Id("gamma"), Sp, To, Sp, D(0));
        Formula criticalLine = Seq(
            s, Sp, Eq, Sp, D(1), Sp, Minus, Sp, Call("conj", s),
            Sp, Iff, Sp, Call("Re", s), Sp, Eq, Sp, Fraction(D(1), D(2)));
        Formula ramanujan = Seq(
            Call("S", x), Sp, Plus, Sp, Call("T", x), Sp, Eq, Sp,
            Sqrt, Grp(Fraction(
                Grp(pi, Sp, Times, Sp, Call("exp", x)),
                Grp(D(2), Sp, Times, Sp, x))));
        Formula lambertMellin = Seq(
            Call("MellinLambert", w), Sp, Eq, Sp, Call("Gamma", w),
            Call("zeta", w), Call("zeta", Seq(w, Sp, Plus, Sp, F.Id("r"))),
            Grp(D(1), Sp, Minus, Sp,
                p, Caret, Grp(Minus, Grp(w, Sp, Plus, Sp, F.Id("r")))));
        Formula goldenZeta = Seq(
            Call("MeromorphicOn", Call("Z", varphi),
                Grp(Call("Re", s), Sp, Gt, Sp, D(0))),
            Sp, Land, Sp, Call("Res", Call("Z", varphi), D(1)),
            Sp, Eq, Sp, Fraction(D(1), Grp(Sqrt, Grp(D(5)))));

        return Disp(Seq(
            Grp(fourier), Sp, Land, RowBreak,
            Grp(gaussianMellin), Sp, Land, RowBreak,
            Grp(exponentialFlow), Sp, Land, RowBreak,
            Grp(goldenFixedPoint), Sp, Land, RowBreak,
            Grp(localPrecision), Sp, Land, RowBreak,
            Grp(eulerResidual), Sp, Land, RowBreak,
            Grp(criticalLine), Sp, Land, RowBreak,
            Grp(ramanujan), Sp, Land, RowBreak,
            Grp(lambertMellin), Sp, Land, RowBreak,
            Grp(goldenZeta), Dot));
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
