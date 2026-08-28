using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class GoldenSlopeSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ArithmeticTomography/GoldenSlopeSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum golden-slope gap in a finite positive integer window has a reciprocal linear lower bound.",
        H("Golden Slope Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-window-gap-set"),
                DeclarationHandle.Create(Prefix + "goldenWindowGapSet"),
                H("Finite-window golden gap set"),
                StatementSource.FromAuthor(GapSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The gap set contains exactly the absolute differences between the "
                            + "golden-slope readings of two distinct points in the positive "
                            + "H by H integer window."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-separation"),
                DeclarationHandle.Create(Prefix + "goldenSeparation"),
                H("Canonical golden separation"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Golden separation is the real infimum of the finite-window gap set. "
                            + "For H at least two that set is nonempty, so this is its minimum "
                            + "pairwise spectral spacing."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-separation-bound"),
                DeclarationHandle.Create(Prefix + "golden_separation_bound"),
                H("Golden separation has a reciprocal linear lower bound"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The product of a nonzero golden reading difference and its conjugate "
                            + "is a nonzero integer, hence has absolute value at least one. The "
                            + "conjugate factor is at most goldenRatio times H minus one, which "
                            + "gives the bound for every gap and therefore for their infimum."))),
                DescribeRole.Theorem))));

    private static Formula GapSetFormula()
    {
        Formula h = F.Id("H");
        Formula d = F.Id("d");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula mPrime = F.Id("mPrime");
        Formula nPrime = F.Id("nPrime");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula window = Call("Icc", D(1), h);
        Formula firstPair = Seq(Open, m, Comma, Sp, n, Close);
        Formula secondPair = Seq(Open, mPrime, Comma, Sp, nPrime, Close);
        Formula firstReading = Seq(Varphi, Sp, m, Sp, Plus, Sp, n);
        Formula secondReading = Seq(Varphi, Sp, mPrime, Sp, Plus, Sp, nPrime);
        Formula gap = new Formula.Absolute(
            Seq(firstReading, Sp, Minus, Sp, Open, secondReading, Close));
        Formula conditions = Seq(
            m, Comma, Sp, n, Comma, Sp, mPrime, Comma, Sp, nPrime,
            Sp, InMacro, Sp, window, Comma, Sp,
            firstPair, Sp, Neq, Sp, secondPair, Sp, Land, Sp,
            d, Sp, Eq, Sp, gap);
        Formula set = Seq(
            OpenBrace, d, Sp, InMacro, Sp, reals, Sp, Mid, Sp,
            Exists, Sp, conditions, CloseBrace);

        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, naturals, Comma, Sp,
            Call("goldenWindowGapSet", h), Sp, Eq, Sp, set, Dot));
    }

    private static Formula SeparationFormula()
    {
        Formula h = F.Id("H");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, naturals, Comma, Sp,
            Call("goldenSeparation", h), Sp, Eq, Sp,
            Call("sInf", Call("goldenWindowGapSet", h)), Dot));
    }

    private static Formula BoundFormula()
    {
        Formula h = F.Id("H");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula denominator = Seq(Varphi, Open, h, Sp, Minus, Sp, D(1), Close);
        return Disp(Seq(
            Forall, Sp, h, Colon, Sp, naturals, Comma, Sp,
            D(2), Sp, Leq, Sp, h, Sp, Rightarrow, Sp,
            Frac, Grp(D(1)), Grp(denominator), Sp, Leq, Sp,
            Call("goldenSeparation", h), Dot));
    }
}
