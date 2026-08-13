using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenChampionPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The proposed golden-tower champion point has equivalent radical and negative-power forms.",
        H("Golden Champion Point Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-champion-point-identity"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/GoldenChampionPoint.golden_champion_point_identity"),
                H("The champion point forms agree"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1, 3)), Grp(D(2)), Sp, Minus, Sp,
                    D(4), Varphi, Sp, Eq, Sp,
                    Frac,
                    Grp(Open, Sqrt, Grp(D(5)), Sp, Minus, Sp, D(2), Close,
                        Caret, Grp(D(2))),
                    Grp(D(2)), Sp, Land, Sp,
                    Frac,
                    Grp(Open, Sqrt, Grp(D(5)), Sp, Minus, Sp, D(2), Close,
                        Caret, Grp(D(2))),
                    Grp(D(2)), Sp, Eq, Sp,
                    Frac, Grp(Varphi, Caret, Grp(Minus, D(6))), Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The square-root identity follows from the library definition of the golden " +
                        "ratio and the exact square of sqrt(5). For the negative power, the library's " +
                        "golden quadratic identity gives phi cubed as 2 + sqrt(5), while sqrt(5) - 2 " +
                        "is its reciprocal. Squaring the reciprocal pair gives the exponent-six form.")),
                    Paragraph(Text(
                        "Pinned Mathlib provides Real.goldenRatio_sq, Real.goldenRatio_ne_zero, " +
                        "Real.sq_sqrt, zpow_neg, and the definitional closed form of " +
                        "Real.goldenRatio. No declaration packaging this three-form equality was found.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the champion closed-form clause only. " +
                        "The constant-arm realization, the maximizing orbit, the global extremality " +
                        "argument, survivor-set analysis, finite orbit enumerations, golden-gap " +
                        "substitution dynamics, higher-order substitution claims, and the boundary " +
                        "outside the finite-type regime remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
