using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class BetaBeattyClosedFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two beta readings are the Zeckendorf displacement minus a linear golden-slope term.",
        H("Closed Forms for the Two Beta Readings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("expanding-beta-beatty-closed-form"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/BetaBeattyClosedForms.betaReal_eq_displacement_sub_goldenConj"),
                H("The expanding beta reading has a golden-conjugate closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Quad, Sp,
                    Beta, Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("displacementDecode")),
                    Open, F.Id("v"), Close, Sp, Minus, Sp,
                    F.Id("v"), Sp, Cdot, Sp, Psi))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural input v, the expanding beta reading is the integer obtained "
                            + "by shifting each occupied Zeckendorf index upward, minus v times the "
                            + "golden conjugate. The digit dependence is therefore concentrated in one "
                            + "integer displacement term, with the remaining dependence on v affine.")),
                    Paragraph(Text(
                        "For canonical Zeckendorf digits, the first coordinate of the associated golden "
                            + "integer is the shifted Fibonacci sum minus the original Fibonacci sum, "
                            + "hence displacementDecode(v) - v. Its second coordinate is v. Embedding "
                            + "these two coordinates and using phi + psi = 1 gives the stated closed form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contracting-beta-beatty-closed-form"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/BetaBeattyClosedForms.betaContraction_eq_displacement_sub_goldenRatio"),
                H("The contracting beta reading has a golden-ratio closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Quad, Sp,
                    Beta, Apos, Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("displacementDecode")),
                    Open, F.Id("v"), Close, Sp, Minus, Sp,
                    F.Id("v"), Sp, Cdot, Sp, Varphi))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural input v, the contracting beta reading has the same integer "
                            + "Zeckendorf displacement as the expanding reading, but subtracts v times "
                            + "the golden ratio rather than v times the golden conjugate.")),
                    Paragraph(Text(
                        "The two beta faces differ by sqrt(5) times v, while the golden ratio and its "
                            + "conjugate differ by sqrt(5). Subtracting this common face spread from the "
                            + "expanding closed form leaves displacementDecode(v) - v phi, which is the "
                            + "contracting closed form."))),
                DescribeRole.Theorem))));
}
