using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class GoldenExponentRaysDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational golden-exponent rays are exactly rational coordinate rays.",
        H("Rational Rays of Golden Exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-exponent-rational-rays-match-coordinate-rays"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/GoldenExponentRays."
                    + "golden_exponent_rational_ray_iff"),
                H("Golden-power values and exponent vectors have the same rational rays"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
                    F.Id("c"), Comma, Sp, F.Id("d"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Left, Open, Exists, Sp, F.Id("p"), Comma, Sp, F.Id("q"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("q"), Gt, D(0), Sp, Land, Sp,
                    F.Id("q"), Cdot, Sp, F.Id("g"), Open, F.Id("a"), Comma, F.Id("b"), Close,
                    Eq, F.Id("p"), Cdot, Sp, F.Id("g"), Open, F.Id("c"), Comma, F.Id("d"), Close,
                    Right, Close, Sp, Equiv, Sp,
                    Left, Open, Exists, Sp, F.Id("p"), Comma, Sp, F.Id("q"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("q"), Gt, D(0), Sp, Land, Sp,
                    F.Id("q"), F.Id("a"), Eq, F.Id("p"), F.Id("c"), Sp, Land, Sp,
                    F.Id("q"), F.Id("b"), Eq, F.Id("p"), F.Id("d"), Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write g(a,b) = a phi^2 + b phi^3. For natural exponent vectors "
                        + "(a,b) and (c,d), there are naturals p and positive q with "
                        + "q g(a,b) = p g(c,d) exactly when the same p and q satisfy "
                        + "qa = pc and qb = pd. Thus the real golden-power values and their "
                        + "exponent vectors determine the same nonnegative rational rays.")),
                    Paragraph(Text(
                        "The forward implication rewrites the scaled values as golden-power "
                        + "coordinates and applies the existing repository theorem "
                        + "GoldenPowerCoordinates.golden_power_coordinates_unique directly. "
                        + "The reverse implication substitutes the two coordinate equalities. "
                        + "That reused theorem already rests on Mathlib's exact irrationality "
                        + "theorem for the golden ratio, so no second irrationality proof is made.")),
                    Paragraph(Text(
                        "Repository search found the coordinate-uniqueness theorem but no prior "
                        + "rational-ray declaration. Pinned Mathlib source and skill search found "
                        + "no exact ray theorem; online Loogle returned zero matches for the "
                        + "formula-shaped irrational-linear-form query.")),
                    Paragraph(Text(
                        "This node closes only the ray-classification sentence in observation "
                        + "6.167, in its positive-denominator natural-coordinate form. It does "
                        + "not formalize the finite shell census, the listed ratios, Euler-product "
                        + "natural boundaries, zero cancellation, or any linear-independence "
                        + "hypothesis about zeta zeros."))),
                DescribeRole.Theorem))));
}
