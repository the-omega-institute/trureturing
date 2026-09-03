using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ExactPoleLayerSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-order pole layers select quotient and remainder, with nine exact row certificates.",
        H("Exact Fourth-Order Pole-Layer Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourth-order-layers-give-nine-exact-selections"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ExactPoleLayerSelection.exact_pole_layer_selection"),
                H("Fourth-order layers give nine exact selections"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("K"), Open, F.Id("a"), Close, Eq,
                    Lfloor, Frac, Grp(F.Id("a")), Grp(D(4)), Rfloor,
                    Comma, Quad, Sp,
                    F.Id("j"), Open, F.Id("a"), Close, Eq,
                    F.Id("a"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(4),
                    InMacro, Grp(D(0), Comma, D(1), Comma, D(2), Comma, D(3))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every row a decomposes uniquely as four times its selected order "
                        + "a/4 plus the remainder layer a mod 4, and the layer is strictly "
                        + "below four. For a at least four this makes the selected order "
                        + "positive, excluding the zero-denominator branch in the signed "
                        + "coefficient factor. The existing power-series shift theorem then "
                        + "reads exactly the remainder coefficient.")),
                    Paragraph(Text(
                        "The rows 4, 8, 9, 12, 13, 14, 15, 16, and 17 are normalized in "
                        + "Lean to their nine claimed order-layer pairs. The rational regular "
                        + "head 1 + 2u - 2u^2 - 2u^3 gives the exact deeper readings 30, "
                        + "-122, and -8 after inversion and powering. These are algebraic "
                        + "certificates; the source's fitted tail polynomials, empirical start "
                        + "points, analytic pole claims, and next-layer interference mechanism "
                        + "require separate premises and are not asserted here.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no theorem combining "
                        + "this source-specific layer selection with its nine rows. The proof "
                        + "uses Nat.mod_add_div and Nat.mod_lt for the quotient-remainder law, "
                        + "and reuses the adjacent frozen pole_layer_coefficient theorem for "
                        + "the coefficient shift."))),
                DescribeRole.Theorem))));
}
