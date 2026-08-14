using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Endpoints;

internal sealed class XiProductEndpointLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The displayed xi product form attains both endpoint values through punctured limits.",
        H("Xi Product Endpoint Limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xi-product-form-tends-to-one-half-at-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_zero"),
                H("Xi product form tends to one-half at zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("s"), To, D(0), Comma, Sp, F.Id("s"), Neq, D(0)),
                    Frac, Grp(D(1)), Grp(D(2)), Thin, F.Id("s"), Open, F.Id("s"), Minus, D(1), Close,
                    Thin, Lambda, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen Mellin reconstruction gives the pole clause that s times the "
                        + "completed-zeta reading tends to minus one at zero. Multiplication by the "
                        + "continuous factor one-half times s minus one yields the displayed limit.")),
                    Paragraph(Text(
                        "The approach is punctured at zero. This theorem does not assert the false "
                        + "literal equality obtained by evaluating the raw totalized product there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("xi-product-form-tends-to-one-half-at-one"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_tendsto_one"),
                H("Xi product form tends to one-half at one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("s"), To, D(1), Comma, Sp, F.Id("s"), Neq, D(1)),
                    Frac, Grp(D(1)), Grp(D(2)), Thin, F.Id("s"), Open, F.Id("s"), Minus, D(1), Close,
                    Thin, Lambda, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen Mellin reconstruction gives the pole clause that s minus one times "
                        + "the completed-zeta reading tends to one at one. Multiplication by the "
                        + "continuous factor one-half times s yields the displayed limit.")),
                    Paragraph(Text(
                        "The approach is punctured at one. This theorem likewise records limiting "
                        + "attainment rather than literal evaluation of the raw product at the pole."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("xi-product-form-attains-the-frozen-endpoint-values"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Endpoints/XiProductEndpointLimits.xi_product_form_attains_endpoint_values"),
                H("Xi product form attains the frozen endpoint values"),
                StatementSource.FromAuthor(Disp(Seq(
                    Left, Open,
                    Lim, Underscore, Grp(F.Id("s"), To, D(0), Comma, Sp, F.Id("s"), Neq, D(0)),
                    Frac, Grp(D(1)), Grp(D(2)), Thin, F.Id("s"), Open, F.Id("s"), Minus, D(1), Close,
                    Thin, Lambda, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("s"), To, D(1), Comma, Sp, F.Id("s"), Neq, D(1)),
                    Frac, Grp(D(1)), Grp(D(2)), Thin, F.Id("s"), Open, F.Id("s"), Minus, D(1), Close,
                    Thin, Lambda, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Right, Close, Sp, Land, Sp, Left, Open,
                    Xi, Open, D(0), Close, Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Sp, Land, Sp,
                    Xi, Open, D(1), Close, Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Right, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two punctured limits are paired with the frozen endpoint theorem "
                        + "xiReading zero equals xiReading one equals one-half. Thus continuity of the "
                        + "pole-removed xi reading closes exactly the two points excluded by the frozen "
                        + "off-endpoint product identity.")),
                    Paragraph(Text(
                        "The source displays the product formula globally, but the repository's "
                        + "completed-zeta reading is totalized at its poles. At zero and one the raw "
                        + "product evaluates to zero, so the honest endpoint interpretation is the "
                        + "punctured-limit statement recorded here."))),
                DescribeRole.Theorem)),
        []));
}
