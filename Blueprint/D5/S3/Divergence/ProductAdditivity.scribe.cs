using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ProductAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite real-valued classical KL divergence is additive on product mass functions.", H("Product Additivity of Finite Classical KL Divergence"), Blocks(
            Describe.Lean(DescribeId.Create("finite-classical-kl-divergence-is-additive-on-products"), DeclarationHandle.Create("D5/S3/Divergence/ProductAdditivity.kl_divergence_product_additive"), H("Finite classical KL divergence is additive on products"), StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("a"), Apos, Comma, Sp, F.Id("b"), Apos, Colon, Sp,
                    Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("a"), Open, F.Id("i"), Close, Eq, D(1),
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("j")),
                    F.Id("a"), Apos, Open, F.Id("j"), Close, Eq, D(1),
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, F.Id("a"), Open, F.Id("i"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, F.Id("b"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("j"), Comma, Sp,
                    D(0), Lt, F.Id("a"), Apos, Open, F.Id("j"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, F.Id("b"), Apos, Open, F.Id("j"), Close, Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("a"), Open, F.Id("i"), Close,
                    F.Id("a"), Apos, Open, F.Id("j"), Close,
                    Vert, Vert, Sp,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("b"), Open, F.Id("i"), Close,
                    F.Id("b"), Apos, Open, F.Id("j"), Close,
                    Close, Eq, RowBreak,
                    F.Id("D"), Open,
                    F.Id("a"), Vert, Vert, Sp, F.Id("b"), Close,
                    Plus,
                    F.Id("D"), Open,
                    F.Id("a"), Apos, Vert, Vert, Sp,
                    F.Id("b"), Apos, Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let iota and kappa be finite types. Let a and b be strictly positive " +
                        "real functions on iota, and let a' and b' be strictly positive real " +
                        "functions on kappa. Only a and a' are normalized: their finite sums " +
                        "are one. The reference functions b and b' need only be strictly " +
                        "positive and are not assumed normalized.")),
                    Paragraph(Text(
                        "This is the finite real-valued klDivergence of ClassicalDPI, the " +
                        "repository's single source for the definition, evaluated genuinely " +
                        "on the product mass functions (i,j) -> a(i)a'(j) and (i,j) -> " +
                        "b(i)b'(j), not a measure-theoretic divergence. Expanding the finite " +
                        "product sum and applying Real.log_mul splits the logarithm; the " +
                        "normalizations of a and a' then leave D(a||b) + D(a'||b').")),
                    Paragraph(Text(
                        "Outside this module, Mathlib's measure-valued chain rule " +
                        "InformationTheory.klDiv_compProd_eq_add is not used, and no bridge " +
                        "between the ENNReal measure divergence and this finite real sum is " +
                        "established here. The declaration therefore does not identify this " +
                        "finite divergence with any measure-valued KL divergence."))), DescribeRole.Theorem))));
}
