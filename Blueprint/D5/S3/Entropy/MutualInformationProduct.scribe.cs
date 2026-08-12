using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MutualInformationProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite classical mutual information in nats vanishes on every normalized product mass function.", H("Mutual Information Vanishes on Product Laws"), Blocks(
            Describe.Lean(DescribeId.Create("mutual-information-vanishes-on-product-laws"), DeclarationHandle.Create("D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero"), H("Mutual information vanishes on product laws"), StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("a"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("b"), Colon, Sp,
                    Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("a"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("a"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("b"), Open, F.Id("j"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("j")),
                    F.Id("b"), Open, F.Id("j"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    Open, F.Id("i"), Comma, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("a"), Open, F.Id("i"), Close,
                    F.Id("b"), Open, F.Id("j"), Close,
                    Close, Eq, D(0), Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "The theorem states that mutual information vanishes on a product joint, " +
                        "the independent case. The factors a and b need only be nonnegative and " +
                        "normalized; no strict positivity is assumed. Zero-mass cells are " +
                        "permitted, and their terms vanish. The units are nats, consistent with " +
                        "the bucket's other entropy modules. This module defines nothing; it uses " +
                        "the imported mutualInformation and marginal definitions.")),
                    Paragraph(Text(
                        "This identity is a definition pin, not merely another consequence of " +
                        "divergence nonnegativity. The nonnegativity theorem holds for any " +
                        "reference that is nonnegative, normalized, and absolutely continuous, " +
                        "so it does not certify that mutualInformation uses the product of the " +
                        "joint's own marginals. By forcing the imported definition to reduce to " +
                        "zero on normalized product joints, this theorem constrains the reference " +
                        "itself, in particular the coordinate swap used to obtain the second " +
                        "marginal. The proof names the swapped second marginal explicitly as " +
                        "hswapped_second_marginal rather than collapsing the mutualInformation " +
                        "definition immediately, so the swap-specific content is present in the " +
                        "proof.")),
                    Paragraph(Text(
                        "A corrupted reference that reuses the first marginal for both coordinates " +
                        "can typecheck when the index types coincide. On the positive Bool example " +
                        "a = (3/4, 1/4) and b = (1/4, 3/4), that reference remains nonnegative, " +
                        "normalized, and absolutely continuous, so it survives the nonnegativity " +
                        "theorem, but it gives one half of log 3 instead of zero. The product " +
                        "identity rejects that corruption.")),
                    Paragraph(Text(
                        "The residual limitation is plain: this identity tests the reference only " +
                        "on product joints. It is blind to any reference that agrees with the " +
                        "product of the marginals on independent joints but differs on correlated " +
                        "ones. Correlated joints are exactly where mutual information does its " +
                        "work. This confirms the reduction to independence at the boundary; it " +
                        "does not verify the reference on correlated joints. Accordingly, the " +
                        "mutualInformation definition is not fully attested by this theorem.")),
                    Paragraph(Text(
                        "This is one direction only. It does not prove the converse that vanishing " +
                        "mutual information forces the joint to be a product, equivalently " +
                        "independence. That converse would require the equality case of the " +
                        "divergence bound, and it is not established here."))), DescribeRole.Theorem))));
}
