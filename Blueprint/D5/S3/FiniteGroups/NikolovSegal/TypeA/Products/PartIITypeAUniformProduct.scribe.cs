using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIITypeAUniformProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Type AUniform Product.",
        H("Type-A Type AUniform Product"),
        Blocks(
            Paragraph(Text("Combine the proved large-field/all-rank and bounded-field/large-rank branches into one genuine uniform bare type-A scalar product length. Ordered identity padding is proved for the actual arbitrary beta/e tuple. This family theorem is NOT the all-finite-simple supplier.")),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeauniformproduct-actual-uniform-all-field-large-rank-sln-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct.actual_uniform_all_field_large_rank_SLn_scalar_product"),
                H("actual uniform all field large rank SLn scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("one chosen positive scalar product length precedes EVERY finite field, EVERY sufficiently large actual rank and EVERY bare SLn beta/divisor tuple. Both cardinal2 and unbounded fields are included with the original q/e."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeauniformproduct-actual-uniform-all-field-large-rank-psln-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct.actual_uniform_all_field_large_rank_PSLn_scalar_product"),
                H("actual uniform all field large rank PSLn scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic PSLn counterpart with identical uniform quantifier order. Every action and correction lives in the quotient; no beta lift is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeauniformproduct-actual-uniform-bare-sln-scalar-product-by-group-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct.actual_uniform_bare_SLn_scalar_product_by_group_card"),
                H("actual uniform bare SLn scalar product by group card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual uniform type-A scalar theorem with a GROUP-CARDINALITY cutoff, all ranks n>=4 and EVERY field. Small field AND small rank exceptions are excluded by a proved actual matrix cardinal bound, not by an exhaustion or bounded-group-order premise. M and C precede every group and beta/e tuple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeauniformproduct-actual-uniform-bare-psln-scalar-product-by-group-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct.actual_uniform_bare_PSLn_scalar_product_by_group_card"),
                H("actual uniform bare PSLn scalar product by group card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic PSLn type-A input at one fixed positive width and group-card cutoff, before all fields/ranks/actions. This is full family coverage for n>=4, including F2, rather than a merely shifted/local class range."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
