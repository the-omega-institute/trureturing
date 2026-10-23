using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnSmallFieldProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Small Field Product.",
        H("Type-A SLn Small Field Product"),
        Blocks(
            Paragraph(Text("Actual PartII Section5 small-field scalar product input for all bare SLn and intrinsic PSLn automorphisms in every sufficiently large rank. The finite-outer consumer, genuine full class width, F2/full-group classification and exact ordered shift are proved consumed inputs. The chosen width and rank cutoff precede every field, rank and beta/e tuple; one correction tuple precedes every target. Other simple families remain open.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnsmallfieldproduct-actual-bare-sln-bounded-field-product-shape"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct.actual_bare_SLn_bounded_field_product_shape"),
                H("actual bare SLn bounded field product shape"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact full-group SLn coverage in the actual long-cycle rank shape, including F2 and original prescribed q/e; no shift remains in the target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnsmallfieldproduct-actual-bare-psln-bounded-field-product-shape"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct.actual_bare_PSLn_bounded_field_product_shape"),
                H("actual bare PSLn bounded field product shape"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic PSLn full scalar product. Target lifting is ordinary quotient surjectivity; the bare automorphisms themselves are NOT lifted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnsmallfieldproduct-actual-uniform-bare-sln-bounded-field-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct.actual_uniform_bare_SLn_bounded_field_scalar_product"),
                H("actual uniform bare SLn bounded field scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed chosen length and explicit rank cutoff BEFORE all groups and bare automorphism/divisor tuples. Covers EVERY bounded finite field and EVERY rank above the cutoff, with no congruence/rank-shape premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnsmallfieldproduct-actual-uniform-bare-psln-bounded-field-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct.actual_uniform_bare_PSLn_bounded_field_scalar_product"),
                H("actual uniform bare PSLn bounded field scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Same uniform field/rank quantifiers, intrinsic projective targets and arbitrary bare quotient actions; one global correction before all targets."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
