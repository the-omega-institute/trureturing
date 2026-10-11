using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIITypeAProjectiveSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Type AProjective Supplier.",
        H("Type-A Type AProjective Supplier"),
        Blocks(
            Paragraph(Text("Genuine complete untwisted type-A FAMILY scalar supply. All finite fields, all matrix ranks, arbitrary bare quotient automorphisms and the original positive e|q are included above one uniform group-card cutoff. A1/A2 and the new all-rank A>=3 proof are actually consumed. No exhaustion of arbitrary finite simple groups is asserted.")),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeaprojectivesupplier-actual-uniform-psln-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAProjectiveSupplier.actual_uniform_PSLn_scalar_product"),
                H("actual uniform PSLn scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("one M(q),C(q) BEFORE every field/rank/bare beta/divisor tuple, with one global correction BEFORE all targets in the actual PSLn. No family classification, class width, scalar or twisted product premise remains."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
