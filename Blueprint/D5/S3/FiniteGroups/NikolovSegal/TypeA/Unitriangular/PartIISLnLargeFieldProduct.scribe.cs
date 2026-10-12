using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIISLnLargeFieldProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Large Field Product.",
        H("Type-A SLn Large Field Product"),
        Blocks(
            Paragraph(Text("Full untwisted SL(k+4) product, using the actual ULUL width and the p255 central-Levi/radical reconstruction.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnlargefieldproduct-actual-uniform-inner-sln-dfg-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnLargeFieldProduct.actual_uniform_inner_SLn_DFG_product"),
                H("actual uniform inner SLn DFG product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine uniform-in-rank full-group product for every prescribed DΦΓ and original positive divisor tuple, over fields beyond the uniform cutoff. N,C precede every field/rank/tuple. one inner tuple precedes all SL targets. No scalar/twisted coverage assumption is used. Bare classification, small fields, other simple families and the original all-simple supplier remain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnlargefieldproduct-actual-uniform-sln-dfg-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIISLnLargeFieldProduct.actual_uniform_SLn_DFG_scalar_product"),
                H("actual uniform SLn DFG scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full group construction supplies the exact consumed q/e scalar interface for the prescribed DΦΓ family. This is proved coverage, not an unproved scalar input; it does not classify every bare automorphism."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
