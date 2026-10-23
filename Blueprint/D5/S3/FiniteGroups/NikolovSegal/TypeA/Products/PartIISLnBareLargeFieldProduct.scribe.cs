using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnBareLargeFieldProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Bare Large Field Product.",
        H("Type-A SLn Bare Large Field Product"),
        Blocks(
            Paragraph(Text("For the large-field branch of PartII Sections2 and6, full-group classification of arbitrary bare SLn and PSLn automorphisms feeds the actual all-rank ordered product. No projective automorphism lift is assumed. The original q/e powers and correction-before-all-targets order are retained.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnbarelargefieldproduct-actual-uniform-bare-sln-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareLargeFieldProduct.actual_uniform_bare_SLn_scalar_product"),
                H("actual uniform bare SLn scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniform chosen-length scalar product for EVERY actual SLn automorphism, all ranks k+4 and sufficiently large fields. No normal-form premise remains. N,C precede every field/rank/tuple; one correction precedes all targets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnbarelargefieldproduct-actual-uniform-bare-psln-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareLargeFieldProduct.actual_uniform_bare_PSLn_scalar_product"),
                H("actual uniform bare PSLn scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic bare PSLn scalar product in the same uniform large-field branch. Classification and correction live in PSLn; alpha is never lifted."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
