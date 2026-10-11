using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIITypeATransitiveSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Type ATransitive Supplier.",
        H("Type-A Type ATransitive Supplier"),
        Blocks(
            Paragraph(Text("Original uniform Proposition10.2 interface on the COMPLETE untwisted projective type-A family, all fields and all ranks above one group cutoff. The newly proved uniform scalar product and its q=1 twisted consequence feed the actual Hall-selected/typeI/typeII forest reconstruction. Other finite-simple families and their exhaustion remain unproved.")),
            Describe.Lean(
                DescribeId.Create("typea-partiitypeatransitivesupplier-actual-uniform-psln-transitive-coverage"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeATransitiveSupplier.actual_uniform_PSLn_transitive_coverage"),
                H("actual uniform PSLn transitive coverage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual full original prescribed value coverage on arbitrary finite nonempty factor ranks over PSLn, at one positive m(q) and C(q) BEFORE all fields/matrix ranks/action/component tuples. All genuine coordinate laws and q/e powers are consumed; corrections precede all targets. No scalar/twisted/coverage/classification premise remains for this family."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
