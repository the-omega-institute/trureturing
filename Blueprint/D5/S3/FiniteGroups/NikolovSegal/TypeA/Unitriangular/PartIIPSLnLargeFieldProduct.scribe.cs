using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIPSLnLargeFieldProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn Large Field Product.",
        H("Type-A PSLn Large Field Product"),
        Blocks(
            Paragraph(Text("Part II p255: actual central-quotient consumption, for prescribed DΦΓ actions. No lift/classification of arbitrary PSL automorphisms is assumed.")),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnlargefieldproduct-projectiveaction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPSLnLargeFieldProduct.projectiveAction"),
                H("projectiveAction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual induced automorphism of the central quotient; characteristic invariance of the center is group theory, not a lifting premise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnlargefieldproduct-actual-uniform-psln-dfg-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPSLnLargeFieldProduct.actual_uniform_PSLn_DFG_scalar_product"),
                H("actual uniform PSLn DFG scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine full actual PSLn scalar product for the induced prescribed DΦΓ family, all ranks k+4 and sufficiently large fields. Uniform N,C are chosen BEFORE all fields/ranks/tuples, and the same quotient correction precedes all full quotient targets. This does not classify bare PSL autos."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
