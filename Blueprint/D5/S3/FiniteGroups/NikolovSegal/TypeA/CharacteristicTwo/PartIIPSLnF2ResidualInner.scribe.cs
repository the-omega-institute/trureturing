using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIIPSLnF2ResidualInnerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn F2 Residual Inner.",
        H("Type-A PSLn F2 Residual Inner"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiipslnf2residualinner-quotient-bijective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2ResidualInner.quotient_bijective"),
                H("quotient bijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine centre-trivial quotient bijectivity over a two-element field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnf2residualinner-quotientequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2ResidualInner.quotientEquiv"),
                H("quotientEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual quotient map is an isomorphism here, proved from matrix centre triviality. No lift of the prescribed projective automorphism is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnf2residualinner-pointwise-u-inner-correction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIIPSLnF2ResidualInner.pointwise_U_inner_correction"),
                H("pointwise U inner correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The intrinsic projective F2 residual is removed by one actual projective central-U inner correction before every full quotient target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
