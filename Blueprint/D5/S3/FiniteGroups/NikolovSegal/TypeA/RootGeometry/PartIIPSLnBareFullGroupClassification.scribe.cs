using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIIPSLnBareFullGroupClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn Bare Full Group Classification.",
        H("Type-A PSLn Bare Full Group Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiipslnbarefullgroupclassification-pointwise-u-t-rigid"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnBareFullGroupClassification.pointwise_U_T_rigid"),
                H("pointwise U T rigid"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic projective full-group rigidity; no projective automorphism lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnbarefullgroupclassification-u-t-agreement-full"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnBareFullGroupClassification.U_T_agreement_full"),
                H("U T agreement full"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality on projective U representatives extends to all SL representatives for an actual projective automorphism and an actual SL automorphism preserving T. The only induced automorphism here is the center quotient of delta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnbarefullgroupclassification-psl-bare-full-group-diagonal-field-graph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnBareFullGroupClassification.psl_bare_full_group_diagonal_field_graph"),
                H("psl bare full group diagonal field graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bare intrinsic PSLn classification on all actual representatives, in the proved branch n>=3/cardF>4. No lift of alpha is assumed. The same genuine projective inner c and same DFG tuple precede EVERY full quotient target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
