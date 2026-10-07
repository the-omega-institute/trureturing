using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnBareFullGroupClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Bare Full Group Classification.",
        H("Type-A SLn Bare Full Group Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnbarefullgroupclassification-pointwise-u-t-rigid"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareFullGroupClassification.pointwise_U_T_rigid"),
                H("pointwise U T rigid"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The missing full-group rigidity: whole-U fixation and actual T preservation force fixation of EVERY actual SLn target. Opposite-root action and generation are proved, not supplied as hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnbarefullgroupclassification-u-t-agreement-full"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareFullGroupClassification.U_T_agreement_full"),
                H("U T agreement full"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine U agreement between actual automorphisms extends to the whole SLn group when both preserve the actual diagonal torus."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnbarefullgroupclassification-sl-bare-full-group-diagonal-field-graph"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareFullGroupClassification.sl_bare_full_group_diagonal_field_graph"),
                H("sl bare full group diagonal field graph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bare actual SLn automorphism classification on the WHOLE group in the proved branch n>=3/cardF>4. one determinant-one inner correction and one DFG tuple are chosen BEFORE all full-group targets."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
