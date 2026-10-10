using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIIPSLnPointwiseURigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn Pointwise URigidity.",
        H("Type-A PSLn Pointwise URigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiipslnpointwiseurigidity-commuting-root-diagonal-nonzero"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnPointwiseURigidity.commuting_root_diagonal_nonzero"),
                H("commuting root diagonal nonzero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A matrix commuting with one elementary positive root has a nonzero diagonal entry, by its actual zero-row equations and determinant one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnpointwiseurigidity-lift-diagonal-commutation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnPointwiseURigidity.lift_diagonal_commutation"),
                H("lift diagonal commutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine nonzero diagonal entry eliminates the central discrepancy in projective commutation with an actual diagonal matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnpointwiseurigidity-fixes-u-kernel-preimage"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnPointwiseURigidity.fixes_U_kernel_preimage"),
                H("fixes U kernel preimage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pointwise projective U fixation preserves the exact projective character kernel. Representatives are selected individually; no automorphism lift occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnpointwiseurigidity-fixes-negative-simple"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnPointwiseURigidity.fixes_negative_simple"),
                H("fixes negative simple"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intrinsic projective opposite-simple-root rigidity. Actual quotient conjugation lifting and the common third coordinate remove all scalar ambiguities, without a lift of the projective automorphism."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
