using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIIPSLnUnipotentSylowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn Unipotent Sylow.",
        H("Type-A PSLn Unipotent Sylow"),
        Blocks(
            Paragraph(Text("Actual arbitrary-rank projective Uplus Sylow recognition. The SLn Sylow is transported through the actual surjective center quotient by Sylow.mapSurjective; no projective group order is recomputed.")),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentsylow-projectiveuplussylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow"),
                H("projectiveUplusSylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("surjective Sylow transport through the literal SLn center quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentsylow-projectiveuplussylow-tosubgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.projectiveUplusSylow_toSubgroup"),
                H("projectiveUplusSylow toSubgroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual underlying subgroup is exactly the projective Uplus."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentsylow-exists-projectiveuplus-sylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.exists_projectiveUplus_sylow"),
                H("exists projectiveUplus sylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every prime, finite field of characteristic p, and rank, without a cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentsylow-mem-projectiveuplussylow-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow.mem_projectiveUplusSylow_iff"),
                H("mem projectiveUplusSylow iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal membership recognition by actual unitriangular determinant-one representatives, retaining the genuine quotient and both entry conditions."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
