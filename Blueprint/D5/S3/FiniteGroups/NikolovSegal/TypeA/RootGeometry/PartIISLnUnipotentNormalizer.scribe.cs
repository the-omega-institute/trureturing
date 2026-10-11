using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIISLnUnipotentNormalizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unipotent Normalizer.",
        H("Type-A SLn Unipotent Normalizer"),
        Blocks(
            Paragraph(Text("The normalizer of the actual full upper unitriangular subgroup of SLn, over every field, in every rank. The canonical coordinate prefixes are derived intrinsically from the subgroup action, using coefficient-one transvections.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-prefix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.Prefix"),
                H("Prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vectors supported on the first k coordinates; no bound on k is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-prefix-succ-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.prefix_succ_iff"),
                H("prefix succ iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual unitriangular action recovers the next coordinate prefix. The reverse direction uses E_(k,j)(1), so works also in characteristics 2/3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-normalizer-preserves-prefix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_preserves_prefix"),
                H("normalizer preserves prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalization preserves every coordinate prefix, derived by induction from the actual conjugation law and the intrinsic action characterization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-below-diagonal-zero-of-normalizer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.below_diagonal_zero_of_normalizer"),
                H("below diagonal zero of normalizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A normalizer element has the actual zero entries below its diagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-conjugate-mem-uplus-of-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.conjugate_mem_Uplus_of_upper"),
                H("conjugate mem Uplus of upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Upper triangular conjugation preserves the literal unitriangular carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-mem-normalizer-iff-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.mem_normalizer_iff_upper"),
                H("mem normalizer iff upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal normalizer/Borel recognition, with no rank or field-size bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnunipotentnormalizer-normalizer-eq-borel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentNormalizer.normalizer_eq_Borel"),
                H("normalizer eq Borel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality with the actual determinant-one upper triangular subgroup."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
