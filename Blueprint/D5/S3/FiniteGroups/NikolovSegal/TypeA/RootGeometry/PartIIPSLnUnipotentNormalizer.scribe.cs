using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry;

internal sealed class PartIIPSLnUnipotentNormalizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A PSLn Unipotent Normalizer.",
        H("Type-A PSLn Unipotent Normalizer"),
        Blocks(
            Paragraph(Text("The actual projective upper-unitriangular normalizer in every rank, over every field. The actual SLn normalizer proof is imported unchanged. Characteristic polynomials eliminate central discrepancies without any rank, characteristic, finiteness or automorphism-lift premise.")),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-projectiveuplus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projectiveUplus"),
                H("projectiveUplus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual central-quotient image of the full SLn upper unitriangular subgroup."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-scalar-unitriangular-charpoly"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.scalar_unitriangular_charpoly"),
                H("scalar unitriangular charpoly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("triangular characteristic-polynomial recognition applied to the actual scalar multiple of a literal unitriangular matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-conjugate-eq-of-quotient-eq"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.conjugate_eq_of_quotient_eq"),
                H("conjugate eq of quotient eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of projective conjugates of actual unitriangular matrices lifts to actual SLn equality. The rank0/1 cases use subsingletons; in positive higher ranks evaluation of the actual charpoly at1 forces the central scalar z to equal1, even when the characteristic divides the rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-projective-conjugate-mem-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_conjugate_mem_iff"),
                H("projective conjugate mem iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Projective conjugation membership lifts on the actual unitriangular carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-quotient-mem-normalizer-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff"),
                H("quotient mem normalizer iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact normalizer preimage under the actual central quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-quotient-mem-normalizer-iff-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.quotient_mem_normalizer_iff_upper"),
                H("quotient mem normalizer iff upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal every-field/all-rank recognition of projective normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-mem-projective-normalizer-iff-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.mem_projective_normalizer_iff_upper"),
                H("mem projective normalizer iff upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual projective element normalizes precisely when it admits an actual determinant-one upper triangular representative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiipslnunipotentnormalizer-projective-normalizer-eq-map-borel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer.projective_normalizer_eq_map_Borel"),
                H("projective normalizer eq map Borel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of actual subgroups: the projective normalizer is the quotient image of the literal determinant-one Borel, in every rank and field."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
