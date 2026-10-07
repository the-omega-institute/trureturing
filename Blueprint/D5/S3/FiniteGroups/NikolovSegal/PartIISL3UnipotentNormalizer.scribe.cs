using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL3UnipotentNormalizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL3UnipotentNormalizer.",
        H("Part II SL3UnipotentNormalizer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentnormalizer-below-diagonal-zero-of-normalizer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer.below_diagonal_zero_of_normalizer"),
                H("below diagonal zero of normalizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every element of the normalizer of the actual upper-unitriangular subgroup has all entries below the diagonal equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentnormalizer-conjugate-mem-u3-of-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer.conjugate_mem_U3_of_upper"),
                H("conjugate mem U3 of upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by an actual upper-triangular SL3 matrix preserves every upper-unitriangular matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentnormalizer-mem-normalizer-iff-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer.mem_normalizer_iff_upper"),
                H("mem normalizer iff upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual SL3 matrix normalizes the upper-unitriangular subgroup exactly when it is upper triangular. This holds over every field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentnormalizer-automorphism-normalizer-map"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer.automorphism_normalizer_map"),
                H("automorphism normalizer map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine automorphism preserving the actual upper-unitriangular subgroup also preserves its normalizer as a subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentnormalizer-automorphism-upper-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer.automorphism_upper_iff"),
                H("automorphism upper iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an automorphism preserving the actual upper-unitriangular subgroup, beta(g) is upper triangular exactly when g is upper triangular."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
