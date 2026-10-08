using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3UnipotentNormalizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 UnipotentNormalizer.",
        H("Actual PSL3 UnipotentNormalizer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-conjugate-eq-of-quotient-eq"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.conjugate_eq_of_quotient_eq"),
                H("conjugate eq of quotient eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, if actual upper-unitriangular x and y have equal projective classes after conjugating x by an arbitrary SL3 matrix A, then A*x*A^-1=y in SL3. Trace and determinant force the central discrepancy to one, including characteristic three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-projective-conjugate-mem-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.projective_conjugate_mem_iff"),
                H("projective conjugate mem iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field and arbitrary SL3 conjugator A, the projective conjugate of an actual U3 element belongs to the projective upper subgroup exactly when its actual conjugate belongs to U3. The proved central-discrepancy elimination supplies the lifting step."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-quotient-mem-normalizer-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.quotient_mem_normalizer_iff"),
                H("quotient mem normalizer iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, an actual SL3 matrix maps into the normalizer of literal projective U3 exactly when it normalizes actual SL3 U3. Both conjugation directions use the proved quotient discrepancy elimination; no flag or lift premise is supplied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-mem-projective-normalizer-iff-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.mem_projective_normalizer_iff_upper"),
                H("mem projective normalizer iff upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, actual projective U3 normalizer membership is exactly existence of an upper-triangular determinant-one SL3 representative. The admitted actual SL3 normalizer recognition is applied after the proved projective preimage criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-automorphism-projective-normalizer-map"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.automorphism_projective_normalizer_map"),
                H("automorphism projective normalizer map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine bare projective automorphism preserving actual projective U3 also preserves its literal normalizer. The actual normalizer functoriality identity is a consumed companion of projective torus alignment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentnormalizer-automorphism-upper-representative-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer.automorphism_upper_representative_iff"),
                H("automorphism upper representative iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a genuine bare projective automorphism preserving actual projective U3, existence of an upper-triangular determinant-one representative is equivalent before and after applying the automorphism. The proved normalizer criterion retains the actual quotient representatives."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
