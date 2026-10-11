using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL3UnipotentGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual PSL3 UnipotentGeometry.",
        H("Actual PSL3 UnipotentGeometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-u3-center-trivial"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.U3_center_trivial"),
                H("U3 center trivial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, an actual upper-unitriangular determinant-one SL3 matrix in the literal SL3 center equals one: native scalar-center recognition and its unit diagonal force the scalar to one. No central-intersection premise is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-quotient-u3-injective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.quotient_U3_injective"),
                H("quotient U3 injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, the actual SL3 central quotient is injective on actual U3. Its kernel is proved trivial using U3_center_trivial; projective upper coordinates remain genuine coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-mem-projectiveupperunipotent"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveUpperUnipotent"),
                H("mem projectiveUpperUnipotent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, membership in the actual projective upper subgroup is exactly existence of three field coordinates a,b,c whose literal upper3 matrix has that projective class."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-projectiveupperequiv-apply"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperEquiv_apply"),
                H("projectiveUpperEquiv apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine projectiveUpperEquiv from actual U3 to its quotient image applies by the literal central quotient on the actual matrix representative. Its injectivity uses the proved trivial central intersection; it is consumed by the projective center and root proofs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-projectiveuppercoordinate-apply"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperCoordinate_apply"),
                H("projectiveUpperCoordinate apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The projective upper-coordinate equivalence sends v to the class of upper3(v(0),v(1),v(2)). The transported group equivalence preserves the noncommutative three-coordinate structure over every field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-projectiveuppersylow-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.projectiveUpperSylow_coe"),
                H("projectiveUpperSylow coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field of characteristic prime p, the mapped actual SL3 p-Sylow has exactly the literal projective upper subgroup as underlying subgroup. This identity supplies the bare projective automorphism normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-exists-projectiveupper-sylow"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.exists_projectiveUpper_sylow"),
                H("exists projectiveUpper sylow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field with a declared prime defining characteristic p, the actual projective upper subgroup is the underlying subgroup of a genuine p-Sylow. Native surjective Sylow mapping is consumed without a simplicity or field-size premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-automorphism-projectiveupper-conjugate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_conjugate"),
                H("automorphism projectiveUpper conjugate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field of prime defining characteristic p and every genuine bare PSL3 automorphism beta, beta maps the literal projective upper subgroup to its conjugate by one actual projective element. The proof uses actual Sylow conjugacy and assumes no SL3 automorphism lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-automorphism-projectiveupper-normalize"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.automorphism_projectiveUpper_normalize"),
                H("automorphism projectiveUpper normalize"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field of prime defining characteristic p and every bare PSL3 automorphism beta, one actual projective g gives beta(V)=gVg^-1 and (conj g^-1)*beta preserves V. This direction and the actual conjugating element supply the later root and torus normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-mem-projectivelowerunipotent-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.mem_projectiveLowerUnipotent_iff"),
                H("mem projectiveLowerUnipotent iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, membership in the literal projective lower subgroup is exactly existence of an SL3 representative with all entries above the diagonal zero and every diagonal entry one. It is the quotient image of the admitted actual lower subgroup."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl3unipotentgeometry-alternating-unipotent-25"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentGeometry.alternating_unipotent_25"),
                H("alternating unipotent 25"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, every actual PSL3 element has exactly 25 ordered factors, with even indices in the literal projective upper subgroup and odd indices in the literal projective lower subgroup. The actual SL3 decomposition is transported through the genuine quotient, retaining order and actual representatives. This consumed companion supplies the full-group scalar product."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50) (pages228-232). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1 (pages247-248), Sections2 and6, Proposition6.2, and Lemma7.1(a) with its A2 orbital application (pages257-261). These are formal adaptations and consequences of published mathematics, using actual matrix/quotient geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. This package concerns the PSL3 family only. Other families, general-rank SLn/PSLn, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition10.2, width/RBP and strong completeness remain open. Registration remains unfinished under the current suspension.")))));
}
