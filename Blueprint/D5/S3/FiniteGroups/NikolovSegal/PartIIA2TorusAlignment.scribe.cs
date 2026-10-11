using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2TorusAlignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2TorusAlignment.",
        H("Part II A2TorusAlignment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2torusalignment-upper-finite-subgroup-diagonal-alignment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2TorusAlignment.upper_finite_subgroup_diagonal_alignment"),
                H("upper finite subgroup diagonal alignment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite subgroup K of upper-triangular SL3 matrices whose cardinality is nonzero in F, one upper-unitriangular u simultaneously conjugates every k by u inverse*k*u to its diagonal matrix. Averaging constructs this common alignment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2torusalignment-actual-torus-image-unipotent-alignment"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2TorusAlignment.actual_torus_image_unipotent_alignment"),
                H("actual torus image unipotent alignment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite field and a genuine automorphism whose actual diagonal-pair images are upper triangular, one actual upper-unitriangular matrix simultaneously makes every such image diagonal, with its original diagonal entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2torusalignment-actual-bare-sl3-u-torus-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2TorusAlignment.actual_bare_SL3_U_torus_normalization"),
                H("actual bare SL3 U torus normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every bare SL3 automorphism over any finite field, one actual inner correction makes both the upper-unitriangular subgroup and the diagonal torus invariant. The statement imposes no field-size cutoff."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
