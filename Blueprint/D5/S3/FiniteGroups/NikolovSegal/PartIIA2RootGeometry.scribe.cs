using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIA2RootGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II A2RootGeometry.",
        H("Part II A2RootGeometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootgeometry-mem-center-u3-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry.mem_center_U3_iff"),
                H("mem center U3 iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An element of the actual upper-unitriangular subgroup is central exactly when its matrix is upper3(0,0,t) for a field parameter t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootgeometry-actual-u-preserving-central-root-map"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry.actual_U_preserving_central_root_map"),
                H("actual U preserving central root map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine SL3 automorphism preserving actual U3 also preserves its actual central (0,2) positive-root subgroup, over every finite field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiia2rootgeometry-actual-bare-sl3-u-t-central-root-normalization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry.actual_bare_SL3_U_T_central_root_normalization"),
                H("actual bare SL3 U T central root normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every finite field, one actual inner correction to a bare SL3 automorphism simultaneously preserves U3, the diagonal torus, and the actual central positive-root subgroup."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
