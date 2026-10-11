using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL3UnipotentWidthGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL3UnipotentWidthGeometry.",
        H("Part II SL3UnipotentWidthGeometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-lower3-mem"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.lower3_mem"),
                H("lower3 mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual transpose chart lower3(a,b,c) belongs to the lower-unitriangular SL3 subgroup, over any field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-mem-lowerunipotent-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.mem_lowerUnipotent_iff"),
                H("mem lowerUnipotent iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership in the actual lower-unitriangular subgroup is equivalent to all entries above the diagonal being zero and all diagonal entries being one, over every field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block01-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_coe"),
                H("block01 coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upper-left SL2 embedding is the actual three-by-three matrix with the SL2 block in indices zero and one and a final diagonal entry one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block12-coe"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_coe"),
                H("block12 coe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower-right SL2 embedding is the actual three-by-three matrix with first diagonal entry one and the SL2 block in indices one and two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block01-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_upper"),
                H("block01 upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upper-left SL2 embedding sends its upper transvection of parameter t to upper3(t,0,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block01-lower"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block01_lower"),
                H("block01 lower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upper-left SL2 embedding sends its lower transvection of parameter t to lower3(t,0,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block12-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_upper"),
                H("block12 upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower-right SL2 embedding sends its upper transvection of parameter t to upper3(0,t,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-block12-lower"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.block12_lower"),
                H("block12 lower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower-right SL2 embedding sends its lower transvection of parameter t to lower3(0,t,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-first-pivot"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.first_pivot"),
                H("first pivot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every SL3 matrix over any field, some upper3(a,0,c) row operation makes the first diagonal entry nonzero. A zero first column would contradict determinant one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidthgeometry-eliminate-to-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidthGeometry.eliminate_to_upper"),
                H("eliminate to upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, four actual alternating row operations from U3, lower U3, U3, lower U3 make any SL3 matrix upper triangular. The actual nesting v3*(v2*(v1*(v0*g))) and subgroup memberships are retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
