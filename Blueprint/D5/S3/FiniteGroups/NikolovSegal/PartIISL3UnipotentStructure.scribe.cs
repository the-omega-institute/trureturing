using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL3UnipotentStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL3UnipotentStructure.",
        H("Part II SL3UnipotentStructure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentstructure-mem-u3-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure.mem_U3_iff"),
                H("mem U3 iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over every field, membership in the actual SL3 upper-unitriangular subgroup is equivalent to all entries below the diagonal being zero and all three diagonal entries being one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentstructure-card-u3"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure.card_U3"),
                H("card U3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual upper-unitriangular SL3 subgroup has Nat.card equal to (Nat.card F)^3, through its three field coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentstructure-first-column-of-fix"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure.first_column_of_fix"),
                H("first column of fix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A determinant-one matrix fixing the first standard vector has first column (1,0,0). The equality follows from the literal matrix-vector action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentstructure-bottomblock-det"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure.bottomBlock_det"),
                H("bottomBlock det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If an actual SL3 matrix fixes the first standard vector, its bottom-right two-by-two block has determinant one. This gives a genuine SL2 action of a first-vector stabilizer."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
