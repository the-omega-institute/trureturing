using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL3UnipotentWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL3UnipotentWidth.",
        H("Part II SL3UnipotentWidth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidth-triangular-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.triangular_factor"),
                H("triangular factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every upper-triangular determinant-one three-by-three matrix factors as the upper-left diag2(a) block, the lower-right diag2(b) block, and one actual U3 element, with a and b nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidth-diagonal01-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal01_factor"),
                H("diagonal01 factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero a over any field, the actual upper-left diag2(a) block is the ordered six-factor product upper3(a,0,0), lower3(-a inverse,0,0), upper3(a,0,0), upper3(-1,0,0), lower3(1,0,0), upper3(-1,0,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidth-diagonal12-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.diagonal12_factor"),
                H("diagonal12 factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero b over any field, the actual lower-right diag2(b) block is the ordered six-factor product upper3(0,b,0), lower3(0,-b inverse,0), upper3(0,b,0), upper3(0,-1,0), lower3(0,1,0), upper3(0,-1,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl3unipotentwidth-alternating-unipotent-25"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth.alternating_unipotent_25"),
                H("alternating unipotent 25"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual SL3 matrix over every field is an ordered product of exactly 25 factors, in actual upper U3 at even indices and lower U3 at odd indices. Four pivot operations, two embedded SL2 diagonal decompositions and identity padding supply the witnesses, including fields of sizes two and three."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), Section 6, Proposition 6.2, and Lemma 7.1(a) with its A2 orbital application (pages 257-261). These are formal adaptations and consequences of published mathematics, using actual matrix geometry, finite-field arithmetic and Sylow arguments. No originality claim or redistribution of the papers is made. The scalar, twisted and transitive conclusions here concern the SL3 family. Other families, CFSG exhaustion, general central covers, the full all-simple scalar supplier, all-length Proposition 10.2, width and restricted Burnside bounds, and strong completeness remain open.")))));
}
