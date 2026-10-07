using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2RootSylowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2RootSylow.",
        H("Part II SL2RootSylow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-mem-upperroot"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot"),
                H("mem upperRoot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual upper-root subgroup consists exactly of determinant-one transvections upper(t), with t in the field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-upper-mem-upperroot"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upper_mem_upperRoot"),
                H("upper mem upperRoot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each actual upper transvection belongs to the upper-root subgroup. This supplies the concrete root elements in the subgroup argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-upperhom-injective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperHom_injective"),
                H("upperHom injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upper transvection homomorphism from the multiplicative form of the additive field is injective, by its upper-right matrix entry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-mem-upperroot-iff-fix-first"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.mem_upperRoot_iff_fix_first"),
                H("mem upperRoot iff fix first"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A determinant-one matrix belongs to the actual upper-root subgroup exactly when it fixes the first standard vector. The matrix-entry equations recover the transvection parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-upperroot-ispgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_isPGroup"),
                H("upperRoot isPGroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In characteristic p with p prime, the upper-root subgroup is a p-group because its elements come from the additive field. This includes every finite field of characteristic two or three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-psubgroup-fixed-vector"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.pSubgroup_fixed_vector"),
                H("pSubgroup fixed vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a finite field of characteristic p, every p-subgroup of SL2 fixes an actual nonzero vector. The fixed-point counting congruence excludes a fixed set containing only zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-upperroot-p-maximal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.upperRoot_p_maximal"),
                H("upperRoot p maximal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any p-subgroup containing the actual upper-root subgroup equals it. A common nonzero fixed vector is forced onto the first coordinate line, and all subgroup matrices then fix the first standard vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootsylow-automorphism-upperroot-conjugate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow.automorphism_upperRoot_conjugate"),
                H("automorphism upperRoot conjugate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every genuine SL2 automorphism over a finite field sends the actual upper-root subgroup to an inner conjugate. The proved p-maximal subgroup is a Sylow subgroup, and Sylow conjugacy supplies the determinant-one matrix; no root-image oracle is a hypothesis."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
