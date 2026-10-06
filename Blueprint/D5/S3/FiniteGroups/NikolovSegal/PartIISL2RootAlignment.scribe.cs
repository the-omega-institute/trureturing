using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIISL2RootAlignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II SL2RootAlignment.",
        H("Part II SL2RootAlignment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiisl2rootalignment-actual-root-conjugate-sl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootAlignment.actual_root_conjugate_SL2_scalar_product"),
                H("actual root conjugate SL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When both root images are the stated actual conjugates, one determinant-one matrix aligns the distinct images to the standard ordered pair. Root reconstruction gives scalar coverage, and the alignment is absorbed into one original correction tuple before every target."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
