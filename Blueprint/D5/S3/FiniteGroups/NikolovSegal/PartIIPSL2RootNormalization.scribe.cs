using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class PartIIPSL2RootNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Part II PSL2RootNormalization.",
        H("Part II PSL2RootNormalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl2rootnormalization-actual-root-stabilizing-psl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL2RootNormalization.actual_root_stabilizing_PSL2_scalar_product"),
                H("actual root stabilizing PSL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bare PSL2 automorphisms preserving the actual projective upper and lower ranges satisfy scalar PRODUCT under the quantitative bounds. Injective root coordinates, Weyl relations and field reconstruction work directly in the centre quotient; no automorphism lift is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-partiipsl2rootnormalization-actual-root-conjugate-psl2-scalar-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/PartIIPSL2RootNormalization.actual_root_conjugate_PSL2_scalar_product"),
                H("actual root conjugate PSL2 scalar product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For bare PSL2 automorphisms with the stated projective root-image conjugacies, distinct root-pair alignment and direct quotient reconstruction supply the literal scalar PRODUCT. The correction absorbs the aligning matrix before all targets; there is no lift premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.")))));
}
