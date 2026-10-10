using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryLeviDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary levi decomposition supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Levi Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarylevidecomposition-actual-steinberg-central-levi"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition.actual_steinberg_central_levi"),
                H("actual steinberg central levi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual steinberg central levi statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarylevidecomposition-actual-steinberg-radical-mem"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition.actual_steinberg_radical_mem"),
                H("actual steinberg radical mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual steinberg radical mem statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarylevidecomposition-actual-levi-radical-middle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition.actual_levi_radical_middle"),
                H("actual levi radical middle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal middle block after multiplying by an arbitrary radical factor. No commutation of the two factors is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarylevidecomposition-actual-unitary-ambient-u-decomposition"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryLeviDecomposition.actual_unitary_ambient_U_decomposition"),
                H("actual unitary ambient U decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact p255 unitary decomposition on the actual central SU(n) and actual V*=V intersect Fix(Steinberg). The fixed-point facts are DERIVED from the original target; no off-block/unitary coverage is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
