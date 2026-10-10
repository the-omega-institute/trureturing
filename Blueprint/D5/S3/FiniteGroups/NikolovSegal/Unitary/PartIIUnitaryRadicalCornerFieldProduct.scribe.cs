using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalCornerFieldProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical corner field product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Corner Field Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalcornerfieldproduct-actual-unitary-radical-corner-field-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalCornerFieldProduct.actual_unitary_radical_corner_field_product"),
                H("actual unitary radical corner field product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("True trace-zero corner supplier. The SAME determinant-one unitary h tuple is fixed before every trace-zero target and all witnesses are actual central V* matrices. It CONSUMES the proved F0 scalar kernel, not a supplied corner/whole-block coverage statement."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
