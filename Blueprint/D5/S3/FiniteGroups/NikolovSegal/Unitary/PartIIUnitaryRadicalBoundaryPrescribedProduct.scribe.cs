using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalBoundaryPrescribedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical boundary prescribed product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Boundary Prescribed Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalboundaryprescribedproduct-actual-unitary-radical-boundary-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalBoundaryPrescribedProduct.actual_unitary_radical_boundary_prescribed_product"),
                H("actual unitary radical boundary prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("True arbitrary prescribed diagonal-SIMILITUDE/field exceptional pair PRODUCT. The original positive s|q scalar supplier is consumed; all targets use the SAME pre-target actual unitary h, and witnesses have genuine axis support with corners retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
