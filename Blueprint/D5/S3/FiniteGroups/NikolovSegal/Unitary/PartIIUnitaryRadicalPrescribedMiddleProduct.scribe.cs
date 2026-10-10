using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalPrescribedMiddleProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical prescribed middle product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Prescribed Middle Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalprescribedmiddleproduct-actual-unitary-radical-prescribed-middle-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedMiddleProduct.actual_unitary_radical_prescribed_middle_product"),
                H("actual unitary radical prescribed middle product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual prescribed diagonal-SIMILITUDE/field V* middle PRODUCT. ONE genuine determinant-one unitary inner correction is constructed before EVERY target. No normalization or commutator-coverage premise is retained. Boundary pairs/corner remain subsequent stages."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
