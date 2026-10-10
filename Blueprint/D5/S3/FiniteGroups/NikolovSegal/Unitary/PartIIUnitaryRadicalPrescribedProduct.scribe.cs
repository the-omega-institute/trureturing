using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalPrescribedProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical prescribed product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Prescribed Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalprescribedproduct-actual-unitary-radical-prescribed-four-batch"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedProduct.actual_unitary_radical_prescribed_four_batch"),
                H("actual unitary radical prescribed four batch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full actual V* prescribed D Phi PRODUCT in four ordered batches. The four correction tuples (one global tuple) precede EVERY target. Middle, both exceptional root pairs and the noncommutative corner are truly reconstructed from actual unitary witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicalprescribedproduct-actual-uniform-unitary-radical-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedProduct.actual_uniform_unitary_radical_prescribed_product"),
                H("actual uniform unitary radical prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Chosen positive length/cutoff BEFORE ALL fields/ranks/diagonal-SIMILITUDE/field tuples. ONE actual SU inner correction precedes every FULL radical target; ordered exact-length commutator VALUES, actual V* witnesses and every original positive divisor power are retained. Whole SU/bare classification are further obligations."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
