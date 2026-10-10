using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryPrescribedUProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary prescribed uproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Prescribed UProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryprescribeduproduct-actual-uniform-all-rank-unitary-u-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedUProduct.actual_uniform_all_rank_unitary_U_prescribed_product"),
                H("actual uniform all rank unitary U prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary-rank, arbitrary genuine prescribed diagonal-similitude/field positive-U PRODUCT. The same fixed length and field cutoff cover BOTH parities; ONE global SU correction is chosen BEFORE all targets."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
