using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryPrescribedLowerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary prescribed lower product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Prescribed Lower Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryprescribedlowerproduct-actual-uniform-all-rank-unitary-lower-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryPrescribedLowerProduct.actual_uniform_all_rank_unitary_lower_prescribed_product"),
                H("actual uniform all rank unitary lower prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ONE uniform length/cutoff precedes every field/rank/genuine prescribed D/Phi tuple. Actual lower unitary targets have genuine lower unitary witnesses; ONE global SU correction precedes ALL targets, with exact ordered original divisor powers. No opposite transport is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
