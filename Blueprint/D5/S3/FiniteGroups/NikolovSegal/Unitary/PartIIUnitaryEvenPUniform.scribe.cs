using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryEvenPUniformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary even puniform supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Even PUniform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryevenpuniform-actual-even-p-prescribed-two-batch"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPUniform.actual_even_P_prescribed_two_batch"),
                H("actual even P prescribed two batch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary genuine paired diagonal/field P tuples. Their ONE ambient unitary INNER correction is constructed BEFORE every P target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryevenpuniform-actual-uniform-even-p-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryEvenPUniform.actual_uniform_even_P_prescribed_product"),
                H("actual uniform even P prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Chosen-length, all-rank EVEN P Proposition6.10 branch. N(q) and the FIELD cutoff are fixed before every field/rank/prescribed tuple. ONE ambient inner correction is fixed before ALL actual P targets; the witnesses are positive UNITARY ambient matrices, and values are ordered."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
