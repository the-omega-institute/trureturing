using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryAmbientGeneralEvenUProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary ambient general even uproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Ambient General Even UProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryambientgeneralevenuproduct-actual-uniform-ambient-even-u-general-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientGeneralEvenUProduct.actual_uniform_ambient_even_U_general_prescribed_product"),
                H("actual uniform ambient even U general prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Entire actual positive U in all even ranks 2(d+2)+2, arbitrary genuine prescribed D/Phi tuples. Both decompositions and all three suppliers are proved inputs; no coverage, lift or action/power identity is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
