using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryAmbientEvenUProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary ambient even uproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Ambient Even UProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryambientevenuproduct-actual-uniform-ambient-even-u-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryAmbientEvenUProduct.actual_uniform_ambient_even_U_product"),
                H("actual uniform ambient even U product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ALL actual positive unitary targets in every even ambient rank 2(d+2)+2. Chosen length/cutoff precede every field/rank/tuple, ONE actual unitary inner correction precedes ALL targets, and actual positive unitary witnesses give the ordered exact-length VALUES. No central/radical/decomposition/coverage premise is retained."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
