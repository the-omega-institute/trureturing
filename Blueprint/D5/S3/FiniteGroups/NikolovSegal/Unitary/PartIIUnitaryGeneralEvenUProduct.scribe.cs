using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryGeneralEvenUProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary general even uproduct supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary General Even UProduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarygeneralevenuproduct-actual-uniform-even-levi-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryGeneralEvenUProduct.actual_uniform_even_Levi_prescribed_product"),
                H("actual uniform even Levi prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual type-A PRODUCT on the central even Levi. The entire prescribed D action is cancelled on ALL central elements; both scalar corrections and ONE ambient SU inner tuple precede all positive type-A targets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarygeneralevenuproduct-actual-uniform-even-p-general-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryGeneralEvenUProduct.actual_uniform_even_P_general_prescribed_product"),
                H("actual uniform even P general prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("General diagonal-similitude/field even P PRODUCT. Real scalar/skew witnesses and exact central powers are transported; ONE ambient unitary inner tuple precedes every actual skew target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarygeneralevenuproduct-actual-uniform-central-even-u-prescribed-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryGeneralEvenUProduct.actual_uniform_central_even_U_prescribed_product"),
                H("actual uniform central even U prescribed product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ENTIRE central even positive unitary U, with arbitrary genuine prescribed D/Phi actions. Derived even U=U2 P and both actual suppliers are consumed; ONE correction precedes ALL targets."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
