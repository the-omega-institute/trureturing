using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryCentralEvenProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary central even product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Central Even Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarycentralevenproduct-actual-uniform-central-even-u-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryCentralEvenProduct.actual_uniform_central_even_U_product"),
                H("actual uniform central even U product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual uniform prescribed diagonal/field VALUE coverage of the ENTIRE even-dimensional central positive unitary U1. Length/cutoff precede all fields/ranks/tuples; ONE ambient unitary h precedes all actual targets b, and every witness is positive UNITARY."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
