using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryTypeALeviProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary type alevi product supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Type ALevi Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytypealeviproduct-levi"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct.levi"),
                H("levi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized levi statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytypealeviproduct-diagonalfield"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct.diagonalField"),
                H("diagonalField"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized diagonalField statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytypealeviproduct-actual-diagonalfield-preserves-unitary"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct.actual_diagonalField_preserves_unitary"),
                H("actual diagonalField preserves unitary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The manufactured diagonal/field actions are genuine unitary actions on the WHOLE actual SU subgroup, not merely on the displayed Levi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitarytypealeviproduct-actual-uniform-unitary-typea-levi-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryTypeALeviProduct.actual_uniform_unitary_typeA_Levi_product"),
                H("actual uniform unitary typeA Levi product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uniform prescribed-power VALUE coverage of the actual U2 inside SU(2d+2), consuming the PROVED Proposition6.5, not a coverage premise. N(q),FIELD cutoff precede all groups/ranks/action/divisor tuples. ONE ambient determinant-one UNITARY correction tuple precedes ALL targets; every witness is an actual positive UNITARY matrix in the type-A Levi."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
