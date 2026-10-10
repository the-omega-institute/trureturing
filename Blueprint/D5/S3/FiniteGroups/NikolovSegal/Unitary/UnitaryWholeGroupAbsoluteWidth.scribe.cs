using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWholeGroupAbsoluteWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One absolute positive length K=5 precedes every finite field, every natural rank, every nonidentity involutive field automorphism and every actual special-unitary target. Five ordered factors lie in the same determinant-one Hermitian special-unitary carrier and alternate U,L,U,L,U. Ranks0,1,2,3 and characteristic2 are retained. Genuine central-Levi reduction and absorption keep the length independent of rank and field size.",
        H("Unitary Whole Group Absolute Width"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywholegroupabsolutewidth-five-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth.five_factor"),
                H("five factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every rank, including zero/one, every finite quadratic field, and every actual SU target. There is no supplied generation or factorization premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywholegroupabsolutewidth-alternating-five"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth.alternating_five"),
                H("alternating five"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal ordered-factor endpoint, with five genuine alternating SU factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywholegroupabsolutewidth-exists-absolute-unitriangular-width"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth.exists_absolute_unitriangular_width"),
                H("exists absolute unitriangular width"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ONE positive absolute length BEFORE every field, rank, involution and target. All factors belong to the SAME literal determinant-one Hermitian SU carrier."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
