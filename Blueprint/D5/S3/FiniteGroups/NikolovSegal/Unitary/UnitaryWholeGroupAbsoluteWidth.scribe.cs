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
            Paragraph(Text("These parameterized results and their consumed helpers support proofs about actual matrix groups over finite fields. Every displayed Lean statement retains its original hypotheses. This package contains no finite enumeration or benchmark-instance deposit. The source geometry is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239. The proof implementation is repository-derived and no originality claim is made. Bare arbitrary automorphism classification, small-field/tiny-rank coverage for the prescribed products, all-family exhaustion and strong completeness are separate obligations. Escape registration is unfinished under CLAUDE3.9 and issue12291; this is not declared_validated registration.")))));
}
