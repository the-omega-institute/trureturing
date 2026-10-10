using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryInnerUNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary inner unormalization supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Inner UNormalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitaryinnerunormalization-mem-specialunitary-iff-hermitian"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInnerUNormalization.mem_specialUnitary_iff_hermitian"),
                H("mem specialUnitary iff hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The subgroup is the literal determinant-one anti-diagonal Hermitian carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryinnerunormalization-inner-positiveu-correction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryInnerUNormalization.inner_positiveU_correction"),
                H("inner positiveU correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every bare actual SU automorphism admits one genuine SU inner correction before all targets. Native finite Sylow conjugacy is applied to the proved literal Sylow, and native normalizer functoriality preserves its actual Borel."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
