using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryRankTwoFixedFieldEquivDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary rank two fixed field equiv supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Rank Two Fixed Field Equiv"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-exists-nonzero-trace-zero"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.exists_nonzero_trace_zero"),
                H("exists nonzero trace zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized exists nonzero trace zero statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-coordinateequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.coordinateEquiv"),
                H("coordinateEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An explicit actual group equivalence for any nonzero anti-fixed scaling element."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-coordinateequiv-forward"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.coordinateEquiv_forward"),
                H("coordinateEquiv forward"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateEquiv forward statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-coordinateequiv-backward"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.coordinateEquiv_backward"),
                H("coordinateEquiv backward"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized coordinateEquiv backward statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-specialunitaryequivfixedsl"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.specialUnitaryEquivFixedSL"),
                H("specialUnitaryEquivFixedSL"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One actual equivalence is selected before every group target."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitaryranktwofixedfieldequiv-exists-explicit-fixedfield-equiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv.exists_explicit_fixedField_equiv"),
                H("exists explicit fixedField equiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal constructive endpoint, recording both the actual conjugation and inverse coordinates."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
