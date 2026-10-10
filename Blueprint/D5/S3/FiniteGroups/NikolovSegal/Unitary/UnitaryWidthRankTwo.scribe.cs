using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWidthRankTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary width rank two supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Width Rank Two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthranktwo-ranktwocarrierequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo.rankTwoCarrierEquiv"),
                H("rankTwoCarrierEquiv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized rankTwoCarrierEquiv statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthranktwo-ranktwo-four-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo.rankTwo_four_factor"),
                H("rankTwo four factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Absolute four-factor width on actual SU2 over every finite quadratic field. There is no field-size or characteristic cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthranktwo-trivial-four-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo.trivial_four_factor"),
                H("trivial four factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Degenerate ranks remain literal actual SU groups."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthranktwo-ranktwo-alternating-25"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRankTwo.rankTwo_alternating_25"),
                H("rankTwo alternating 25"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The desired literal ordered Fin25 endpoint, fully closed on the rank-two base."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
