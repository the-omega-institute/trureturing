using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class UnitaryWidthRadicalNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual unitary width radical normalization supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Unitary Width Radical Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-slcentral-transpose"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.slCentral_transpose"),
                H("slCentral transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized slCentral transpose statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-centralembed-transpose"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.centralEmbed_transpose"),
                H("centralEmbed transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized centralEmbed transpose statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-centralembed-positive"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.centralEmbed_positive"),
                H("centralEmbed positive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized centralEmbed positive statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-centralembed-negative"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.centralEmbed_negative"),
                H("centralEmbed negative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized centralEmbed negative statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-central-conjugate-downradical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.central_conjugate_downRadical"),
                H("central conjugate downRadical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual opposite radical is normalized by every actual central SU."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-upradical-one"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.upRadical_one"),
                H("upRadical one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized upRadical one statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-downradical-one"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.downRadical_one"),
                H("downRadical one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized downRadical one statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-upradical-inv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.upRadical_inv"),
                H("upRadical inv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized upRadical inv statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-downradical-inv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.downRadical_inv"),
                H("downRadical inv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized downRadical inv statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-positive-levi-radical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.positive_levi_radical"),
                H("positive levi radical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The accepted actual U=Levi*radical decomposition, in the literal SU carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-unitarywidthradicalnormalization-negative-levi-radical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization.negative_levi_radical"),
                H("negative levi radical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine opposite decomposition, with the Levi moved to the left by proved normalization."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
