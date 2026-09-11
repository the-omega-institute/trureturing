using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class AdaptiveRadiusFourCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive radius-four geometric coverage for the zero-freeness proof.",
        H("Adaptive radius-four certificates"),
        Blocks(
            Describe.Lean(DescribeId.Create("adaptive-r4-mask"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourMask"),
                H("Actual blocked vertices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer mask decodes to actual grid points in the full lexicographic Manhattan disk. Distinct codes are checked; no numerical-weight quotient replaces the geometry."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-choice"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourChoice"),
                H("Selected local order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit state-dependent controller selects one of six orders."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-step"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourStep"),
                H("Geometrically computed successor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The successor is obtained by computing memoryStep and looking up its exact mask. The unused action argument fits the shared counting API; only the selected order is certified. No supplied transition list is trusted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-weight"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFourWeight"),
                H("Stored integer weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original integer weight payload is retained as a public accessor."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-geometry"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.radiusFour_geometry"),
                H("Complete selected geometric closure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All 881 masks and all 2643 selected direction cases are checked against actual integer-grid updates. A failed lookup cannot be accepted as a blocked move unless that direction is genuinely in the mask."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("adaptive-r4-root-direction"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDirection"),
                H("Four root directions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unconditioned root has east, south, north and west directions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-root-domain"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootDomain"),
                H("Actual root branch domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root and earlier neighbors are deleted before the chosen branch is translated and rotated. Its parent is proved absent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adaptive-r4-root-count"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveRadiusFourCertificates.rootCount"),
                H("Full root deletion count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual domain membership decides root and child availability. Nonroot branches use the same certified adaptive controller."))), DescribeRole.Definition),
            Paragraph(Text("The finite geometric checks are replayed by Lean's kernel. Resource measurements are recorded separately.")))));
}
