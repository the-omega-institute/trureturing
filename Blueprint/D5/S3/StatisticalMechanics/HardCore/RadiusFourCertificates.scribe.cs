using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RadiusFourCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core memory, exact path semantics and integer certificates.",
        H("Certified Radius-Four Growth Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfourmask"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourMask"),
                H("Actual blocked vertices"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Decode the geometric mask in the fixed Manhattan-disk coordinate order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfourstep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourStep"),
                H("Fixed-SRL transitions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only action zero is implemented; other actions return none without any coverage claim. Selected successors are computed from the geometric update and exact lookup."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfourweight"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFourWeight"),
                H("Positive integer potential"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Read the exact positive weight associated with each geometric state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-geometry"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometry"),
                H("Full selected-order geometric closure"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Check all 851 states and three directions, distinct masks, initial state, parent retention and origin exclusion. Option-map equality preserves each direction, including absent children."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-potential"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_potential"),
                H("Exact integer row certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every weight is between one and twenty thousand. Ten thousand times the child-weight sum is at most 24827 times the parent weight. The root weight is exactly twenty thousand. Equality in a row is allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-table-upper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_table_upper"),
                H("All-depth represented count bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing super-potential induction supplies the quantitative bound for every state, depth and history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-geometric-upper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_geometric_upper"),
                H("Transport to the raw geometric process"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact fixed-order presentation semantics transfers the bound to the actual radius-four memory rooted at the parent-blocked set. No spectral-fit or supplied count-equality premise remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-finite-domain-upper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_finite_domain_upper"),
                H("An actual finite-domain consumer"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integer-grid vertex set with the parent absent, the raw ordered deletion count has prefactor twenty thousand and rate at most 24827 over ten thousand. Real domain membership determines child availability. Partition-polynomial and complex zero-free consequences remain separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusfourcertificates-radiusfour-beats-every-radiusthree-controller"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusFourCertificates.radiusFour_beats_every_radiusThree_controller"),
                H("A finite universal separation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At depth seven hundred, the fixed-SRL radius-four count is strictly below the count of every history-dependent radius-three controller. The proof combines the actual two model certificates with an exact integer comparison; it does not enumerate policies or transfer a relaxed-model lower bound to the physical grid."))),
                DescribeRole.Theorem))));
}
