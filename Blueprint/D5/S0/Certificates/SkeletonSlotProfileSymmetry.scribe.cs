using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SkeletonSlotProfileSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SkeletonSlotProfileSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite gap constraints and a complete proved renaming cover for the original typed slot semantics.",
        H("SkeletonSlotProfileSymmetry"),
        Blocks(
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-relabel"),
                DeclarationHandle.Create(Prefix + "relabel"), H("relabel"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rename slots while retaining exactly the same Skeleton object."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-relabel_gap"),
                DeclarationHandle.Create(Prefix + "relabel_gap"), H("relabel_gap"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Gap transition rows transform by conjugacy, including all self-loops."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-relabel_readout"),
                DeclarationHandle.Create(Prefix + "relabel_readout"), H("relabel_readout"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both observed channels transform with the slot names."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-profilecode"),
                DeclarationHandle.Create(Prefix + "profileCode"), H("profileCode"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A joint output code orders profiles, without identifying equal profiles."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-orderedfive"),
                DeclarationHandle.Create(Prefix + "orderedFive"), H("orderedFive"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sort only the two slots not named by the three distinct-output observations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-orderedfive_profiles"),
                DeclarationHandle.Create(Prefix + "orderedFive_profiles"), H("orderedFive_profiles"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every five-slot realization has an equivalent ordered profile presentation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-orderedfive_anchor"),
                DeclarationHandle.Create(Prefix + "orderedFive_anchor"), H("orderedFive_anchor"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output and return of each named anchor are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-fiveoutputcases"),
                DeclarationHandle.Create(Prefix + "fiveOutputCases"), H("fiveOutputCases"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three anchored Boolean post-zero outputs and two ordered six-valued extra profiles. The actual digit labels on each extra slot are 1,2,3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-fiveoutputcases_card"),
                DeclarationHandle.Create(Prefix + "fiveOutputCases_card"), H("fiveOutputCases_card"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete ordered output enumeration, not a sample-search result."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("skeletonslotprofilesymmetry-fiveoutputcases_cover"),
                DeclarationHandle.Create(Prefix + "fiveOutputCases_cover"), H("fiveOutputCases_cover"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Either the extra profiles are already ordered or their interchange is."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/SkeletonSlotGapConstraintTransport"))]));
}
