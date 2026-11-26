using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalAmbientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbient";
    private const string Title = "Vertical prime exclusion on the ordered native chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalambient"),
                DeclarationHandle.Create(Module + ".no_vertical_prime"),
                H("Vertical height-one prime exclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least three, a height-one prime of the simple nonzero ordered-root chart with nonzero contraction to the root polynomial ring cannot contain all ten native maximal minors. Quotient specialization gives criticality on each admissible generic paired section, where the section minors supply a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-generic-section-descent"),
                DeclarationHandle.Create(Module + ".genericSectionNativeCritical_of_heightOne"),
                H("Descent from height one to the generic section"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the prime contains a nonzero root polynomial and all native maximal minors, the induced generic paired sections have native rank deficiency."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-vertical-mass-open"),
                DeclarationHandle.Create(Module + ".no_vertical_prime_massOpen"),
                H("Vertical height-one prime exclusion on the mass open"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Localizing at the exact raw mass preserves the height of the contracted prime. For m at least three, a height-one prime with nonzero root contraction cannot contain all ten localized native maximal minors."))),
                DescribeRole.Theorem))));
}
