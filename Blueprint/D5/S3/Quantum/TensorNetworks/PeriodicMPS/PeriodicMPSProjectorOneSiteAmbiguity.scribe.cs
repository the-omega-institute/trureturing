using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSProjectorOneSiteAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectorOneSiteAmbiguity";
    private static LibraryNoteRef CritchMorton => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic one-site ambiguity in the compact periodic MPS projector space",
        H("Generic one-site ambiguity in the compact periodic MPS projector space"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-mps-projector-one-site-observation"),
                DeclarationHandle.Create(Module + ".oneSiteObservation"),
                H("Single-site observation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Trace out the second site in the adjacent-pair partial trace of the full projector."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("periodic-mps-projector-one-site-trace"),
                DeclarationHandle.Create(Module + ".trace_oneSiteObservation_of_mem_closure"),
                H("Trace one on the compact closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On an actual projector, the one-site trace before normalization is the total squared amplitude mass. Division by that positive mass gives trace one. This identity extends to the projector closure by continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-mps-projector-one-site-generic-ambiguity"),
                DeclarationHandle.Create(Module + ".generic_projector_one_site_ambiguity"),
                H("Actual collisions arbitrarily close in the one-site fiber"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CritchMorton),
                Blocks(
                    Paragraph(Text("For every ring length at least four, work in the relative Euclidean topology on the closure of the trace-one projectors of actual periodic binary bond-two complex matrix product states. The nonzero locus of the normalized adjacent-pair commutator is nonempty, open and dense there. Each actual point of that locus lies in the relative closure of distinct actual projectors with its single-site observation.")),
                    Paragraph(Text("The commutator is continuous and homogeneous of degree two in the adjacent-pair matrix. Projecting the dense raw amplitude locus preserves nonvanishing and approximates every actual projector, so its image is dense in the compact closure.")),
                    Paragraph(Text("Apply the collective physical rotation to any core that presents the target. Equality of the raw one-site matrices preserves the trace and hence the positive squared amplitude mass. Every point of the curve therefore gives an actual normalized projector with the same single-site density. The raw adjacent-pair matrix differs arbitrarily near the target parameter. The common normalization preserves this difference, which distinguishes the full projectors.")),
                    Paragraph(Text("Critch and Morton give the periodic trace parametrization and formulate the periodic marginal reconstruction problem in Conjecture 10, SIGMA 10 (2014), 095. The declaration here proves the single-site insufficiency bound in the trace-one projector formulation."))),
                DescribeRole.Theorem))));
}
