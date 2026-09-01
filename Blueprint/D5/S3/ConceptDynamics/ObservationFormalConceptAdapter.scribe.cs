using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ObservationFormalConceptAdapterDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S3/ConceptDynamics/ObservationFormalConceptAdapter.extentClosure_singleton_eq_jointKernel_class";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readout-value incidence identifies observational equivalence classes with singleton extent closures in Mathlib formal concept analysis.",
        H("Observation Kernels as Formal-Concept Extents"),
        Blocks(Describe.Lean(
            DescribeId.Create("observation-formal-concept-adapter"),
            DeclarationHandle.Create(Declaration),
            H("A singleton extent closure is the common-kernel class"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An attribute is a pair consisting of one readout in the family and one output value. A state has that attribute exactly when the readout returns that value.")),
                Paragraph(Text(
                    "Closing a singleton under Mathlib's polar Galois connection therefore retains exactly the states agreeing with the original state under every readout.")),
                Paragraph(Text(
                    "The resulting set is equal to the repository joint-kernel equivalence class and hence supplies a direct adapter into the upstream complete concept lattice."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois")),
        ]));
}