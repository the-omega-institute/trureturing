using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreAnalyticSeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticSeparation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quartic separation of actual hard-core paths",
        H("Quartic separation of actual hard-core paths"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticseparation-forbidden-expansion-of-matched-taylor"),
                DeclarationHandle.Create(Module + ".forbidden_expansion_of_matched_taylor"),
                H("The quartic survives passage to analytic paths"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each ring length n ≥ 7, assume the opposite-slope path matches the regular readouts and coherence exactly and has the stated cubic approximation by a polynomial chart path plus a cubic multiple of the null direction. The difference of the normalized 11,11 populations then has leading term quartic(n) times the fourth power of the path parameter. The transfer uses the vanishing first derivative and the null-line behavior of the forbidden corner to account for the cubic correction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticseparation-exists-generic-actual-reconstruction-of-matched-taylor"),
                DeclarationHandle.Create(Module + ".exists_generic_actual_reconstruction_of_matched_taylor"),
                H("Matched Taylor data imply actual reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The parity Taylor data and exact matching give separated pairs arbitrarily close to the witness because quartic(n) is nonzero. The analytic chart theorem then gives generic targets in an actual-projector neighborhood, with every actual projector of the same length admitted as a competitor."))),
                DescribeRole.Theorem))));
}
