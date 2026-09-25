using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitUpperFamilyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitUpperFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized positive effect matrices and pure-state arcs give a matching upper family.",
        H("Actual pure-qubit upper family"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-effect-family"),
                DeclarationHandle.Create(Module + "actual_effect_family"), H("Normalized positive effect family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any normalized centered direction, the quadratic small roots admit a differentiable normalization branch and a local inverse radius map. Along the same family the actual effects are positive semidefinite and sum to the identity, the strict arc and probability margins hold, and the extended cost has the required moment limit.")))),
            Describe.Lean(DescribeId.Create("actual-upper-family"),
                DeclarationHandle.Create(Module + "actual_upper_family"), H("Matching family of actual programs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive finite probabilities and a centered direction of unit weighted second moment, the radius family gives actual POVMs and pure curves. Their spectral cost excess has the stated moment coefficient. Scaling the direction in the infimum theorem gives the original affine data.")))))));
}
