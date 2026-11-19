using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointWeightedPauliDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pauli expansion identifies both the actual endpoint map and the unweighted twirl.",
        H("Weighted Pauli conjugations at the Wu endpoint"),
        Blocks(
            Paragraph(Text("With α = (1 + λ)/2 and β = (1 − λ)/2, a product of k distinct conjugating words has weight α^(4−k)β^k. Multiplying the four sign factors on each Pauli word gives the eigenvalue λᵈ, and the Pauli basis determines the linear map.")),
            Paragraph(Text("The weighted sum of all sixteen ordered Pauli conjugations equals the signed two-mode map (`A₁_eq_weighted_pauli`).")),
            Describe.Lean(DescribeId.Create("twirl"), DeclarationHandle.Create(Owner + "endpoint_pauli_twirl"),
                H("Unweighted Pauli twirl"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unweighted sum of the sixteen conjugations sends any two-mode matrix X to 4 tr(X) times the identity."))), DescribeRole.Theorem))));
}
