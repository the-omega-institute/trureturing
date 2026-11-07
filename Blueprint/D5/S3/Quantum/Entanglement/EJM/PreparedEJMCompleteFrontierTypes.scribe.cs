using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierTypesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierTypes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cut metadata and context-specific semantic responses",
        H("Original cut metadata and context-specific semantic responses"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank.")),
            Node("subtree-contexts", "subtreeContexts", "Count occurrences with fuel and all four split edges",
                "Fuel zero contributes zero. A bound or symmetry node at positive fuel contributes one; a split contributes one plus the recursive counts of children 0, 1, 2 and 3 with one less fuel. Repeated child indices are counted at each occurrence.", DescribeRole.Definition),
            Node("metadata", "metadata", "Check every numerical cut field against the original decoder",
                "A row must have an in-range node index, reserved field zero, depth at most twenty, code below four to its depth, kind below three equal to the original word modulo four, and domain four to twenty minus depth. Its positive subtree count must be at most 4096 and equal the fuel-indexed original occurrence count.", DescribeRole.Definition),
            Node("canonical-response", "CanonicalResponse", "Strict rank descent for a bad event at one prefix",
                "For every assignment compatible with the stated prefix whose original F1/F2 score is below scale, the response requires an assignment still below scale with strictly smaller finite lexicographic rank. The proposition uses the row depth and code and the unchanged F1/F2 score and scale.", DescribeRole.Definition),
            Node("response-of-raw", "response_of_raw", "Derive a response from exact original suffix acceptance",
                "For an in-range original index and depth at most twenty, Accepted at the row depth, code and index gives CanonicalResponse through accepted_suffix_bad_event_response. The acceptance premise includes the full original cache and partial assignment.", DescribeRole.Theorem),
            Node("response-of-semantic", "response_of_semantic", "Derive a response by excluding bad events at that prefix",
                "A score lower bound at scale for every event compatible with the row prefix implies CanonicalResponse: any compatible event below scale contradicts that bound.", DescribeRole.Theorem),
            Node("responses", "Responses", "Require a response at every table leaf",
                "The empty tree requires True, a leaf requires CanonicalResponse for its complete row, and a branch requires the conjunction of both subtree response propositions.", DescribeRole.Definition),
            Node("lookup-response", "lookup_response", "Select a response along the actual lookup path",
                "For any CutTable with Responses, every successful lookup by depth and code yields the corresponding CanonicalResponse. Tree induction follows the same lexicographic pivot comparison as lookup and extracts the response at the matching leaf.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
