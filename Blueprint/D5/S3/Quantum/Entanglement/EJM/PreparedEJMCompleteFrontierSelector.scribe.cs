using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteFrontierSelectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierSelector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Select a cut using original fuel, index and complete valid prefix",
        H("Select a cut using original fuel, index and complete valid prefix"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The frontier Boolean ignores its cache argument, while its semantic use retains the actual cache and Valid hypothesis. Selection requires the fuel window, prefix decoding, table lookup, exact depth/code/index matches and all metadata checks.")),
            Node("selected", "selected", "Look up and check the whole original cut row",
                "Only positive fuel at most twenty-one is eligible. Read the partial prefix at depth twenty-one minus fuel, look up that depth and code, then require matching row depth, code and original node index together with metadata true. Any failed branch returns none.", DescribeRole.Definition),
            Node("frontier", "frontier", "Mark precisely the successful selections",
                "For the given fuel, original index and partial assignment, the Boolean is selected.isSome. The cache argument is unused in this definition; validity remains a hypothesis of frontier_responses.", DescribeRole.Definition),
            Node("selected-spec", "selected_spec", "Recover exact partial equality and table membership",
                "Given Valid for the actual fuel, cache and partial assignment and a selected row, the entire partial assignment equals the canonical prefix at the row depth and code, and cutTable.lookup at those fields returns that row. Prefix-reader soundness requires validity of that same context.", DescribeRole.Theorem),
            Node("frontier-responses", "frontier_responses", "Use the selected response in the same valid context",
                "Assume cutTable.Responses, Valid for the actual context, a true frontier Boolean, a compatible event and score below scale. Selection recovers full partial equality and table membership; lookup_response then gives another below-scale event of strictly smaller rank.", DescribeRole.Theorem),
            Node("checked-of-selected", "checked_of_selected", "A positive-fuel selected node passes the adaptive frontier branch",
                "For any cache and partial assignment, positive fuel and a successful selected row imply adaptive checker acceptance at those exact inputs. The proof uses the marked frontier branch of the checker; semantic response evidence is supplied separately by frontier_responses.", DescribeRole.Theorem),
            Node("accepted-of-selected", "accepted_of_selected", "Specialize selected acceptance to the canonical prefix",
                "At depth at most twenty, a successful selection at fuel twenty-one minus depth, original index and prefixPartial implies adaptive Accepted for that exact depth/code/index, using the whole prefixCache.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
