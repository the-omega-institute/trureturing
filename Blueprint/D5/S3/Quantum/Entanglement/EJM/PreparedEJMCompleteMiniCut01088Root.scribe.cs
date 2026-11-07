using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class PreparedEJMCompleteMiniCut01088RootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteMiniCut01088Root.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic score bound at depth thirteen and code 17540",
        H("Semantic score bound at depth thirteen and code 17540"),
        Blocks(
            Paragraph(Text("The statement concerns all original twenty-coordinate, four-valued events compatible with prefixPartial 13 17540. It retains the original F1/F2 score and scale. Thirty-two local factor bounds are collected into eighteen normalized groups on this same event.")),
            Paragraph(Text("Fifteen min-plus eliminations each retain an exact permutation of consumed and untouched factors and the appropriate scaled bucket inequality. Their ValidProgram proof composes these steps, while the terminal certificate bounds the remaining one-variable table. The actual-prefix theorem feeds response_of_semantic for this cut.")),
            Node("context", "Context", "Events compatible with the complete actual prefix",
                "Context is the subtype of assignments compatible with prefixPartial 13 17540. All factor functions and elimination states are evaluated on the same member of this subtype.", DescribeRole.Definition),
            Node("lift", "lift", "Scale a function on the same context",
                "The lift multiplies an integer event function by 6987435 on the underlying compatible assignment. Each scaled bucket inequality uses nonnegativity of this multiplier.", DescribeRole.Definition),
            Node("factor", "factor", "Select the exact group and residual factors",
                "Indices 0 through 17 select the eighteen scaled normalized group functions; indices 18 through 32 select the fifteen scaled residual functions. All other indices select zero.", DescribeRole.Definition),
            Node("initial", "initial", "Initial sum of all normalized groups",
                "The initial State stores its literal scaled offset and the complete list of factors 0 through 17. The private initial_lower proof identifies this value with the sum of all group lower bounds and uses the equality of component scores with the original F1/F2 score.", DescribeRole.Definition),
            Node("operations", "operations", "The full fifteen-step elimination program",
                "The list contains operation0 through operation14 in order. Each operation records consumed factors, untouched factors, its signed scaled offset and replacement residual; private step-validity proofs retain both the list permutation and pointwise inequality.", DescribeRole.Definition),
            Node("actual-prefix-score-lower-bound", "actual_prefix_score_lower_bound", "The original score bound at this exact prefix",
                "For every event compatible with prefixPartial 13 17540, scale is at most the original score F1 F2. The proof applies FiniteMinPlusElimination.program_lower_bound to initial_lower, the complete valid_program and the terminal certificate, at that same event and compatibility proof.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
