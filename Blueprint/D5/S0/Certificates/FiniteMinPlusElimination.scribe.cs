using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteMinPlusEliminationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteMinPlusElimination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite bucket relaxations preserve the original score bound",
        H("Finite bucket relaxations preserve the original score bound"),
        Blocks(
            Paragraph(Text("Every factor is evaluated on the same complete assignment. A concrete finite table receipt over remaining axes and every eliminated value must be connected to this pointwise value. The assignment type is arbitrary; for an original EJM prefix it retains all twenty coordinates, all four values and exact prefix compatibility. Scope ordering, axis insertion and table indexing remain concrete proof obligations.")),
            Node("factor", "Factor", "Lift factors to complete assignments",
                "A factor is an integer-valued function on the assignment type. For one exact prefix, that type may contain full original events together with a proof of compatibility; every event in that context is retained.", DescribeRole.Definition),
            Node("state", "State", "Retain the constant and every active occurrence",
                "A state stores an integer constant and a finite list of active factors. Repeated occurrences remain repeated list entries.", DescribeRole.Definition),
            Node("state-value", "State.value", "Evaluate the represented bound",
                "The state value on an assignment is its accumulated constant plus the sum of every active factor value.", DescribeRole.Definition),
            Node("elimination", "Elimination", "Propose a literal bucket replacement",
                "An operation supplies its old bucket, untouched rest, integer offset and output function. The rest may still depend on the same axis; full elimination and mini-bucket relaxations share this interface. An empty kept-axis set uses a constant output.", DescribeRole.Definition),
            Node("next", "next", "Execute the offset and factor update",
                "Add the offset exactly once, discard the proposed bucket and prepend its output to the proposed rest. This computes the next state; its correctness is separately proved from ValidStep.", DescribeRole.Definition),
            Node("valid-step", "ValidStep", "Prove a partition and every pointwise inequality",
                "The active factor list must be a permutation of bucket followed by rest. For every complete assignment, offset plus output must be at most the sum of the old bucket. No claimed native minimum, optimum, success flag or all-incident-axis condition substitutes for these proofs.", DescribeRole.Definition),
            Node("run", "run", "Compute the full finite program",
                "Operations execute in order, each using the state computed by the preceding operation.", DescribeRole.Definition),
            Node("valid-program", "ValidProgram", "Validate the actual intermediate states",
                "The empty program is valid. A nonempty program requires its head operation to be valid on the current state and its tail to be valid on the computed next state.", DescribeRole.Definition),
            Node("terminal", "Terminal", "Match a lower minimum to every remaining factor",
                "List.Forall₂ pairs each terminal minimum with one remaining factor occurrence and proves that minimum below its value on every assignment. The requested gap must be at most the accumulated constant plus the sum of those minima. Length and occurrence coverage cannot be omitted.", DescribeRole.Definition),
            Node("valid-step-le", "valid_step_le", "One valid replacement decreases the represented function",
                "Permutation preserves the original sum, the bucket receipt bounds the replacement, and the rest and constant are retained algebraically. Negative offsets and arbitrary complete assignments are covered.", DescribeRole.Theorem),
            Node("valid-program-le", "valid_program_le", "Compose the actual finite state transitions",
                "Induction on the defined program applies one-step soundness at every actual intermediate state. The final represented value is at most the initial represented value on every original assignment.", DescribeRole.Theorem),
            Node("program-lower-bound", "program_lower_bound", "Transport terminal receipts to the original score",
                "Mathlib's finite list sum inequality combines all paired terminal minima. Their threshold is then transported through the valid program to the original initial score bound. Complete initial factor coverage and original local validity must be proved by the application.", DescribeRole.Theorem),
            Paragraph(Text("The original EJM depth13/code4/index674 consumer reconstructs its initial bound from the original 32 factors grouped into eighteen normalized tables, proposes six literal bucket operations and pairs the final factor with a proved terminal lower minimum. Its proof obligations retain F1/F2, scale 6987435 and every assignment compatible with the exact prefix. This construction requires kernel checking of every original group bound, normalization, bucket receipt, occurrence partition and terminal minimum before first freeze. It supplies no raw replay acceptance or complete EJM frontier coverage. Source-owned Reg audits and current bindings for the three public theorems remain unfinished under https://github.com/the-omega-institute/trureturing/issues/16309.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
