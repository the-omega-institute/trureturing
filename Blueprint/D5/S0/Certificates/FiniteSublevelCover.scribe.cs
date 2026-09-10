using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSublevelCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of locally proved cover steps controls an arbitrary candidate space, including continuous phase spaces.",
        H("Finite Proof-Carrying Sublevel Covers"),
        Blocks(Describe.Lean(
            DescribeId.Create("sublevel-covered-by-locally-proved-finite-steps"),
            DeclarationHandle.Create("D5/S0/Certificates/FiniteSublevelCover.sublevel_mem_target_of_local_steps"),
            H("Strictly ordered local proofs imply the complete sublevel cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The LocalStep proof type records target inclusion, scalar residual exclusion, conserved residual-box exclusion, complete binary splitting and sublevel-preserving contraction. "
                    + "Every local premise is an actual proposition with a proof. Child indices must be strictly earlier. Strong induction then retains every candidate in the closed residual band until it reaches the target.")),
                Paragraph(Text(
                    "Only the proof nodes are finite. The candidate type may be uncountable, and the theorem does not replace it with observed roots or tube labels. "
                    + "Closed split boundaries are included; a contraction must preserve all sublevel points, not only exact zeros. Empty or overlapping target tubes and shared subtrees are permitted.")),
                Paragraph(Text(
                    "This is a logical assembly theorem. It is not a parser, an interval evaluator, or a proof that a concrete external trace satisfies LocalStep. "
                    + "The interval soundness, chart changes, actual seed identities and all local proof terms remain necessary for a concrete kernel-certified exclusion."))),
            DescribeRole.Theorem))));
}
