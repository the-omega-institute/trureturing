using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteSymmetryBoundReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteSymmetryBoundReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel replay of partial bounds and rank-decreasing finite symmetry cuts.",
        H("Finite symmetry bound replay"),
        Blocks(
            Describe.Lean(DescribeId.Create("partial-lower-bound"),
                DeclarationHandle.Create(Prefix + "partial_lower_bound_sound"),
                H("Partial lower bounds are sound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact values on complete events and monotonicity under filling unknown coordinates imply the stored partial lower bound for every compatible event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-bound"),
                DeclarationHandle.Create(Prefix + "checked_global_lower_bound"),
                H("Accepted trees prove a global bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction on an actual natural rank rules out every bad event. A symmetry cut is accepted only with score preservation and strict descent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lex-rank"),
                DeclarationHandle.Create(Prefix + "finite_lex_dominates_rank_lt"),
                H("Concrete lexicographic descent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinate permutations and outcome relabellings use a finite lexicographic order and a cardinality order isomorphism to Nat."))), DescribeRole.Theorem))));
}
