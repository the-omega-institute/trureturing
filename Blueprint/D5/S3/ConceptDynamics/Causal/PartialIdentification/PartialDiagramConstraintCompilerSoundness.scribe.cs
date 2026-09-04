using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class PartialDiagramConstraintCompilerSoundnessDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
        + "PartialDiagramConstraintCompilerSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Required edges, forbidden edges, and query-order admissibility compile to an exact finite support polytope over candidate causal completions.",
        H("Partial-Diagram Constraint Compiler Soundness"),
        Blocks(
            Paragraph(Text(
                "A finite completion supplies a directed-edge table and a query-order compatibility judgment. The compiler introduces simplex rows and one zero-support row for every witnessed edge or order violation.")),
            Paragraph(Text(
                "The generated linear system is exact. Its feasible vectors are precisely normalized nonnegative masses supported on completions compatible with the partial diagram and the query-implied causal order.")),
            Paragraph(Text(
                "This support polytope has latent-completion mixture semantics. When one complete graph is a single global unknown object, completion-specific identified ranges must instead be combined by the completion-union construction.")),
            Describe.Lean(
                DescribeId.Create("feasible-iff-compatible-completion-mixture"),
                DeclarationHandle.Create(
                    Prefix + "feasible_iff_compatible_completion_mixture"),
                H("The compiled LP exactly characterizes admissible completion mixtures"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nonnegativity and two normalization rows produce a probability law. Active violation rows force every inadmissible completion coordinate to zero. Conversely, an admissibly supported probability law satisfies every generated row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("point-mass-feasible-iff-admissible"),
                DeclarationHandle.Create(
                    Prefix + "pointMass_feasible_iff_admissible"),
                H("A deterministic completion witness is feasible exactly when it is admissible"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unit mass concentrated on one completion passes the compiler exactly when that completion satisfies every required edge, every forbidden-edge exclusion, and the query-order condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-problem-nonempty-iff-exists-admissible"),
                DeclarationHandle.Create(
                    Prefix + "compiled_problem_nonempty_iff_exists_admissible"),
                H("The support polytope is inhabited exactly when an admissible completion exists"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A normalized feasible mass has at least one nonzero support coordinate, which supplies an admissible completion. The reverse implication uses its point mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-antitone-under-refinement"),
                DeclarationHandle.Create(
                    Prefix + "feasible_antitone_under_refinement"),
                H("Adding partial-graph information shrinks the compiled feasible set"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every completion supporting a stronger diagram also supports the weaker diagram. The same normalized mass therefore remains feasible after forgetting graph assertions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound-survives-refinement"),
                DeclarationHandle.Create(
                    Prefix + "lower_bound_survives_refinement"),
                H("A weaker-diagram lower certificate remains valid after refinement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Feasible-set inclusion transports any replayable rational lower certificate from a weaker partial diagram to every stronger one with the same completion semantics and query."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-bound-survives-refinement"),
                DeclarationHandle.Create(
                    Prefix + "upper_bound_survives_refinement"),
                H("A weaker-diagram upper certificate remains valid after refinement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dual monotonicity statement holds at the upper endpoint. Additional graph assertions cannot invalidate a universal upper bound proved on the larger feasible family."))),
                DescribeRole.Theorem))));
}
