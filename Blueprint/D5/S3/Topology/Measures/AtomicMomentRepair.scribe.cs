using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class AtomicMomentRepairDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Topology/Measures/AtomicMomentRepair";
    private const string Digest =
        "Replace the zero cutoff while preserving five signed moments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Exact moment repair with admissible atoms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-moment-repair"),
                DeclarationHandle.Create(Module + ".exists_exact_moment_repair"),
                H("Exact moment matching at arbitrarily small correction cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the five-coordinate moment function be continuous from "
                        + "the right at zero. Fix five positive cutoff nodes in (0,1] whose "
                        + "moment columns form a basis. For any real weight on the zero cutoff "
                        + "and any strictly positive correction budget, a positive cutoff with "
                        + "the original weight and corrections on the five basis nodes have "
                        + "the same weighted moment as the zero cutoff. The sum of the absolute "
                        + "correction weights is strictly below the budget.")),
                    Paragraph(Text("The reusable OmegaMath proof applies to a singleton family. "
                        + "Right continuity puts the zero-cutoff moment in the closure of the "
                        + "positive-cutoff moments. The proof takes the residual of a nearby "
                        + "admissible replacement in fixed basis coordinates and chooses the "
                        + "replacement where the sum of their absolute values is small.")),
                    Paragraph(Text("For the total-variation application, assume a feasible finite "
                        + "atomic measure attains the closed-interval lower bound. Collect equal "
                        + "nodes and apply the theorem to the zero-cutoff atom if it occurs. "
                        + "Keep the remaining positive-cutoff atoms and weights. The repaired "
                        + "measure is feasible in the positive domain. Domain inclusion gives "
                        + "the closed minimum as a lower bound on its total variation. The triangle "
                        + "inequality bounds it above by the closed minimum plus the sum of the "
                        + "absolute correction weights. The correction budget is arbitrary, "
                        + "so the two infima agree."))),
                DescribeRole.Theorem))));
}
