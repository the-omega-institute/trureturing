using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class ForwardPathPosteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The graph posterior after a nonbacktracking path disclosure.",
        H("Conditioning on the edges of a disclosed path"),
        Blocks(
            Definition("path-schedule", "Schedule", "Schedule of requested slots",
                "A schedule is a list of pairs containing a position and a Boolean slot."),
            Definition("path-entry", "Entry", "A row of the disclosure",
                "A row stores the requested position and slot, the state before the step, "
                + "and the disclosed vertex."),
            Definition("path-run", "run", "Replay of the scheduled observations",
                "At each requested slot, apply the order at its position to the slot, "
                + "read the corresponding candidate at the current state, record the row, "
                + "and update the state for the remaining schedule. An empty schedule "
                + "produces no rows."),
            Describe.Lean(
                DescribeId.Create("graph-path-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior.graph_path_posterior"),
                H("The path posterior is the prior conditioned on its recorded edges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Draw a graph world from a probability mass function and independently "
                        + "draw a uniform binary order at each position in a finite set. "
                        + "Start with the same incoming edge in every world. Follow a fixed "
                        + "schedule of positions and slots, shifting the incoming pair after "
                        + "each step. Each world, position and incoming pair specifies two "
                        + "distinct candidate vertices.")),
                    Paragraph(Text(
                        "Fix the rows of a reference disclosure. The rows never backtrack, "
                        + "each visited position has one common incoming pair, and the partial "
                        + "slot table records precisely the values of the rows. The set of "
                        + "observed positions contains exactly those with at least one recorded "
                        + "slot. In every world containing a row's incoming edge, require "
                        + "that its observed vertex "
                        + "is a candidate exactly when it is a neighbor other than the predecessor.")),
                    Paragraph(Text(
                        "For a disclosure of positive mass, the posterior probability of any "
                        + "set of worlds equals its prior probability conditional on all "
                        + "recorded edges being present. Replaying the fixed schedule reduces "
                        + "transcript equality to matching the observed slots. Induction along "
                        + "the path shows that compatibility is equivalent to the recorded-edge "
                        + "constraints, because each recorded edge supplies the incoming edge "
                        + "at the next step. The likelihood of the compatible slot table then "
                        + "cancels from numerator and denominator."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/ForwardPathPosterior." + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
