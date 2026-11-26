using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingConnectorLawDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef EulerTourCount =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/creedcryan2013eulertours");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact probabilities for a prescribed connection in a compatible labelled cycle.",
        H("Prescribed connectors in compatible cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("alternating-connector-mass"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingConnectorLaw.connector_mass"),
            H("The mass of a specified successor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(EulerTourCount),
            Blocks(
                Paragraph(Text(
                    "Each label of a finite set C has a source color s and a destination color d, "
                    + "both Boolean. A compatible cycle is a single-orbit permutation σ on the "
                    + "nonempty set C with d(z) = s(σ(z)) at each label. Let μ be a probability mass "
                    + "function assigning the reciprocal of the number of compatible cycles to "
                    + "each cycle. Fix distinct labels x and y.")),
                Paragraph(Text(
                    "The event σ(x) = y has probability zero when s(y) differs from d(x). "
                    + "When the colors agree, remove x, assign source color s(x) to y, and keep "
                    + "the destination colors and the other source colors. Write R for the "
                    + "remaining label set, a and b for the counts of its two source colors, "
                    + "m for its number of false-to-true transitions, and p and q for its "
                    + "false-to-false and true-to-true transition counts.")),
                Paragraph(Text(
                    "The event probability is M divided by the original compatible-cycle count. "
                    + "If m is positive then M equals m(a−1)!(b−1)!. If m is zero and p or q is "
                    + "zero then M equals (|R|−1)!. If m is zero and both p and q are positive "
                    + "then M is zero. The theorem expresses the event probability as outer "
                    + "measure on the finite carrier.")),
                Paragraph(Text(
                    "Removing x from a cycle with the specified successor redirects the incoming "
                    + "edge of x to y. Inserting x immediately before y reverses this operation. "
                    + "Color compatibility at the redirected edge is exactly the source-color "
                    + "update above. The transition-color counts stay balanced and the existing "
                    + "compatible-cycle inventory theorem supplies M. For an alternating "
                    + "directed forest, s is the color of a component's head and d is the "
                    + "opposite of the color of its tail."))),
            DescribeRole.Theorem))));
}
