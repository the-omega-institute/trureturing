using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class LegalGrowthCompactnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/LegalGrowthCompactness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For an arbitrary discrete partial order, the space of injective locally legal infinite " +
        "growth sequences is compact exactly when every finite lower stem has finite enabled frontier.",
        H("Compactness of Legal Infinite Growth"),
        Blocks(
            Paragraph(Text(
                "Let E be a partially ordered set in an arbitrary universe, equipped with a discrete " +
                "topology. The sequence space carries the product topology. A finite lower stem F " +
                "is a finite set closed under the order. An event is enabled at F when it is absent " +
                "from F and every strict predecessor lies in F. This is the same enabled-event " +
                "predicate used by finite enabled executions.")),
            Describe.Lean(
                DescribeId.Create("legal-infinite-growth"),
                DeclarationHandle.Create(Prefix + "Omega"),
                H("The space of locally legal sequences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A sequence belongs to Omega when it is injective and every strict predecessor " +
                    "of its event at position i occurs at a position strictly below i. The sequence " +
                    "need not exhaust E. In particular, this space differs from the space of " +
                    "bijective histories of a countable past-finite order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("legal-growth-compactness"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Compactness and all finite lower frontiers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Omega is compact if and only if every finite lower stem has a finite set " +
                        "of enabled events. All finite lower stems are quantified, including stems " +
                        "with empty frontier. There is no assumption of countability, infinitude, " +
                        "global past finiteness, a total order, finite width, an existing infinite " +
                        "path, or a nonempty Omega. Empty and finite carriers are included.")),
                    Paragraph(Text(
                        "First, Omega is closed. A repeated pair of coordinates violates " +
                        "injectivity on a finite set of coordinates. At position i, failure to " +
                        "include a strict predecessor earlier is also determined by the first " +
                        "i plus one coordinates. More explicitly, for fixed i and x the condition " +
                        "that x is not a strict predecessor of the current event is closed, as is " +
                        "the finite union saying x occurs at one of the earlier coordinates. " +
                        "Intersecting these closed conditions over all i and x, together with " +
                        "the pairwise distinctness conditions, gives precisely Omega.")),
                    Paragraph(Text(
                        "Suppose every finite lower frontier is finite. The stem before position " +
                        "n is the image of the positions below n. Local legality makes it lower, " +
                        "and injectivity and predecessor legality make the next event enabled. " +
                        "Induction on n shows there are finitely many possible stems: initially " +
                        "there is only the empty stem, and each next stem inserts one of finitely " +
                        "many enabled events into one of finitely many preceding stems. The " +
                        "coordinate image at n lies in the finite union of these frontiers. " +
                        "Finite discrete coordinate images are compact, so the closed-subset " +
                        "criterion for products proves compactness of Omega. Empty levels and " +
                        "terminal stems contribute empty sets to these unions.")),
                    Paragraph(Text(
                        "Conversely, suppose a finite lower stem F has infinite frontier A. " +
                        "The finite enabled-execution theorem supplies an extension list of the " +
                        "finite subtype F. Its subtype values form a legal prefix: lower closure " +
                        "keeps every predecessor in F, and the extension order places that " +
                        "predecessor earlier. Choose an injection from the natural numbers into " +
                        "A. For any x in A, exchange x with the first value of that injection " +
                        "inside A. Append the resulting injective sequence to the prefix. Its " +
                        "values are fresh outside F and all their strict predecessors already " +
                        "lie in F, so the concatenation is an actual infinite legal growth " +
                        "sequence with x immediately after the prefix. Thus the coordinate " +
                        "image at the prefix length contains all of A. Compactness would make " +
                        "that discrete coordinate image finite, a contradiction. Infinite " +
                        "continuation is constructed from A rather than assumed.")),
                    Paragraph(Text(
                        "The product compactness and discrete compactness steps use the pinned " +
                        "Mathlib results Pi.isCompact_iff_of_isClosed and isCompact_iff_finite. " +
                        "Finite stem ordering uses EnabledPathSwapConnectivity.result on the " +
                        "finite subtype, retaining its original partial order. The stem membership " +
                        "identity supplies the lower-closure and next-event facts used by the " +
                        "induction; the infinite concatenation supplies the coordinate obstruction " +
                        "in the reverse implication.")),
                    Paragraph(Text(
                        "Brightwell and Luczak, Order-invariant measures on fixed causal sets, " +
                        "arXiv:0901.0242v2, Theorem 3.1 on page 6, state the corresponding " +
                        "compactness criterion for causal sets with their sequence metric. That " +
                        "literature statement has a restricted causal-set setting. The theorem " +
                        "here is proved for arbitrary partial orders and the product of discrete " +
                        "topologies; the cited theorem is mathematical context, not an assumed " +
                        "arbitrary-poset result or a separate claim about originality."))),
                DescribeRole.Theorem))));
}
