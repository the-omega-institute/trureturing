using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class FixedIncrementFiberTransportDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/recioui2026circular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-increment encoding and explicit vacancy-normalized transport between actual and one-choice fibers.",
        H("Fixed-Increment Fiber Transport"),
        Blocks(
            Node("read-an-increment", "Read the positive clockwise increment", "actualIncrement",
                "The increment is the canonical value of second minus anchor in ZMod(n+1). Distinctness "
                    + "rules out zero, and the canonical value bound gives the upper bound n."),
            Node("rebuild-an-ordered-choice", "Rebuild an ordered choice", "choiceOfAnchorIncrement",
                "Given an anchor and k in 1 through n, the second choice is anchor+k. The strict "
                    + "canonical-value bound proves that this spot cannot equal the anchor."),
            Node("read-all-increments", "Read every car's increment", "actualIncrements",
                "The increment decoder is applied pointwise, retaining the original per-car order."),
            Node("fixed-actual-fiber", "Fixed increments and fixed actual vacancy", "FixedActualFiber",
                "This subtype contains exactly the literal actual preferences whose decoded increment "
                    + "matrix equals the supplied matrix and whose actual vacancy equals the supplied "
                    + "spot."),
            Node("one-choice-fiber", "Fixed one-choice vacancy", "OneChoiceFiber",
                "This subtype contains exactly the one-choice anchor vectors whose vacancy is the "
                    + "supplied spot."),
            Node("actual-to-one-choice-normalization", "Normalize an actual fiber",
                "fixedFiberToOneChoice",
                "The map forgets neither a car nor its position. It extracts all anchors and rotates "
                    + "them by target vacancy minus their one-choice vacancy. The rotation law proves "
                    + "that the normalized anchor vector lies in OneChoiceFiber n j."),
            Node("one-choice-to-actual-normalization", "Reconstruct the literal fixed fiber",
                "oneChoiceToFixedFiber",
                "The inverse first rotates the anchors so that rebuilding with the fixed increment "
                    + "matrix has vacancy j, then rebuilds every ordered pair. The increment proof is "
                    + "pointwise, and actual vacancy equivariance proves membership in the target fiber."),
            Node("fixed-fiber-orbit-equivalence", "The fixed-fiber orbit equivalence",
                "fixedFiberOneChoiceEquiv",
                "The forward and reverse normalizations form an explicit equivalence. For the left "
                    + "inverse, subtraction recovers the increment of each original pair and rebuilding "
                    + "recovers both its anchor and second choice; the two compensating rotations cancel. "
                    + "For the right inverse, the vacancy equation makes the corresponding rotations "
                    + "cancel on every anchor.")),
        []));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

}
