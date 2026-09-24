using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CircularTwoChoiceParkingOperationalDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/CircularTwoChoiceParkingOperational.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/recioui2026circular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal circular two-choice parking process, its vacancy and rotation laws, "
            + "and explicit fixed-increment normalization and cutting operations.",
        H("The Operational Circular Two-Choice Parking Construction"),
        Blocks(
            Node("circular-spots", "Circular spots", "Spot",
                "For n cars, the parking circle is ZMod(n+1). Addition is clockwise "
                    + "translation, so every scan and rotation is performed on exactly n+1 spots."),
            Node("positive-increments", "Positive clockwise increments", "Increment",
                "An increment is a natural number k with hypotheses 1 <= k and k <= n. "
                    + "These inequalities make the second choice distinct from the anchor and "
                    + "cover every admissible second choice when n is positive."),
            Node("ordered-actual-choice", "Literal ordered choices", "ActualChoice",
                "Each car carries an anchor, a second spot, and evidence that the two spots are "
                    + "distinct. The field order is operational: the anchor is tried first and "
                    + "the second spot starts the fallback scan."),
            Node("actual-preferences", "Actual preferences", "ActualPreferences",
                "An actual preference assigns one ordered ActualChoice to every car in Fin n. "
                    + "Nothing is quotiented by rotation or by the increment encoding."),
            Node("one-choice-anchors", "One-choice anchors", "Anchors",
                "The comparison input assigns one circular anchor to each of the n cars."),
            Node("increment-matrices", "Per-car increment matrices", "IncrementMatrix",
                "An increment matrix retains one positive clockwise increment for every car. "
                    + "It is the fixed parameter of the source-level anchor classes."),
            Node("literal-actual-step", "Anchor priority and second-origin scanning", "actualStep",
                "Given the occupied list and an ordered choice q, the step returns q.anchor when "
                    + "that spot is free. Only when the anchor is occupied does it inspect offsets "
                    + "0 through n clockwise from q.second; offset zero therefore selects a free "
                    + "second choice before any later spot."),
            Node("one-choice-step", "The comparison scanner", "oneStep",
                "The one-choice process uses the same bounded circular scanner, beginning at its "
                    + "single anchor with offset zero."),
            Node("generic-parking-recursion", "Parking from an occupied state", "parkFrom",
                "For an arbitrary step function, cars are processed in list order. Each selected "
                    + "spot is prepended to the occupied state before the remaining cars run, while "
                    + "the returned list stays in car order."),
            Node("actual-landings", "Actual landing spots", "actualSpots",
                "The literal ordered choices are listed in car order and run from an empty occupied "
                    + "state using actualStep."),
            Node("one-choice-landings", "One-choice landing spots", "oneSpots",
                "The anchor vector is listed in car order and run from an empty occupied state using "
                    + "the comparison step."),
            Theorem("actual-prefix-freshness", "Every actual prefix is fresh", "actual_prefix_fresh",
                "For any list of actual choices with length at most n, the landing list has exactly "
                    + "the same length and has no duplicate spot. The proof first shows that the "
                    + "finite offset set contains a free position, characterizes its minimum, and "
                    + "then carries freshness through the recursive occupied state."),
            Node("actual-empty-spot", "The actual vacancy", "actualEmpty",
                "After all n actual choices run, the vacancy is the first circular spot absent from "
                    + "the landing list, scanning from zero."),
            Node("one-choice-empty-spot", "The comparison vacancy", "oneEmpty",
                "The one-choice vacancy uses the identical complement selector on the one-choice "
                    + "landing list."),
            Theorem("actual-unique-vacancy", "The actual vacancy is unique", "actual_unique_vacancy",
                "For every spot x, x is absent from the n actual landings if and only if x equals "
                    + "actualEmpty. Prefix freshness gives n distinct elements of a type with n+1 "
                    + "elements; adjoining two different missing spots would exceed that cardinality."),
            Theorem("one-choice-unique-vacancy", "The comparison vacancy is unique",
                "one_unique_vacancy",
                "For every spot x, x is absent from the one-choice landings if and only if x equals "
                    + "oneEmpty. The proof uses the same finite-complement argument as the literal run."),
            Node("rotate-one-choice-pair", "Rotate an ordered choice", "rotateChoice",
                "A common circular displacement is added to both the anchor and the second choice. "
                    + "Translation preserves their inequality."),
            Node("rotate-all-actual-choices", "Rotate an actual preference", "rotateActual",
                "The same displacement is applied pointwise to every car's ordered choice."),
            Node("rotate-all-anchors", "Rotate a one-choice preference", "rotateAnchors",
                "The same displacement is applied pointwise to every one-choice anchor."),
            Theorem("actual-landings-rotate", "Actual landings commute with rotation",
                "actualSpots_rotate",
                "Rotating all ordered choices rotates the complete landing list by the same amount. "
                    + "The proof transports membership through translated occupied lists, proves "
                    + "that the minimum free offset is unchanged, and inducts through parkFrom."),
            Theorem("actual-vacancy-rotates", "The actual vacancy commutes with rotation",
                "actualEmpty_rotate",
                "The vacancy of the rotated actual input is the original vacancy plus the common "
                    + "displacement. Uniqueness identifies it from the rotated landing complement."),
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
                    + "cancel on every anchor."),
            Node("cut-a-circular-spot", "Cut the circle at a vacancy", "cutSpot",
                "The linear coordinate of x relative to vacancy j is the canonical natural value of "
                    + "x-j, ranging from zero through n."),
            Node("uncut-a-linear-spot", "Restore a cut coordinate", "uncutSpot",
                "A natural linear coordinate p is placed back on the circle as j+p."),
            Theorem("scanner-cut-comparison", "Cutting identifies the two scanners", "firstFree_cut",
                "Assume the occupied list has no duplicates, its length is at most n, j is unoccupied, "
                    + "and the circular scanner does not land at j. Cutting at j sends the circular "
                    + "first-free result to the supplier's linear parkStep. The proof rotates j to zero, "
                    + "orders every skipped offset before the cut, and applies the supplier's vacancy "
                    + "and skipped-position specification."),
            Theorem("scanner-avoids-vacancy", "The reverse scanner does not cross the vacancy",
                "firstFree_ne_vacancy",
                "Let 1 <= p <= q <= n and suppose uncutSpot j q is free. The first circular free spot "
                    + "from uncutSpot j p cannot be j: the free offset q-p occurs strictly before the "
                    + "offset n+1-p that returns to the cut."),
            Theorem("forward-cut-simulation", "Cutting simulates the complete one-choice run", "cut_run",
                "Assume a duplicate-free occupied state, enough remaining capacity, an unoccupied cut j, "
                    + "and a future one-choice run that never lands at j. Then supplier parkFrom on the "
                    + "cut occupied list and cut anchors equals the cut circular landing list. The same "
                    + "induction also proves that every input anchor differs from j.")),
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

    private static DocumentBlock Theorem(
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
            DescribeRole.Theorem);
}
