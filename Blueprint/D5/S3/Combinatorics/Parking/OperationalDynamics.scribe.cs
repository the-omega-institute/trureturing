using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class OperationalDynamicsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Parking/OperationalDynamics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/recioui2026circular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal ordered circular process, its bounded scanner, unique vacancy, and rotation laws.",
        H("Operational Dynamics of Circular Two-Choice Parking"),
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
            Node("orbit-enumeration", "Circular offset enumeration", "orbitEquiv",
                "For each starting spot, offsets in Fin(n+1) are identified bijectively with all "
                    + "circular spots in clockwise order."),
            Node("free-offsets", "Available offsets", "freeOffsets",
                "The available-offset finset retains exactly those bounded offsets whose circular "
                    + "images are absent from the occupied finset."),
            Node("first-free-offset", "Least available offset", "firstFreeOffset",
                "The scanner selects the minimum available offset, with zero used only in the "
                    + "unreachable empty-set branch later excluded by the capacity theorem."),
            Node("first-free-scanner", "Bounded first-free scanner", "firstFree",
                "The sole scanner inspects offsets zero through n from its start and returns the "
                    + "spot at the least free offset."),
            Theorem("free-start-is-selected", "A free start is selected at offset zero",
                "firstFree_of_not_mem",
                "When the scan origin is absent from the occupied list, offset zero is available "
                    + "and minimal, so the bounded scanner returns that origin exactly."),
            Theorem("first-free-fresh", "The selected spot is fresh", "firstFree_fresh",
                "For a duplicate-free occupied list of length at most n, the bounded scan returns "
                    + "a spot not already occupied."),
            Theorem("first-free-skipped", "Earlier offsets are occupied", "firstFree_skipped",
                "Every offset strictly below the selected first-free offset maps to a spot already "
                    + "present in the occupied list."),
            Node("rotate-occupied-list", "Rotate an occupied state", "rotateList",
                "A common circular displacement is added to every occupied spot while preserving "
                    + "the list order used by the operational recursion."),
            Theorem("rotated-membership", "Rotation preserves occupied membership",
                "mem_rotateList_iff",
                "A translated spot belongs to the translated occupied list exactly when its "
                    + "untranslated spot belongs to the original list."),
            Theorem("first-free-rotates", "The scanner commutes with rotation", "firstFree_rotate",
                "Translating the occupied state and scan origin leaves the chosen offset unchanged "
                    + "and translates the selected spot by the same displacement."),
            Theorem("one-choice-vacancy-rotates",
                "The comparison vacancy commutes with rotation", "oneEmpty_rotate",
                "The unique empty spot of a translated one-choice run is the original comparison "
                    + "vacancy plus the common displacement.")),
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
