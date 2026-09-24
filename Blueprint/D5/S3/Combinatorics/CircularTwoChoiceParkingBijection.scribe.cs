using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CircularTwoChoiceParkingBijectionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/CircularTwoChoiceParkingBijection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/recioui2026circular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting the literal circular process at its observed vacancy gives an explicit "
            + "fixed-fiber equivalence with classical parking functions, while a separate "
            + "global equivalence retains all original observables.",
        H("Circular Two-Choice Parking and Classical Parking Functions"),
        Blocks(
            Node("classical-parking-functions", "Classical parking functions", "ClassicalPF",
                "ClassicalPF n is the subtype of natural-number lists with length n satisfying "
                    + "the frozen supplier's literal IsParkingFunction predicate. Preferences and "
                    + "their final spots therefore both lie in the linear street 1 through n."),
            Node("one-choice-classical-equivalence", "Cut and uncut are inverse",
                "oneChoiceClassicalEquiv",
                "For every natural n and every circular vacancy j, this construction is an explicit "
                    + "equivalence between OneChoiceFiber n j and ClassicalPF n. Forward, each anchor "
                    + "is cut relative to j. The cut_run theorem identifies the complete circular run "
                    + "with the supplier's parkFrom, proving the parking predicate. Reverse, every "
                    + "classical preference is uncut by adding j. The reverse feedback-state induction "
                    + "uses parkStep_spec and firstFree_ne_vacancy to show that its circular run is the "
                    + "uncut classical run and leaves j empty. Pointwise cut-after-uncut and "
                    + "uncut-after-cut identities prove both inverse laws."),
            Node("fixed-fiber-classical-equivalence", "The fixed-increment fixed-vacancy equivalence",
                "fixedFiberEquiv",
                "For every natural n, every per-car increment matrix, and every vacancy j, this is the "
                    + "composition of fixedFiberOneChoiceEquiv with oneChoiceClassicalEquiv. Its forward "
                    + "map performs orbit normalization and then cuts at j. Its inverse uncuts a "
                    + "classical parking function, reverses the normalization, and reconstructs each "
                    + "literal ordered pair. Both equivalence laws are inherited from those explicit "
                    + "two-sided constructions. For the source's range n >= 1, this is the canonical "
                    + "bijection requested for every fixed increment class and prescribed vacancy."),
            Node("global-observable-equivalence", "The auxiliary global observable equivalence",
                "globalParkingEquiv",
                "For n with hypothesis 1 <= n, every literal actual preference is equivalent to a "
                    + "classical parking function together with its original increment matrix and its "
                    + "actual vacancy. The forward map definitionally projects actualIncrements and "
                    + "actualEmpty. The inverse enters that exact fixed fiber and applies "
                    + "fixedFiberEquiv, so its round trip reconstructs each car's anchor and second "
                    + "choice, not only the encoded increment. Mathlib's sigma-fiber and product "
                    + "equivalences assemble the fibers; they do not replace the orbit and cut/uncut "
                    + "construction. This global interface is auxiliary and is not a second ownership "
                    + "claim for the source problem.")),
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
