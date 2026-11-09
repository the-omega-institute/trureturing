using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class QuaternionDihedralCounterexamplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/manikandishzhang2026sumcodes");

    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quaternion, dihedral and proper-product missing-case examples.",
        H("Three counterexamples to singleton-only total-code necessity"),
        Blocks(
            Item("quaternion-central-involution", "q8Central", "Minus one in Q8",
                "The actual QuaternionGroup 2 central involution a squared is -1, "
                + "in the group presentation a to the fourth equals 1 and x squared "
                + "equals a squared.", DescribeRole.Definition),
            Item("dihedral-central-involution", "d8Central", "The half-turn in D8",
                "The rotation by two in DihedralGroup 4 is the central involution "
                + "a squared in the order-eight dihedral presentation.", DescribeRole.Definition),
            Item("quaternion-connection", "q8Connection", "The quaternion connection set",
                "The actual connection set is {1,-1}. It includes the identity even "
                + "though the sum graph has no loops.", DescribeRole.Definition),
            Item("dihedral-connection", "d8Connection", "The dihedral connection set",
                "The actual connection set is {1,a squared} in D8. This is the "
                + "exceptional two-element square regime.", DescribeRole.Definition),
            Item("quaternion-matching", "quaternion_result", "The full Q8 matching",
                "In Q8 the center and square set are both exactly {1,-1}. With "
                + "that normal connection set, every group vertex has exactly one "
                + "open neighbor, so the actual sum graph is a perfect matching. "
                + "This is Example 2.3(1), using the existing Mathlib quaternion "
                + "group rather than a scalar certificate.", DescribeRole.Theorem),
            Item("dihedral-matching", "dihedral_result", "The full D8 matching",
                "In D8 the center and square set are both {1,a squared}, and the "
                + "actual sum graph for that connection set is a perfect matching. "
                + "This is Example 2.3(2). The finite decision proofs are ordinary "
                + "Lean proofs; no native evaluation axiom is introduced.", DescribeRole.Theorem),
            Item("quaternion-old-necessity", "quaternion_old_necessity_fails",
                "Every normal Q8 transversal consists of squares",
                "A transversal of a group in itself is a singleton, and normality "
                + "forces its element into the center. In Q8 both central elements "
                + "are squares. Thus the old normal-transversal nonsquare necessity "
                + "fails for this actual matching, while the corrected two-case "
                + "criterion retains it.", DescribeRole.Theorem),
            Item("dihedral-old-necessity", "dihedral_old_necessity_fails",
                "The same necessity failure in D8",
                "Every normal transversal of D8 in itself consists of squares, "
                + "since its singleton representative is central. This refutes "
                + "the old necessity and preserves its surviving sufficiency; "
                + "it does not refute unrelated perfect-code antecedents.", DescribeRole.Theorem),
            Item("proper-product-subgroup", "productSubgroup", "A proper normal subgroup",
                "The actual product subgroup is Q8 times the identity of the "
                + "multiplicative form of ZMod 3. The ambient group has twenty-four "
                + "elements and the subgroup is proper and normal.", DescribeRole.Definition),
            Item("proper-product-connection", "productConnection", "The four specified product elements",
                "The connection set is {(1,0),(-1,0),(1,1),(1,2)} when the "
                + "second coordinate is written additively. It is the exact "
                + "normal subset in Example 2.3(3).", DescribeRole.Definition),
            Item("proper-product-code", "product_result", "The proper-normal code witness",
                "Q8 times the identity is a proper normal total perfect subgroup "
                + "code for the specified four-element connection set. This gives "
                + "the missing-case phenomenon with H proper in G, retaining the "
                + "source distinction from the two H=G examples. No enumeration "
                + "table, regular classification or arbitrary-finite-group "
                + "equivalence is inferred from these examples.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
