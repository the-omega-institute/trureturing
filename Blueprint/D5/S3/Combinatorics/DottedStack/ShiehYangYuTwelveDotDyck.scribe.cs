using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DottedStack;

internal sealed class ShiehYangYuTwelveDotDyckDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotDyck.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bijection from 231-avoiding permutations to Dyck paths carries left-to-right maxima to primitive excursions.",
        H("231-Avoiding Permutations and Dyck Paths"),
        Blocks(
            Node("syy-twelve-dot-avoiding-encode-definition", "Encode an avoiding permutation", "avoiding_encode",
                "For every natural number m, avoiding_encode maps a 231-avoiding permutation "
                + "of [1,...,m] to a Dyck path of semilength m. A Dyck path has up and down "
                + "steps, starts and ends at height zero, and never has negative height. The "
                + "empty permutation maps to the empty path. A nonempty permutation splits "
                + "at its maximum into a left permutation of [1,...,k] and a right permutation "
                + "whose values are decreased by k. Its path is the left path followed by the "
                + "right path enclosed between an up step and a down step.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-last-excursion-definition", "The last primitive excursion", "lastExcursion",
                "The map lastExcursion returns a pair of Dyck paths. On the empty path it "
                + "returns two empty paths. On a nonempty path, the first component is the "
                + "prefix preceding the last primitive excursion and the second is the path "
                + "inside that excursion, with its initial up step and final down step removed. "
                + "A primitive excursion is a nonempty Dyck path that returns to height zero "
                + "only at its end.", DescribeRole.Definition),
            Node("syy-twelve-dot-last-excursion-theorem", "Reconstruct the last excursion", "last_excursion",
                "Every nonempty Dyck path is the concatenation of the first component of "
                + "lastExcursion and the second component enclosed between an up step and a "
                + "down step. Conversely, for any Dyck paths A and B, lastExcursion applied "
                + "to A followed by B enclosed between an up step and a down step returns "
                + "exactly the pair (A,B).", DescribeRole.Theorem),
            Node("syy-twelve-dot-avoiding-decode-definition", "Decode a Dyck path", "avoiding_decode",
                "For every Dyck path of semilength m, avoiding_decode returns a 231-avoiding "
                + "permutation of [1,...,m]. The empty path gives the empty permutation. For "
                + "a nonempty path, write (A,B) for lastExcursion and let k be the semilength "
                + "of A. The decoded word is the decoded word of A, followed by the maximum "
                + "m, followed by the decoded word of B with k added to every entry.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-excursions-definition", "Interiors of primitive excursions", "excursions",
                "For every Dyck path, excursions is the ordered list of the interiors of "
                + "its primitive excursions. Each interior is obtained by removing the "
                + "initial up step and final down step of its excursion. The empty path "
                + "gives the empty list. A nonempty path contributes its first excursion's "
                + "interior, followed by the list obtained from the remaining path.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-avoiding-inverse-theorem", "Inverse maps and record counts", "avoiding_inverse",
                "For every natural number m and every 231-avoiding permutation of [1,...,m], "
                + "decoding its encoded path recovers the permutation. For every Dyck path, "
                + "encoding its decoded permutation recovers the path. For every such "
                + "permutation, the number of record values equals the length of the "
                + "excursions list of its encoded path, so records correspond in number "
                + "to primitive excursions.", DescribeRole.Theorem),
            Node("syy-twelve-dot-excursion-equivalence-definition", "Dyck paths as lists of excursion interiors", "excursion_equiv",
                "The bijection excursion_equiv sends a Dyck path to its excursions list "
                + "and sends any finite list of Dyck paths back to the concatenation obtained "
                + "by enclosing each member between an up step and a down step. These two "
                + "maps are inverse on all Dyck paths and all finite lists of Dyck paths, "
                + "including the empty path and empty list.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
