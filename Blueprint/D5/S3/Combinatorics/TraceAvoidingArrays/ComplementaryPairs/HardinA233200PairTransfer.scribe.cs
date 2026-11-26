using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233200PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200PairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal eight-colour six-column arrays and their exact weighted pair transfer.",
        H("Anchored literal arrays and all three bond types"),
        Blocks(
            Paragraph(Text("The pair fibres are {0,7}, {1,6}, {2,5}, and {3,4}. Scanner flags retain actual earlier occurrences of colours one, two, and three. The generic literal counting decomposition is HardinA233196Strip.width_counting_bridge.")),
            Node("Row", "Colour rows", "Six ordered individual colours from zero through seven.", DescribeRole.Definition),
            Node("PairRow", "Pair-label rows", "Six ordered labels for the four complementary pairs.", DescribeRole.Definition),
            Node("Boundary", "Labelled boundaries", "All six labels of the preceding row.", DescribeRole.Definition),
            Node("rho", "Strict row-major index", "The index of cell (i,j) is six times i plus j.", DescribeRole.Definition),
            Node("rowLegal", "Horizontal exclusions", "Every adjacent pair in a row is unequal and has natural-number sum different from seven.", DescribeRole.Definition),
            Node("bonds", "Vertical and antidiagonal exclusions", "Each preceding cell is bonded to the next row in the same column. Each preceding cell in column j+1 is also bonded to the next cell in column j. Both exclusions forbid equality and natural-number sum seven.", DescribeRole.Definition),
            Node("Legal", "The literal array predicate", "The upper-left colour is zero and every contained horizontal, vertical, and antidiagonal bond satisfies the exclusions. Colours two through six require a strictly earlier one; three, four, and five require a strictly earlier two; four requires a strictly earlier three. Earlier means a smaller rho value. No occurrence of an unused colour is required.", DescribeRole.Definition),
            Node("a", "The positive-height literal count", "Count all individual functions from the positive-height six-column rectangle to eight colours that satisfy Legal.", DescribeRole.Definition),
            Node("pairs", "The preceding boundary", "Apply the existing complementary-pair map to every cell of the row.", DescribeRole.Definition),
            Node("compatible", "The individual next-row test", "Pair labels express the six vertical and five antidiagonal exclusions.", DescribeRole.Definition),
            Node("rowProper", "Proper label rows", "Consecutive labels differ.", DescribeRole.Definition),
            Node("labelCompatible", "Cross-row compatibility", "All six vertical and five antidiagonal pairs have distinct labels.", DescribeRole.Definition),
            Node("labelBoundary", "The successor boundary", "Retain the entire labelled row.", DescribeRole.Definition),
            Node("pairV", "Weighted continuation transfer", "The empty continuation has value one. For each additional row sum over all proper compatible label rows, multiplying their exact scanner multiplicity by the next continuation value.", DescribeRole.Definition),
            Node("continuation_pair_bridge", "Every continuation height and state", "For every natural continuation height, every initial three-flag state, and every labelled boundary, the existing eight-colour continuation equals pairV. The exact scanner pushforward replaces each individual-colour row sum. The source.state_binder audit binding is unfinished under https://github.com/the-omega-institute/trureturing/issues/28653.", DescribeRole.Theorem),
            Node("literal_pair_bridge", "The exact anchored readout", "For every natural n the literal count at height n+1 equals the weighted sum over five-label words q. Prepend label zero and retain the summand only when that six-label word is proper. The summand is rowWeight from the three false flags along q, times pairV at n with rowFinish along q and boundary obtained by prepending zero. The fixed first colour has multiplicity one and leaves all flags false. This identity includes every positive height and gives the literal input for the 58-state reduction.", DescribeRole.Theorem),
            Node("seen", "Stage flags", "Stage k records flags one through k as seen.", DescribeRole.Definition),
            Node("finalStage", "Stage after scanning", "Take the highest recorded flag index, or zero if all flags are false.", DescribeRole.Definition),
            Node("nativeStage", "Historical scanner stage", "The 58 states contain one canonical proper boundary with two available pair labels, sixteen with three available labels, and forty-one with four available labels. The stage is the number of available labels minus one.", DescribeRole.Definition),
            Node("nativeRepresentative", "Canonical proper boundaries", "Each boundary is a restricted growth word beginning zero, one. Rows related by a permutation of the already available labels have the same continuation; unavailable labels are fixed. Canonicalization retains the historical stage even if an available label is absent from the current boundary.", DescribeRole.Definition),
            Node("nativeClassOf", "Stage-preserving boundary class", "For a proper six-label boundary using only labels zero through its positive stage, relabel by order of first occurrence and select the corresponding state at that same stage.", DescribeRole.Definition),
            Node("nativeT", "The exact finite weighted transfer", "Entry (i,j) sums rowWeight over every proper six-label row compatible with representative i whose final scanner stage and normalized boundary have class j. Compatibility includes six vertical and five antidiagonal bonds. The scanner starts at the three flags encoded by stage i. Every weighted nonzero successor has a valid positive stage and uses only labels available at its final stage.", DescribeRole.Definition),
            Node("nativeInitial", "Anchored initial vector", "Component i sums the exact rowWeight of all five-label words q for which zero prepended to q is proper and its final stage and boundary have class i. The individual first colour is fixed to zero and has weight one; no unused label is required to occur.", DescribeRole.Definition),
            Node("native_linear_bridge", "All positive heights as a finite linear readout", "For every natural n the original literal count a(n+1), cast to the integers, equals the dot product of nativeInitial with nativeT to the power n applied to the constant-one vector. The proof transports the exact pairV continuation through permutations of already available labels and retains every scanner stage. The terminal readout is one in all 58 states. This is the all-height semantic bridge used by HardinA233200Recurrence.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
