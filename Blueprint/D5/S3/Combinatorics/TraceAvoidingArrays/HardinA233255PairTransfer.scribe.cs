using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233255PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal seven-column arrays and the exact transfer on labelled six-cell boundaries.",
        H("Positive-height arrays with horizontal and antidiagonal bonds"),
        Blocks(
            Paragraph(Text("Source problem: R. H. Hardin, OEIS A233255, "
                + "https://oeis.org/A233255 (OEIS licence: https://oeis.org/LICENSE). "
                + "The all-height labelled count correspondence below is one part of the "
                + "literal count to canonical-shape transfer argument.")),
            Paragraph(Text("An array is an individual function on a positive number of rows and "
                + "seven columns with values in six colours. Its upper-left colour is zero. "
                + "Only horizontal and upper-right/lower-left antidiagonal bonds exclude equal "
                + "colours and colours whose sum is five. In row-major order each colour two, "
                + "three, or four requires an earlier one, and each three requires an earlier two. "
                + "Missing colours are allowed. No zero-height sequence value is defined.")),
            Node("Row", "Colour rows", "Seven ordered individual colours.", DescribeRole.Definition),
            Node("PairRow", "Pair-label rows", "Seven ordered complementary-pair labels.", DescribeRole.Definition),
            Node("Boundary", "Labelled boundaries", "The six labels in columns one through six.",
                DescribeRole.Definition),
            Node("rowLegal", "Horizontal exclusions", "Every adjacent horizontal bond is tested.",
                DescribeRole.Definition),
            Node("bonds", "Antidiagonal exclusions", "The preceding column j+1 is bonded to the next column j.",
                DescribeRole.Definition),
            Node("Legal", "The literal array predicate", "The existing HardinA233251TriangleStrip.widthLegal "
                + "is applied at width seven with rowLegal and bonds. Its scanner normalization uses strict earlier cells.",
                DescribeRole.Definition),
            Node("a", "The positive-height literal count", "The filter ranges over individual arrays without a quotient.",
                DescribeRole.Definition),
            Node("pairs", "The preceding boundary", "Apply the existing complementary-pair map after discarding column zero.",
                DescribeRole.Definition),
            Node("compatible", "The literal next-row bond test", "Every preceding boundary label excludes its bonded next-row label.",
                DescribeRole.Definition),
            Node("rowProper", "Proper pair words", "Consecutive labels differ.", DescribeRole.Definition),
            Node("labelCompatible", "Compatible pair words", "The six cross-row exclusions are expressed in pair labels.",
                DescribeRole.Definition),
            Node("labelBoundary", "The successor boundary", "Discard column zero only after scanning the entire row.",
                DescribeRole.Definition),
            Node("pairV", "The exact labelled continuation transfer", "Each actual pair word is weighted by its scanner fibre. "
                + "The empty continuation has weight one.", DescribeRole.Definition),
            Node("continuation_pair_bridge", "All continuation heights", "Induction on the number of rows replaces the "
                + "individual-colour row sum by the exact scanner-fibre sum. Both initial scanner flags remain arbitrary.",
                DescribeRole.Theorem),
            Node("literal_pair_bridge", "The anchored literal readout", "The existing literal array decomposition and the "
                + "continuation identity give this equality at every positive height. Fixing its first colour to zero "
                + "leaves six pair labels with the exact scanner weight, so the first-row sum also counts individual "
                + "colours. Precisely, for every natural n, a(n+1) is the integer sum over all functions "
                + "q from Fin 6 to Fin 3 of rowWeight((false,false),q) times "
                + "pairV(n,rowFinish((false,false),q),q), with a zero summand unless the word "
                + "obtained by prepending zero to q is proper. Reducing labelled boundaries to "
                + "the sixteen canonical proper shapes and aggregating "
                + "the first-row weights by those shapes are further mathematical obligations; "
                + "this identity asserts no recurrence.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
