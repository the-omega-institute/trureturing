using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeAnalyticWeightTwelveDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeAnalyticWeightTwelve";
    private static readonly LibraryNoteRef CubeCode =
        LibraryNoteRef.Create("D5/L/Hamming/fishkeymwambene2009cubecodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every weight-twelve kernel word is the binary sum of two shells whose centers have Hamming distance two.",
        H("Weight-twelve binary adjacency-kernel words on the eight-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weight-twelve-two-shells"),
                DeclarationHandle.Create(Module + ".weight_twelve_two_shells"),
                H("Every weight-twelve kernel word is a sum of two distance-two shells"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(CubeCode),
                Blocks(
                    Paragraph(Text("Let f be a binary word on Q8 with zero adjacency and support size twelve. There are vertices " +
                        "x and y and distinct coordinates i and j such that y is obtained from x by flipping i and j, " +
                        "and f is the adjacency of δₓ + δᵧ. Equivalently, the support is the symmetric difference of " +
                        "the open neighbor shells of x and y.")),
                    Paragraph(Text("If for every pair through coordinate zero one opposite sum vanishes, the star conjugation " +
                        "and radial kernel equations force weight eight. Hence a pair has both sums nonzero. A " +
                        "coordinate permutation preserving adjacency and weight moves that pair to the first two " +
                        "positions. The sharp split determines the two centers there, and the coordinate permutation " +
                        "carries them back to the original cube.")),
                    Paragraph(Text("Fish, Key and Mwambene record minimum weight n for the binary adjacency code of a " +
                        "positive even-dimensional cube in §4, Result 2. Here BinaryKernelMinimum supplies the " +
                        "classification of the minimum supports used on Q6. The repository derives the Q8 " +
                        "weight-twelve form by the sharp split and reconstruction.")),
                    Paragraph(Text("For the axial Q8 fold in the study of Hong–Wu–Xia, §7, Problem 2, the repository's " +
                        "one-site exchange argument applies this theorem twice to a twelve-site projection with a " +
                        "twelve-site binary adjacency syndrome. The syndrome is a kernel word because Q8 adjacency " +
                        "squares to zero. Its shell centers identify a one-site exchange that gives a new twelve-site " +
                        "support in the kernel. The second application identifies the new support's two shells. " +
                        "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weight-less-twelve-one-shell"),
                DeclarationHandle.Create(Module + ".weight_less_twelve_one_shell"),
                H("Every nonzero kernel word below weight twelve is one shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f be a binary adjacency-kernel word on Q8 of positive weight strictly below twelve. A " +
                        "pair through coordinate zero with both opposite sums nonzero would force weight twelve. " +
                        "Consequently the radial alternative applies, giving a radius-one or radius-seven layer after " +
                        "translation. Undoing the translation identifies the word as the adjacency of a singleton at " +
                        "the translation center or its antipode. Its support has eight sites."))),
                DescribeRole.Theorem)),
        []));
}
