using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickPaddedCyclesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickPaddedCycles.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform padding supplies simple cycles beyond every face count above six.",
        H("EaslickPaddedCycles"),
        Blocks(
            Node("easlick-padded-cycle", "Uniform nested padding", "padded_cycle",
                "For every r at least three, every positive even k, and every t with r+6 at most r+2t, a simple k-cycle for r-face dice gives a simple k(t+1)-cycle for (r+2t)-face dice. Enumerate the clone blocks by j from zero through t and, inside each block, enumerate the seed positions. Adjacent positions have opposite parity, including block transitions and the final closing edge because k is even. The central faces recover the seed position, and the multiplicity of the first low label recovers j, proving that all k(t+1) vertices are distinct."),
            Node("easlick-longer-cycle", "All parameters above six", "longer_cycle",
                "For every natural n at least seven, some k greater than n satisfies HasCycle(n,k). The finite cycles cover seven through eleven. For even n at least twelve use the six-face six-cycle and t=(n-6)/2; for odd n at least thirteen use the seven-face fourteen-cycle and t=(n-7)/2. The resulting lengths are 6(t+1) and 14(t+1), respectively, and both strictly exceed n. All vertices are explicit valid dice in the same graph and every edge uses the actual attained unconditional minimum."),
            Node("easlick-not-s-above-six", "Failure of an exact n bound above six", "not_S_above_six",
                "For every natural n at least seven, S(n) is false: the simple longer cycle contradicts its universal upper-bound clause. No assumed existence premise is added to the target.")
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
