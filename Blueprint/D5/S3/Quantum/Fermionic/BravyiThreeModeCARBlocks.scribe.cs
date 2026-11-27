using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BravyiThreeModeCARBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.";
    private const string Digest = "Clifford conjugations and the exact block reduction of the three-mode channel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Digest, H("The three-mode channel in chiral coordinates"), Blocks(
            Entry("majorana_anticomm", "The Majorana relations",
                "Distinct Majorana matrices anticommute. The signed row permutations compute the two products over the Gaussian integers."),
            Entry("conjugateWord_majorana_prod", "The action on Majorana products",
                "Conjugation by a Clifford word gives a sign on each Majorana generator. The signs multiply on an ordered word of generators."),
            Entry("channel_normal_blocks", "Exact real blocks for the normal form",
                "Take the rank-one projector of the real spinor with entries c, 0, 0, 0, p, q, 0, 0 and squared norm one. Applying the weighted Clifford channel and changing to the signed basis gives the complex embedding of the four-dimensional chiral block and two copies of the two-dimensional complementary block."),
            Entry("determinantBlocks_charpoly", "The block characteristic polynomial",
                "The signed ordering places the three blocks on the diagonal. The characteristic polynomial of the assembled real matrix is the chiral characteristic polynomial times the square of the complementary characteristic polynomial."))));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("bravyi-car-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
