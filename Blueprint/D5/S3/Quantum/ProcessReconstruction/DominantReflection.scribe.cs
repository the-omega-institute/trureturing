using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class DominantReflectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/DominantReflection";
    private static readonly LibraryNoteRef Bravyi =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/bravyi2026identitycheck");
    private static readonly LibraryNoteRef Huang =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/huang2024learning");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complementary partial SWAP localizes a test of orthogonal global outputs.",
        H("Amplified Reflection and a Dominant Site"),
        Blocks(
            Describe.Lean(DescribeId.Create("complement-commutator"),
                DeclarationHandle.Create(Module + ".complement_commutator_le"),
                H("Commutator bound after the complementary SWAP"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("Swapping all sites except one transports a system reflection into an amplified observable on the remaining site. The complete diamond error at that site bounds its commutator with the transported unitary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dominant-site-overlap"),
                DeclarationHandle.Create(Module + ".no_zero_overlap_of_dominant"),
                H("A large local error forces nonzero global overlap below total error two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("If one site has error at least one and the total is less than two, the partial SWAP on the other sites and the rank-one reflection bound rule out a unit input vector orthogonal to its unitary image."))),
                DescribeRole.Theorem))));
}
