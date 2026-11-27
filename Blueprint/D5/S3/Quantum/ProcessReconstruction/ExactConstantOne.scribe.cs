using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.ProcessReconstruction;

internal sealed class ExactConstantOneDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/ProcessReconstruction/ExactConstantOne";
    private static readonly LibraryNoteRef Bravyi =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/bravyi2026identitycheck");
    private static readonly LibraryNoteRef Huang =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/huang2024learning");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of complete single-output diamond errors bounds the global diamond distance with optimal coefficient one.",
        H("Sharp Local-Output Unitary Reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("sharp-constant-one"),
                DeclarationHandle.Create(Module + ".diamond_le_sum_localError"),
                H("The global diamond distance is bounded by the sum of local distances"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("For square unitary channels on a finite tensor product of nonzero local spaces, each observed channel retains one output and accepts the entire global input. The bound holds for unhalved diamond distance with arbitrary finite references. A complementary partial SWAP and a localized reflection handle a dominant local error. An angular estimate along the SWAP chain handles uniformly small errors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-qubit-equality"),
                DeclarationHandle.Create(Module + ".sharp_one_site"),
                H("A single qubit attains equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Bravyi, Huang),
                Blocks(Paragraph(Text("On one qubit there are two conjugation channels whose global distance and complete local distance both equal two. This attains the universal coefficient."))),
                DescribeRole.Theorem))));
}
