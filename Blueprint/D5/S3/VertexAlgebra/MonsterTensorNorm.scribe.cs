using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterTensorNormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterTensorNorm.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/griess1981monsterlocalcompletion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Norton trace Gram coefficient fixes the normalized cubic tensor Frobenius square sum.",
        H("Monster Cubic Tensor Norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-trace-gram-square-sum"),
                DeclarationHandle.Create(Prefix + "symmetric_trace_gram_square_sum"),
                H("Symmetric trace Gram square sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text(
                    "For a finite family of real symmetric square matrices, if every diagonal "
                    + "trace of T_i squared equals c, then the coordinate Frobenius square sum "
                    + "is the cardinality of the index type times c. The proof expands the trace "
                    + "and uses symmetry to turn each entry product into a square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moonshine-tensor-square-sum"),
                DeclarationHandle.Create(Prefix + "moonshine_tensor_square_sum"),
                H("Moonshine tensor numerical square sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text(
                    "Specializing the finite family to dimension 196883 and the Norton "
                    + "coefficient 4620 - 2/3 gives the exact value 2728404614/3. The trace "
                    + "and symmetry hypotheses are inputs from the cited Norton formula; this "
                    + "declaration does not construct a VOA or claim a numerical stability "
                    + "constant for the actual Moonshine tensor."))),
                DescribeRole.Theorem))));
}
