using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Physical;

internal sealed class OriginalPhysicalLieDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual original physical-state quotient carries the zero-mode Lie bracket.",
        H("The original physical state Lie algebra"),
        Blocks(
            Describe.Lean(DescribeId.Create("exact-representative-bracket"),
                DeclarationHandle.Create(Prefix + "physicalBracket_mk"),
                H("Exact quotient representative bracket"),
                StatementSource.FromAuthor(Disp(Text("The quotient bracket of two physical weight-one classes is represented literally by the original zero mode a_0 b."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quotient is exactly P^1 modulo the image of the actual translation restricted to P^0. The skew primitive is finite and physical, so antisymmetry descends through this exact image. Jacobi is inherited from the actual zero-mode commutator."))),
                DescribeRole.Theorem),
            Paragraph(Text("This unit formalizes the matter physical-state Lie algebra only. It does not identify it with BRST cohomology or discharge the independent original BRST, HPL, no-ghost, string and AdS/CFT obligations.")))));
}
