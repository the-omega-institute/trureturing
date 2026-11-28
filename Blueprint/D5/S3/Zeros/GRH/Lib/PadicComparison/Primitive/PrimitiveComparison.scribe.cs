using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Primitive;

internal sealed class PrimitiveComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive Comparison", H("Primitive Comparison"),
        Blocks(
            Paragraph(Text("Primitive comparison and finiteness of mod p cohomology for smooth proper varieties.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitiveComparison.finite_and_primitive_comparison"),
                H("finite_and_primitive_comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Primitive comparison. Let Ω be algebraically closed, Y proper with IsCharted over Ω, and B ↦ B ⊗ M satisfy IsAcyclicOnPerfect (acyclic for tilting at every perfect O^♭-algebra). Then ℤ[Y_Ω] satisfies FP, each Hⁿ(Y_Ω, 𝔽_p) is finite, and primitiveMap ⊗ M is bijective on cohomology along Y(S) → Y_Ω(S[1/p]).")))))));
}
