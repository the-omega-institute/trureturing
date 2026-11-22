using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The intrinsic C2 span of the actual sign-fixed lattice vertex algebra.",
        H("The Intrinsic Lattice Fixed C2 Span"),
        Blocks(
            Paragraph(Text("The lattice data consist of a natural-number rank and a symmetric integral Gram "
                + "matrix with even diagonal. The actual complex carrier consists of finitely supported "
                + "charge families of oscillator polynomials.")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-span"),
                DeclarationHandle.Create(Prefix + "fixedC2"),
                H("The intrinsic fixed C2 span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed space consists of the states fixed by the lattice sign "
                    + "involution. The intrinsic C2 submodule is the complex span in that space of the "
                    + "restricted actual (-2)-products of pairs of fixed states. The intrinsic quotient "
                    + "is the fixed space modulo this span."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-translation"),
                DeclarationHandle.Create(Prefix + "translation_mem_fixedC2"),
                H("Translation of a fixed state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The translation of every fixed state lies in the intrinsic C2 span. "
                    + "It is the fixed (-2)-product of that state with the fixed vacuum."))),
                DescribeRole.Theorem))));
}
