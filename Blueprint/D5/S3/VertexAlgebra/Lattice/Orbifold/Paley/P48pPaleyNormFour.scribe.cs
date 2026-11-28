using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.Paley;

internal sealed class P48pPaleyNormFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ternary small-support bound implies squared-norm-four exclusion in the catalogue odd neighbor.",
        H("The P48p Paley Norm-Four Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("p48p-paley-norm-four-reduction"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyNormFour.norm_ne_four_of_paley_small_support"),
            H("Small-support exclusion suffices for the odd neighbor"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Squared norm four would give a Paley graph pair with a nonzero input of Hamming weight at most "
                + "six and total Hamming weight at most twelve. A strict bound above twelve on all such nonzero "
                + "inputs therefore rules out squared norm four."))),
            DescribeRole.Theorem))));
}
