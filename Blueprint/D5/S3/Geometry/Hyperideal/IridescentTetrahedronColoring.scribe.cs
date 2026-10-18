using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class IridescentTetrahedronColoringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/IridescentTetrahedronColoring.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rainbow three-edge colorings of one tetrahedron are exactly the opposite-pair balanced colorings, with six named choices.",
        H("Rainbow colorings of a tetrahedron"),
        Blocks(
            Paragraph(Text("The six local edges are ordered (12,13,14,34,24,23). A color is an element of Fin 3. Each of the four faces is rainbow when its three edge colors are pairwise different.")),
            Describe.Lean(
                DescribeId.Create("iridescent-local-classification"),
                DeclarationHandle.Create(Prefix + "rainbow_iff_opposite_balanced_and_distinct"),
                H("Local rainbow classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every six-edge coloring, all four faces are rainbow exactly when opposite pairs 12/34, 13/24, and 14/23 agree in color and the three pair colors are mutually different. The proof checks the finite three-color cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("iridescent-named-realizations"),
                DeclarationHandle.Create(Prefix + "namedColoring_is_rainbow"),
                H("Named rainbow realizations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assigning a permutation of the three colors to the three opposite pairs produces a rainbow coloring on every face."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("iridescent-named-count"),
                DeclarationHandle.Create(Prefix + "namedColoring_count"),
                H("Six named choices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The permutation group of the three colors has cardinality six, giving six named local choices."))),
                DescribeRole.Theorem))));
}
