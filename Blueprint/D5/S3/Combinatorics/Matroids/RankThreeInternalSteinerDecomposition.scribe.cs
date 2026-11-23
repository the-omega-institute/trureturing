using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeInternalSteinerDecompositionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal extensions with the extra ternary potential dimension are organized by rows and residue classes.",
        H("Latin Squares and Partial Steiner Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-steiner"),
                DeclarationHandle.Create(Module + ".IsPartialSteiner"),
                H("Partial Steiner triple systems"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A system is an unordered family of three-element sets. Two distinct labels occur together in at most one member."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("extended-family"),
                DeclarationHandle.Create(Module + ".extendedFamily"),
                H("The unordered extension from the square and packing data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each square gives the different-residue triples in its row. Each partial Steiner system adds triples inside one actual residue class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-decomposition"),
                DeclarationHandle.Create(Module + ".forward_decomposition"),
                H("An extension with the extra dimension splits into squares and partial systems"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The residue condition forbids a triple with exactly two residues. The different-residue triples cover every required pair and give the Latin square in each row. The remaining triples project to pair-unique triples in their own residue classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realize-decomposition"),
                DeclarationHandle.Create(Module + ".realize_decomposition"),
                H("Independent square and packing data give an extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose an enumeration for each three-element block in a partial system and transport its labels back into the residue class. The fixed mixed family, the Latin squares, and the partial Steiner systems each give pair uniqueness within their own component. Their three kinds of pairs are disjoint, so pair uniqueness also holds across components. Adding the latter triples preserves the dimension criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decomposition-unique"),
                DeclarationHandle.Create(Module + ".decomposition_unique"),
                H("The unordered extension determines all of its data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three distinct residues of a Latin triple distinguish it from every same-residue triple. A same-residue triple identifies its row and residue class, and its labels are recovered using the given bijection. Thus the unordered family recovers every square entry and every block."))),
                DescribeRole.Theorem))));
}
