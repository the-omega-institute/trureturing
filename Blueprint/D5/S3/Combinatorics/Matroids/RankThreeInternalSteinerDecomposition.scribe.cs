using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeInternalSteinerDecompositionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeInternalSteinerDecomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal extensions with the extra ternary potential dimension are organized by rows and residue classes.",
        H("Latin Squares and Partial Steiner Systems"),
        Blocks(
            Paragraph(
                Text("For extraction and realization, let "), Math(Id("d")), Text(" and "),
                Math(Id("r")), Text(" be positive integers. A row is a vector of "),
                Math(Id("d")), Text(" ternary coordinates. A point consists of a row and a cyclic coordinate modulo "),
                Math(Multiply(Num(3), Id("r"))), Text(". Label the points in each row by a fixed bijection "
                    + "with pairs of a ternary residue and one of the "), Math(Id("r")),
                Text(" labels. The first coordinate of each bijection is reduction of the cyclic coordinate modulo three.")),
            Paragraph(Text(
                "Fix an existing indexed family of lifted triples on three distinct rows. Each triple sums to zero in the product group, "
                + "and every pair on distinct rows occurs with its zero-sum completion. Each pair of distinct points is covered by at most one index. "
                + "For an extended family, a ternary potential vanishes at the zero point, sums to zero over all points and on each triple, "
                + "and takes equal values at the two points of any uncovered pair.")),
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
                Blocks(Paragraph(Text(
                    "For each cell, lift its two indices as labels in residues zero and one and its square entry in residue two. "
                    + "For each block of a partial Steiner system, lift its three labels within its specified row and residue class. "
                    + "The unordered internal family is the union of these two sets of triples."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-decomposition"),
                DeclarationHandle.Create(Module + ".forward_decomposition"),
                H("An extension with the extra dimension splits into squares and partial systems"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(
                        Text("Assume each added triple consists of three distinct points in a single row, each pair of distinct points "
                            + "is covered by at most one index of the combined family, and the combined normalized potential space has dimension "),
                        Math(Add(Id("d"), Num(1))),
                        Text(". Then the unordered added triples equal the family built from one Latin square per row and one partial Steiner "
                            + "system per row and residue.")),
                    Paragraph(Text(
                        "The residue condition forbids a triple with exactly two residues. The different-residue triples cover each pair "
                        + "from different residues in the same row and give the Latin square there. The remaining triples project to "
                        + "pair-unique blocks in their own residue classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realize-decomposition"),
                DeclarationHandle.Create(Module + ".realize_decomposition"),
                H("Independent square and packing data give an extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(
                        Text("With the fixed pair-unique lifted family and the residue-preserving labellings above, choose a Latin square in each row "
                            + "and a partial Steiner system of labels in each row and residue. These data give a finitely indexed internal extension "
                            + "with exactly the prescribed unordered triples. All triples in the combined family have distinct points, "
                            + "each distinct pair is covered by at most one index, and the normalized potential space has dimension "),
                        Math(Add(Id("d"), Num(1))), Text(".")),
                    Paragraph(Text(
                        "Enumerate each packing block and lift its labels back into the residue class. Mixed triples use pairs on different rows, "
                        + "Latin triples use pairs on one row in different residues, and the packing triples use pairs inside a single residue class. "
                        + "The same-residue triples preserve the potential dimension of the Latin extension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("decomposition-unique"),
                DeclarationHandle.Create(Module + ".decomposition_unique"),
                H("The unordered extension determines all of its data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed rowwise labelling bijection, take two assignments of tables and two assignments of partial Steiner "
                        + "systems, one system per row and residue. If their unordered internal families are equal, the tables agree entry by entry "
                        + "and the systems agree in every row and residue.")),
                    Paragraph(Text(
                        "A triple meeting three residues gives its cell indices and entry. A same-residue triple gives its row, residue, "
                        + "and three labels through the fixed bijection."))),
                DescribeRole.Theorem))));
}
