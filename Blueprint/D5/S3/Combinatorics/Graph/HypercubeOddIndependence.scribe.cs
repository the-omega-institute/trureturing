using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HypercubeOddIndependenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeOddIndependence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/caro2025oddindependence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd independence ratio of the Boolean cube converges to one half through all even dimensions.",
        H("Odd independence in even dimensional Boolean cubes"),
        Blocks(
            Paragraph(Text(
                "The graph Q_d consists of all Boolean functions on Fin d, with adjacency at "
                    + "Hamming distance exactly one. Write E for the even parity class. The "
                    + "argument uses binary parity checks, as in the classical Hamming construction "
                    + "described in Kleitman's Matrix Hamming Codes, Sections 9.1 to 9.3. Only the "
                    + "syndrome update under a coordinate flip is needed; no perfectness property "
                    + "for an extended code is assumed.")),
            Describe.Lean(
                DescribeId.Create("odd-independent-set"),
                DeclarationHandle.Create(Prefix + "IsOddIndependent"),
                H("Odd independent sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A finite set S is independent if none of its vertices are adjacent to one "
                        + "another. At each vertex outside S, the number of neighbours belonging "
                        + "to S must be zero or odd. Zero is explicitly permitted; a vertex "
                        + "outside S need not be dominated. Counts use the intersection of the "
                        + "actual cube neighbour set with S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-independence-number"),
                DeclarationHandle.Create(Prefix + "oddIndependenceNumber"),
                H("The finite maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The number is the greatest cardinality attained by an odd independent set, "
                        + "bounded by the full vertex count 2^d. The empty set is admissible, so "
                        + "the selected maximum is attained. Every admissible set has cardinality "
                        + "at most this maximum. Thus the invariant is an actual finite maximum, "
                        + "rather than the size of the particular construction below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("even-cube-odd-independence-limit"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The limit through all even dimensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix k greater than zero and any even d at least 2^k. Label 2^k of the "
                            + "coordinates once each by the vectors in the binary k-dimensional "
                            + "space, including the zero vector. Give every remaining coordinate "
                            + "the zero label. There are an even number of remaining coordinates. "
                            + "Every nonzero label occurs once and zero occurs an odd number of "
                            + "times. Define the syndrome of a vertex to be the sum of the labels "
                            + "at its occupied coordinates. Flipping coordinate i adds its label "
                            + "to the syndrome and reverses vertex parity.")),
                    Paragraph(Text(
                        "For any syndrome a, delete its class from E and call the remaining "
                            + "set S. It is independent because parity changes on every cube edge. "
                            + "An external even vertex has zero neighbours in S. For an odd vertex "
                            + "x, all d neighbours are even. Exactly the coordinates labelled by "
                            + "syndrome(x)+a lead to the deleted class. This count is odd, so its "
                            + "complement among an even number d of coordinates is odd. Hence S "
                            + "satisfies the zero-or-odd condition at every external vertex.")),
                    Paragraph(Text(
                        "The 2^k syndrome classes partition E. The finite pigeonhole principle "
                            + "gives a class of size at most |E|/2^k. Flipping one fixed coordinate "
                            + "bijects the two parity classes, so |E|=2^d/2. Deleting a smallest "
                            + "syndrome class therefore leaves at least "
                            + "2^d times (1/2-1/(2 times 2^k)) vertices. Conversely, any independent "
                            + "set and its image under one fixed coordinate flip are disjoint and "
                            + "have equal cardinality. Its cardinality is at most 2^d/2.")),
                    Paragraph(Text(
                        "The actual maximum lies between these lower and upper bounds. Choose "
                            + "k so that 1/(2 times 2^k) is below the given positive real epsilon, "
                            + "and take D=2^k. The same construction works for every even d at least "
                            + "D. Dividing by the positive real number 2^d gives the absolute error "
                            + "bound in the theorem. This proves the final asymptotic question in "
                            + "Problem 40 and does not determine the exact maximum at each finite "
                            + "even dimension."))),
                DescribeRole.Theorem)),
        []));
}
