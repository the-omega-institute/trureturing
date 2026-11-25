using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class BinaryFaceMomentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Hypercube/BinaryFaceMoments";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-orders face moments of binary cube words",
        H("All-orders face moments of binary cube words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-cube-face-moment"),
                DeclarationHandle.Create(Module + ".faceMoment"),
                H("Positive-face moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a binary cube word f and a set S of prescribed coordinates, the face moment m_f(S) sums f over the vertices containing S. The product of the coordinate bits in S is the indicator of that face. For a support indicator the moment is the parity of the number of support vertices in the face."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-cube-face-moment-adjacency"),
                DeclarationHandle.Create(Module + ".faceMoment_adjacency"),
                H("Adjacency on face moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindex each summand of adjacency by its involutive coordinate flip. In direction j the product of coordinate bits is unchanged if j is outside S. If j is in S, toggling that bit adds the product on S with j deleted. Summing over directions gives n copies of the original moment and one deletion term for each coordinate in S. The same single-flip calculation gives the action of cube translations on moments. Coordinate permutations relabel the prescribed sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-cube-face-moment-characterization"),
                DeclarationHandle.Create(Module + ".adjacency_eq_dim_smul_iff"),
                H("The deletion equations characterize the binary eigenspace"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The adjacency equation Af = (n mod 2) f holds exactly when the sum of m_f(S with i deleted) over i in S is zero for every S. The adjacency identity gives the difference of the two sides in moment coordinates. To recover a word with zero moments, proceed downward from sets of size n. In the moment on S all proper supersets already have zero value, so the moment equals the value at S. This also covers dimension zero.")),
                    Paragraph(Text("For a pivot coordinate a, the equation on S with a adjoined, for S avoiding a, solves for m_f(S) as the sum over i in S of m_f((S with i deleted) with a adjoined). The other deletion equations follow because substituting these expressions pairs the two orders of each double deletion. Thus a candidate can be checked by comparing every pivot-free face parity with its predicted value from pivot-containing faces.")),
                    Paragraph(Text("In Hong, Wu and Xia's Q9 Problem 2, the indicator of a Huang-saturated cubic component is fixed by binary adjacency. Each support vertex has three neighbors in the component, and the signed eigenrow equation forces an even number of component neighbors at exterior vertices. For a Q9 candidate, the 256 pivot comparisons test binary fixedness exactly, so any mismatch excludes the candidate. To project to Q8, sum the two indicator values in each fiber of a deleted coordinate modulo two. The deleted-coordinate flip contributes the projected word itself, so fixedness projects to the Q8 binary kernel equation. The same face equations test the projected word in dimension eight. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
