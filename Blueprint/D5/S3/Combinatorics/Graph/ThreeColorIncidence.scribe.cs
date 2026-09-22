using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ThreeColorIncidenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ThreeColorIncidence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact mixed-incidence counts reduce the reciprocal potential of a properly three-colored graph to two expressions in its unrestricted ordinary and mixed populations.",
        H("Three-color incidence and population reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("neighborhood"),
                DeclarationHandle.Create(Prefix + "neighborhood"),
                H("Finite neighborhoods"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neighborhood of a vertex is the set of vertices in the specified finite set adjacent to it. The ambient type need not be finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed"),
                DeclarationHandle.Create(Prefix + "Mixed"),
                H("Mixed vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A vertex is mixed if two of its neighbors have different colors. For a proper coloring with three colors these are the two colors different from the vertex color."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordinary"),
                DeclarationHandle.Create(Prefix + "ordinary"),
                H("Ordinary populations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinary population U(i,j) consists of the nonisolated vertices of color i all of whose neighbors have color j. A nonisolated vertex is either mixed or lies in exactly one ordinary population."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixedcolor"),
                DeclarationHandle.Create(Prefix + "mixedColor"),
                H("Mixed populations by color"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed population of color i is the set of mixed vertices having that color. Its cardinality is denoted by m(i)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("potential"),
                DeclarationHandle.Create(Prefix + "potential"),
                H("Reciprocal potential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The potential is the sum of the three reciprocals of color-class sizes plus one, together with one half the sum of the reciprocals of degrees plus one. All terms are rational, and empty classes contribute one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("incoming"),
                DeclarationHandle.Create(Prefix + "incoming"),
                H("Available mixed incidences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the ordinary population U(i,j), the available mixed incidences are m(j) when U(j,i) is nonempty and the natural-number difference m(j)-m(i) otherwise. The latter case follows from equality of the two counts of edges between the colors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chargedlower"),
                DeclarationHandle.Create(Prefix + "chargedLower"),
                H("Attachment-charge expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This expression includes the class reciprocals, one sixth of the total mixed population, and one half the sum over distinct i,j of x(i,j)/(x(j,i)+1) minus m(j)/((x(j,i)+1)(x(j,i)+2)). Each mixed incidence is charged the loss caused by a first attachment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadraticlower"),
                DeclarationHandle.Create(Prefix + "quadraticLower"),
                H("Cauchy expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This expression includes the class reciprocals, one sixth of the total mixed population, and one half the sum of x(i,j) squared divided by x(i,j)(x(j,i)+1) plus the available mixed incidences. Empty ordinary populations contribute zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("incidence-reduction"),
                DeclarationHandle.Create(Prefix + "incidence_reduction"),
                H("Exact balance and incidence bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the adjacency relation is symmetric on the finite vertex set, the three-coloring is proper, and every mixed vertex has degree two. For distinct colors i,j, let D(i,j) be the sum of degrees in U(i,j). Then D(i,j)+m(i)=D(j,i)+m(j), and D(i,j) is at most x(i,j)x(j,i)+m(j). In addition, the total number of mixed neighbors counted from U(i,j) is at most m(j), and each individual degree is at most x(j,i) plus its number of mixed neighbors. Every mixed vertex has exactly one neighbor in each of the other two colors. Counting the same edges in both directions gives the balance identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("population-reduction"),
                DeclarationHandle.Create(Prefix + "population_reduction"),
                H("Reduction to actual populations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the preceding graph assumptions, also suppose every vertex is nonisolated. Set m(i) to the actual mixed population and x(i,j) to the actual ordinary population. Then x(i,i)=0, and x(i,j)=0 implies m(j)+x(j,i) is at most m(i). Both the attachment-charge expression and the Cauchy expression are lower bounds for the potential. The class sizes and the mixed contribution follow from the complete vertex partition. The ordinary estimates use, respectively, the discrete decrease of the reciprocal under attachments and Cauchy inequality with the actual degree sum."))),
                DescribeRole.Theorem)),
        []));
}
