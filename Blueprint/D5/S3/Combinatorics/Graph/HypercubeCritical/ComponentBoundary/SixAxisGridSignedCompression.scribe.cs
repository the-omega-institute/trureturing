using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class SixAxisGridSignedCompressionDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "SixAxisGridSignedCompression";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Huang compression on the six-axis cubical grid",
        H("Four sums over the internal coordinate blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("six-axis-grid-signed-projection"),
                DeclarationHandle.Create(Module + ".project"),
                H("The four unnormalized sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Split the nine axes into three contiguous three-axis blocks A, B and E. "
                    + "A selected axis is a false bit at the all-true origin. For each fixed "
                    + "exterior vertex in E, let p be the empty internal entry, r the sum over "
                    + "A singletons, q the sum over B singletons and s the sum over the nine "
                    + "mixed A/B pairs. These are integer sums with no averaging."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("six-axis-grid-signed-exterior-action"),
                DeclarationHandle.Create(Module + ".exteriorAction"),
                H("The signed action in the exterior block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operator K sums the three signed exterior flips. Each flip has "
                    + "coefficient minus one to the power of the number of earlier false "
                    + "bits in E, using the same convention as the nine-axis Huang action."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("six-axis-grid-signed-intertwiner"),
                DeclarationHandle.Create(Module + ".project_weightedAction"),
                H("The signed four-sum identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the unit-weight integer Huang action and then take the four "
                        + "sums. In order p, r, q, s the result is r + q + Kp, "
                        + "3p − s − Kr, 3p + s − Kq, 3q − 3r + Ks. "
                        + "The real scalar extension of the input action agrees with the "
                        + "Huang operator by weightedAction_real.")),
                    Paragraph(Text(
                        "A block permutation permutes the selected axes and acts with the "
                        + "sign of their induced reordering. At a vertex with two selected "
                        + "axes in a block their transposition fixes the vertex and reverses "
                        + "the sign. An invariant integer covector therefore vanishes there. "
                        + "The empty and singleton orbits in each block have trivial "
                        + "stabilizer signs. Together they give the four sums at each of eight "
                        + "exterior vertices.")),
                    Paragraph(Text(
                        "The proof uses the corresponding row cancellation. For axes i < j "
                        + "in one block, the row of singleton i has coefficient −1 to their "
                        + "doubleton, while the row of singleton j has coefficient +1. "
                        + "Pairing them cancels each doubleton even with arbitrary values "
                        + "on those vertices. The preceding A block contributes a minus sign "
                        + "to B flips in A singleton rows. The two internal blocks give "
                        + "exterior signs +, −, −, + across the four sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-axis-grid-signed-mixed-divisibility"),
                DeclarationHandle.Create(Module + ".three_dvd_mixed_of_eigen"),
                H("The exterior mixed sum obeys a congruence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an integral three-eigenfunction, the mixed row gives "
                        + "Ks = 3(s − q + r) at every exterior vertex. Thus the mixed "
                        + "profile reduced modulo three is killed by the signed exterior "
                        + "action, coupling its values at all three neighboring vertices.")),
                    Paragraph(Text(
                        "Hong–Wu–Xia Problem 2 asks whether the minimum maximum induced degree "
                        + "on 258 vertices of Q9 is three or four. In its cubical-subdivision branch the "
                        + "normalized six-axis grid has three axes in each branch class. "
                        + "The switching signs of a balanced induced cubic support, extended "
                        + "by zero, supply a three-eigenfunction. Its signed counts on the "
                        + "mixed middle vertices in the eight exterior layers must satisfy "
                        + "the congruence. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("six-axis-grid-signed-singleton-reconstruction"),
                DeclarationHandle.Create(Module + ".reconstruct_single_profiles_of_eigen"),
                H("The empty and mixed profiles determine the singleton sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-eigenfunction, the singleton equations are "
                    + "(3 + K)r = 3p − s and (3 + K)q = 3p + s. The weighted Huang "
                    + "square identity specialized to the three exterior axes gives K² = 3I. "
                    + "Applying 3 − K gives the integer identities 6r = (3 − K)(3p − s) "
                    + "and 6q = (3 − K)(3p + s). These determine both singleton sums "
                    + "from the empty and mixed profiles without dividing inside the integer proof."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9IsotropicHuang"))
        ]));
}
