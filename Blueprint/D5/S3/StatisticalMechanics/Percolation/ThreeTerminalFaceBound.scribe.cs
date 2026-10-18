using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalFaceBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-edge estimate for the actual independent three-terminal partition law.",
        H("The complementary-configuration bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-terminal-face-edge-count-bound"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceBound.edge_count_bound"),
            H("A uniform bound for a fixed number of independent edges"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite vertex type V with decidable equality, finite edge-index "
                + "type E with decidable equality, endpoint function ends:E->V*V, marked "
                + "vertices a,b,c, and independent rates theta:E->Real in [0,1], put "
                + "m=card(E) and p=law ends a b c theta. If m>0, then "
                + "abs(delta(p))<=2^(m-1)*p(ac). The law is the finite Bernoulli sum "
                + "over actual open-edge connectivity partitions, independently defined "
                + "before the estimate; loops or repeated endpoint pairs are permitted "
                + "as independent indexed coordinates. No distinct-terminal hypothesis "
                + "or division by p(ac) is used. "
                + "Two ordered configurations are grouped by each edge's open-copy "
                + "multiplicity 0,1,2. Within each face all pairs have the same "
                + "nonnegative product weight. A face with no ac configuration has "
                + "equal (separate,all) and (ab,bc) counts by the fixed-coordinate "
                + "switch. On every other face the first-copy map is injective, "
                + "and exchanging the two copies pairs each target count with an "
                + "equal disjoint reversed count. Hence their difference is at most "
                + "2^(m-1) times the number of first-copy ac occurrences. The final "
                + "sum uses Z=Z*1, expanding the full second configuration cube; "
                + "deterministic edge rates merely set some face weights to zero. "
                + "This is the finite central-network estimate. The block-rank "
                + "bound still requires a complete five-law block reduction and "
                + "a rank-preserving series/parallel compression argument."))),
            DescribeRole.Theorem)), []));
}
