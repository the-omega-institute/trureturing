using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three independent arc events retain the complete terminal partition law "
            + "of an actual finite simple cycle.",
        H("Independent bond percolation on simple cycles"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-terminal-actual-cycle-law-and-invariant"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycle.cycle_law_and_invariant"),
                H("Full cycle law and strengthened determinant bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every simple graph G with finite actual edge type, simple closed "
                        + "walk p whose edge set is exactly G.edgeSet, three pairwise distinct "
                        + "vertices a,b,c in p.support, and independent rates theta:G.edgeSet->R "
                        + "in [0,1], there exist u,v,r in [0,1] such that the entire five-mode "
                        + "bondLaw G a b c theta equals the law on triangleArmsEnds with "
                        + "rates [u,v,r,1,1,1]. Put P=bondLaw G a b c theta and Z=P(ac). "
                        + "Then 0 <= delta(P), and delta(P)+P(all)Z <= 2Z. "
                        + "Rotate and, if necessary, reverse the cycle to order its marked "
                        + "vertices. A bijection identifies its actual undirected edges with "
                        + "cyclic coordinates and preserves the complete Bernoulli product "
                        + "weight. Each configuration has the same full partition as the "
                        + "triangle of its three all-open arc bits; the arc supports are "
                        + "disjoint. The result includes rates zero and one, and allows "
                        + "additional isolated vertices outside the cycle."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-terminal-coincident-invariant"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycle.coincident_terminal_invariant"),
                H("Coincident terminal labels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every simple graph G with finite edge type, vertices a,b,c with "
                        + "a=b or a=c or b=c, rates theta in [0,1], and real C>=1, put "
                        + "P=bondLaw G a b c theta and Z=P(ac). Then 0<=delta(P) and "
                        + "delta(P)+P(all)Z<=C Z. In fact delta(P)=0: no configuration "
                        + "has three separated labels, and at least one of the ab and bc "
                        + "modes is impossible. Nonnegativity and normalization give "
                        + "P(all)<=1. No cycle or connectivity assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-terminal-cycle-invariant"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycle.cycle_invariant"),
                H("Every marked triple on a cycle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every simple graph G with finite actual edge type, simple closed "
                        + "walk p with G.edgeSet=p.edgeSet, arbitrary a,b,c in p.support, "
                        + "and rates theta in [0,1], the actual partition law P satisfies "
                        + "0<=delta(P) and delta(P)+P(all)P(ac)<=2P(ac). The three labels "
                        + "may coincide. Distinct labels use the independent three-arc "
                        + "law; coincident labels have zero determinant."))),
                DescribeRole.Theorem)), []));
}
