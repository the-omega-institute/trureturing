using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class IrrationalIndependenceRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite graph with an irrational purely imaginary independence root.",
        H("An irrational purely imaginary independence root"),
        Blocks(
            Paragraph(Text(
                "Brown and Cameron, A note on purely imaginary independence roots, "
                + "arXiv:2001.08881v2, Question 2 on printed page 11, ask whether a graph can have "
                + "an independence root bi with irrational real b. The polynomial counts every independent "
                + "vertex subset by cardinality, with the empty subset contributing one. "
                + "There is no prescribed graph order, connectivity, independence number, or lower bound on the modulus.")),
            Describe.Lean(DescribeId.Create("hc-irrational-root-graph"),
                DeclarationHandle.Create(Prefix + "graph"), H("A graph with 128 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be the disjoint union of four complete graphs on four vertices. "
                    + "Join A, thirty-four blocks each consisting of two isolated vertices, "
                    + "and a complete graph on forty-four vertices. Distinct join blocks are completely adjacent. "
                    + "The total order is 16+68+44=128. The tagged vertex type and its equivalence to Fin 128 "
                    + "describe actual finite simple undirected graphs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-irrational-root-polynomial"),
                DeclarationHandle.Create(Prefix + "native_polynomial"), H("The native integer polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every nonempty independent subset belongs to exactly one join block. "
                    + "Within A, each of the four cliques contributes either no vertex or one of four vertices, "
                    + "giving (1+4X)^4. Each isolated pair contributes 2X+X^2 beyond the empty subset; "
                    + "the forty-four-clique contributes 44X. Thus the actual independent-subset sum is "
                    + "(1+4X)^4+34(2X+X^2)+44X = 1+128X+130X^2+256X^3+256X^4 "
                    + "= (1+2X^2)(1+128X+128X^2)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-irrational-root-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Existence with irrational imaginary part"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exist n, a simple graph G on Fin n, and an irrational real b such that "
                    + "the complex evaluation of the native integer independence polynomial of G at i*b equals zero. "
                    + "Take n=128 and b=1/sqrt(2). Irrationality follows from irrationality of sqrt(2) "
                    + "and preservation of irrationality under inversion. Since (i*b)^2=-1/2, "
                    + "the factor 1+2X^2 vanishes exactly. Relabeling preserves the full independent-subset sum.")),
                    Paragraph(Text(
                        "The construction answers the unrestricted existential question. It gives no minimum-order "
                        + "claim and no claim that every irrational purely imaginary number is an independence root. "
                        + "The source's separate restriction on square roots of rationals greater than one does not "
                        + "exclude b^2=1/2."))),
                DescribeRole.Theorem))));
}
