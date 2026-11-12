using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class IrrationalIndependenceRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/IrrationalIndependenceRoot.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/browncameron2020imaginary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite graph with an irrational purely imaginary independence root.",
        H("An irrational purely imaginary independence root"),
        Blocks(
            Paragraph(Text(
                "Brown and Cameron, A note on purely imaginary independence roots, "
                + "arXiv:2001.08881v2, DOI 10.1016/j.disc.2020.112113, "
                + "Question 2 on printed page 11, ask whether a graph can have "
                + "an independence root bi with irrational real b. The polynomial counts every independent "
                + "vertex subset by cardinality, with the empty subset contributing one. "
                + "There is no prescribed graph order, connectivity, independence number, or lower bound on the modulus.")),
            Describe.Lean(DescribeId.Create("hc-irrational-root-copies"),
                DeclarationHandle.Create(Prefix + "Copies"), H("The recursive tagged carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every type α : Type and every natural n, Copies α n is defined recursively by "
                    + "Copies α 0 = Empty and Copies α (n+1) = α ⊕ Copies α n. "
                    + "The sum tags distinguish successive copies, including the separate empty terminal type. "
                    + "No finiteness assumption is required to define this carrier.")),
                    Paragraph(Text(
                        "The instance copiesFintype supplies Fintype (Copies α n) for every n when α has a Fintype instance. "
                        + "At zero it uses the Fintype instance of Empty; at a successor it installs copiesFintype at n "
                        + "and uses the sum instance on α ⊕ Copies α n. The instance copiesDecidableEq likewise supplies "
                        + "DecidableEq (Copies α n) from DecidableEq α, using Empty at zero and the recursive sum "
                        + "instance at a successor. These instances introduce no restriction on n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-irrational-root-joined-copies"),
                DeclarationHandle.Create(Prefix + "joinedCopies"), H("Joining every tagged copy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any α : Type and G : SimpleGraph α, joinedCopies G n is a SimpleGraph (Copies α n), "
                    + "defined for all natural n by joinedCopies G 0 = ⊥ on Empty and "
                    + "joinedCopies G (n+1) = join G (joinedCopies G n). "
                    + "Here join is the graph on the tagged sum with all cross edges and the original edges within "
                    + "each side. Thus every distinct pair of copies is completely joined, while every individual "
                    + "copy retains G. The definition requires no finite-domain or decidability hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-irrational-root-four-clique-vertices"),
                DeclarationHandle.Create(Prefix + "FourCliqueVertices"), H("The four-clique carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public type abbreviation is FourCliqueVertices := ((Fin 4 ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4. "
                    + "Its left-associated sum tags distinguish the four four-element vertex sets."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-irrational-root-four-cliques"),
                DeclarationHandle.Create(Prefix + "fourCliques"), H("Four disjoint complete graphs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph fourCliques : SimpleGraph FourCliqueVertices is defined by "
                    + "(((⊤ : SimpleGraph (Fin 4)) ⊕g ⊤) ⊕g ⊤) ⊕g ⊤. "
                    + "Each top graph is complete on its own Fin 4 carrier; ⊕g is the disjoint graph sum, "
                    + "so there are no edges between the four summands."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-irrational-root-vertex"),
                DeclarationHandle.Create(Prefix + "Vertex"), H("The complete witness carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public type abbreviation is Vertex := (FourCliqueVertices ⊕ Copies (Fin 2) 34) ⊕ Fin 44. "
                    + "The parenthesized sum retains the four-clique carrier, the thirty-four tagged pairs, "
                    + "and the final forty-four-element carrier as distinct parts."))),
                DescribeRole.Definition),
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
            Describe.Lean(DescribeId.Create("hc-irrational-root-fin-graph"),
                DeclarationHandle.Create(Prefix + "finGraph"), H("Transport to Fin 128"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph finGraph : SimpleGraph (Fin 128) is defined by "
                    + "graph.map (Fintype.equivFinOfCardEq vertex_card).toEmbedding. "
                    + "The internal proof vertex_card establishes Fintype.card Vertex = 128. "
                    + "Fintype.equivFinOfCardEq vertex_card is therefore an equivalence Vertex ≃ Fin 128; "
                    + "graph.map transports edges along its underlying embedding. "
                    + "This specifies the actual graph used in the existential conclusion on the standard finite domain."))),
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
                    + "= (1+2X^2)(1+128X+128X^2). The degree is exactly four. For every "
                    + "natural k, the number of independent k-subsets is 1, 128, 130, 256, 256 "
                    + "for k=0,1,2,3,4 respectively, and zero for every k greater than four. "
                    + "These counts are cardinalities of filtered actual configuration families."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-irrational-root-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Existence with irrational imaginary part"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
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
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brown-cameron-2020-irrational-imaginary-independence-root"),
                    ResolutionKind.Proved)))));
}
