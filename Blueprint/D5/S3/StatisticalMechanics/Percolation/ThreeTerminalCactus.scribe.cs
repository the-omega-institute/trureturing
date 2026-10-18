using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalCactusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant bound is uniform over all finite connected simple cacti, with arbitrary independent bond rates.",
        H("The sharp cactus bound"),
        Blocks(
            Node("cactus_invariant", "A determinant invariant on every cactus",
                "For every finite vertex type V, connected simple graph G on V satisfying "
                + "IsCactus G, three vertices a,b,c of V, and rates theta on the actual edge "
                + "type G.edgeSet with each theta(e) in [0,1], let p=bondLaw G a b c theta. "
                + "Then delta(p)>=0, delta(p)+p(all)*p(ac)<=2*p(ac), and delta(p)<=2*p(ac). "
                + "IsCactus means that "
                + "distinct simple cycles, distinguished by their undirected edge sets, share "
                + "at most one vertex. The terminals may coincide. The source is the finite "
                + "Bernoulli product sum of the actual open-edge connectivity partitions. "
                + "The proof uses induction on the number of actual edges: forests give the "
                + "tree case; a spanning cycle gives three independent arcs; otherwise a "
                + "cycle gate splits the graph into smaller connected induced cacti. All "
                + "five partition events are transported together through actual-edge "
                + "bijections. When one side contains a single marked terminal its only "
                + "contribution is an independent attachment bit; a side with no marked "
                + "terminal is invisible. The strengthened invariant is preserved at each "
                + "of the three possible attachment labels, including deterministic rates "
                + "and zero ac mass. Nonnegativity of the actual source "
                + "masses removes p(all)*p(ac) from the strengthened inequality. The "
                + "four-vertex interior-rate family in ThreeTerminalCactusSharpness already "
                + "shows that every constant smaller than two fails within this graph class; "
                + "the bound is uniform in graph size and number of cactus cycles. "
                + "For the AURIC five-mode source, x records a connected to b, y records "
                + "b connected to c, and z records a connected to c with b separate; "
                + "these are the actual five partition events of this same law. Write "
                + "X=p(ab)+p(all), Y=p(bc)+p(all), Z=p(ac), and kappa=p(all). "
                + "Normalization gives kappa-X*Y/(1-Z)=delta(p)/(1-Z) when Z<1. "
                + "Thus the existing ThreeTerminalCompletion.pyramid_of_bound supplies "
                + "absolute hidden-mass error at most 2*Z/(1-Z) and, for every "
                + "f:Mode->Real, observable error at most abs(J_f)*2*Z/(1-Z), where "
                + "J_f=f(separate)-f(ab)-f(bc)+f(all). The completion keeps X,Y,Z "
                + "and replaces kappa by X*Y/(1-Z). At Z=0 the entire law equals "
                + "this independent completion; at Z=1 it is the ac vertex law. "
                + "These are consequences of the graph bound and normalized source, "
                + "distinct from the numerical escape readings of an AURIC Application.")), []));

    private static DocumentBlock Node(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-cactus-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
