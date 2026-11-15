using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Potts;

internal sealed class HealingUnboundedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/SpinModels/choi2026healing");
    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula X => F.Id("X");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tree of triangles forces arbitrarily many displaced apices before a stuck tight set can augment.",
        H("Unbounded healing displacement"),
        Blocks(
            Node("frustration", "Two-colour frustration", FrustrationFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "For a finite vertex type V with decidable equality and a simple graph G with decidable adjacency, "
                + "mono(G,c) consists of the unordered edges {u,v} of G for which c(u)=c(v). Each edge is counted once. "
                + "The infimum over all total Boolean colourings is the attained minimum, including the empty graph. "
                + "Boolean values represent the source's states 1 and 2. This is Appendix B's frustration invariant."),
            Node("phi", "Deletion potential", WithSet(Equal(Call("phi", G, X),
                    Add(Card(X), Call("frustration", Deleted(G, X))))), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "X is a finite vertex set. Deletion is the actual induced simple graph on the subtype of all vertices outside X; "
                + "it retains every edge whose two endpoints survive. The cardinality term counts removed vertices."),
            Node("Tight", "Independent tight sets", WithSet(Equal(Call("Tight", G, X),
                    And(Call("IsIndepSet", G, Parenthesized(Seq(X, Colon, Sp, Call("Set", V)))),
                        Equal(Call("phi", G, X), Call("frustration", G))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Tightness includes independence and the equality of the deletion potential to the original frustration. "
                + "It does not mean a maximum independent set or a tight set of maximum cardinality."),
            Node("Augmentable", "Tight independent augmentation", WithSet(Equal(Call("Augmentable", G, X),
                    And(Call("Tight", G, X), Some("v", V,
                        And(Not(Member(F.Id("v"), X)),
                            Call("Tight", G, Insert(F.Id("v"), X))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "The new vertex lies outside X. The enlarged set must be both independent and tight; "
                + "the definition also requires the original set to be tight."),
            Node("Stuck", "Stuck tight sets", WithSet(Equal(Call("Stuck", G, X),
                    And(Call("Tight", G, X), Not(Call("Augmentable", G, X))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "A stuck set is tight and admits no independent tight augmentation, exactly as in the constructive version of Appendix B."),
            Node("claim", "The uniform displacement assertion", Equal(Named("claim"), ClaimBody()),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "The constant C is a natural number common to every finite simple graph on a universe-zero vertex type. "
                + "The type is equipped with Fintype and DecidableEq and the adjacency is decidable. "
                + "The graph is connected, every degree is at most three, and there is no graph isomorphism to the complete graph on Fin 4. "
                + "Every stuck tight S with residual frustration at least one must have an augmentable tight T of the same cardinality "
                + "with at most C vertices of S absent from T. This is the displacement consequence of a uniform stage bound in Section VIII(1)."),
            ClaimedNode("result", "No uniform displacement bound", Not(Named("claim")), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Fix any proposed C and put h=C+1 and B=3·2^h−2. The vertices are pairs of a block in Fin B and a port in Fin 3. "
                + "Every block is a triangle. Root port b joins the apex of block b+1. At each positive block u, ports 1 and 2 join "
                + "the apices of blocks 2u+2 and 2u+3 whenever those blocks exist. These are exactly the complete rooted triangle trees "
                + "of height h, with three children at the root and two at each other internal block. Distinct incoming bridges have "
                + "distinct parent ports, by parity and the separation of the root children 1,2,3 from later children. "
                + "Every vertex therefore has its two triangle neighbours and at most one bridge neighbour. Parent descent proves connectedness. "
                + "There are 3B≥12 vertices, so the graph is not K4. "
                + "Every Boolean colouring leaves a monochromatic edge in each triangle, and the block indices make these edges distinct. "
                + "For the matching upper bound, give every apex a shade and both other ports its opposite. The root shade is false; "
                + "the first child's shade is true and the other two children's shades are false. Below them each child inherits its parent's shade. "
                + "Every bridge is bichromatic and the only monochromatic edge in each triangle is its port-1 to port-2 edge. Thus fr(G)=B. "
                + "Let S contain every positive block's apex. It is independent and has B−1 vertices. Deleting S removes every bridge "
                + "and leaves the root triangle and B−1 isolated edges. Colour those edges properly and the root with one monochromatic edge; "
                + "hence fr(G−S)=1 and S is tight. Every root vertex is adjacent to a child apex in S, and every remaining nonroot port "
                + "is adjacent to its own apex in S. Consequently S has no independent augmentation and is stuck. "
                + "If T is augmentable and |T|=B−1, its augmentation R has B vertices and is independent. The projection from R to blocks "
                + "is injective; equal finite cardinalities make it surjective. Thus R meets each triangle exactly once. Its root selection "
                + "excludes a child's apex. The selected vertex of that child is then a port and excludes the next child's apex. "
                + "For a positive block u whose selected port is nonzero, induction constructs k+1 distinct missing apices whenever "
                + "2^k(u+3)≤B+2: the child c=2u+r(u)+1 satisfies u<c and c+3≤2(u+3), preserving the induction bound. "
                + "The first child has u≤3, so k=C is available. The resulting C+1 apices are outside R and therefore outside T, "
                + "contradicting |S∖T|≤C. No residual-frustration formula for arbitrary deletion sets is needed. "
                + "The source's component-dependent healing theorem remains consistent with this family. A tested set after j chain "
                + "exchanges and one test exchange loses at most j+1 vertices of the original S. Any absolute stage bound would therefore "
                + "give an absolute displacement bound, which the theorem refutes. This implication concerns the number of exchanges; "
                + "zero-based stage labels differ by one and do not change unboundedness.")
        )));

    private static DocumentBlock ClaimedNode(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("potts-healing-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("choi-yoo-kim-kwon-won-2026-healing-chain-unbounded"), ResolutionKind.Refuted));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("potts-healing-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula FrustrationFormula() => Context(Equal(Call("frustration", G),
        Call("sInf", Seq(OpenBrace, Sp, Card(MonochromaticEdges(F.Id("c"))), Sp, Mid, Sp,
            F.Id("c"), Colon, Sp, new Formula.TypeArrow(V, Named("Bool")), Sp, CloseBrace))));

    private static Formula MonochromaticEdges(Formula c)
    {
        Formula e = F.Id("e"), u = F.Id("u"), v = F.Id("v");
        Formula same = And(Equal(e, Call("Sym2.mk", u, v)),
            Equal(new Formula.Apply(c, [u]), new Formula.Apply(c, [v])));
        Formula predicate = Parenthesized(Seq(LambdaLower, Sp, e, Colon, Sp, Call("Sym2", V), Sp,
            Mapsto, Sp, Some("u", V, Some("v", V, same))));
        return Call("Finset.filter", predicate, Call("edgeFinset", G));
    }

    private static Formula ClaimBody()
    {
        Formula s = F.Id("S"), t = F.Id("T"), c = F.Id("C"), v = F.Id("v");
        Formula conclusion = Some("T", Call("Finset", V), And(Call("Augmentable", G, t),
            And(Equal(Card(t), Card(s)), Le(Card(Difference(s, t)), c))));
        Formula sets = All("S", Call("Finset", V), Imp(Call("Stuck", G, s),
            Imp(Le(D(1), Call("frustration", Deleted(G, s))), conclusion)));
        Formula notComplete = Not(Call("Nonempty", Call("SimpleGraph.Iso", G,
            Call("completeGraph", Call("Fin", D(4))))));
        return Some("C", Naturals(), Context(Imp(Call("Connected", G),
            Imp(All("v", V, Le(Call("degree", G, v), D(3))), Imp(notComplete, sets)))));
    }

    private static Formula Context(Formula body) => All("V", new Formula.Subscript(Named("Type"), D(0)),
        Seq(Instance(Call("Fintype", V)), Sp, Instance(Call("DecidableEq", V)), Sp,
            All("G", Call("SimpleGraph", V),
                Seq(Instance(Call("DecidableRel", Call("Adj", G))), Sp, body))));
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket);
    private static Formula WithSet(Formula body) => Context(All("X", Call("Finset", V), body));
    private static Formula Deleted(Formula graph, Formula set) => Call("induce", graph,
        Seq(OpenBrace, Sp, F.Id("v"), Colon, Sp, V, Sp, Mid, Sp,
            Not(Member(F.Id("v"), set)), Sp, CloseBrace));
    private static Formula Insert(Formula v, Formula set) => Call("insert", v, set);
    private static Formula Difference(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Setminus, Sp, b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Not(Formula x) => new Formula.Not(Parenthesized(x));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Named(string name) => Seq(Operatorname, Grp(name switch
    {
        "SimpleGraph.Iso" => Seq(F.Id("SimpleGraph"), Dot, F.Id("Iso")),
        "Sym2" => Seq(F.Id("Sym"), D(2)),
        "Sym2.mk" => Seq(F.Id("Sym"), D(2), Dot, F.Id("mk")),
        "Finset.filter" => Seq(F.Id("Finset"), Dot, F.Id("filter")),
        _ => F.Id(name)
    }));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
