using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class HistoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/History.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/haas2003henneberg");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be any finite vertex type in any universe and G a simple graph on V. The additive Laman counts characterize an actual finite list of legal Henneberg moves starting with K2. No embedding or geometric placement is required.",
        H("The complete finite Henneberg characterization"),
        Blocks(
            Definition("state", "State", "Canonical graph states",
                "A state is a natural number n together with a simple graph on Fin n. There is no upper bound on n. Any graph on a finite type, in any universe, is transported to such a state by its finite enumeration isomorphism."),
            Definition("base", "base", "The initial edge",
                "The base state is n=2 with the complete graph on Fin 2. The reflexive relation closure admits this graph with zero moves."),
            Definition("legal", "Legal", "Independently guarded legal operations",
                "A legal step s to t has either two distinct old vertices a,b and an isomorphism from typeI(s.graph,a,b) to t.graph, or three old vertices a,b,c with an actual edge ab, a!=b, c!=a, c!=b and an isomorphism from typeII(s.graph,a,b,c) to t.graph. Legality does not mention Laman counts. Composing Option.some with the isomorphism gives an injective old-vertex embedding. The image of none is the unique fresh vertex, because every Option value is either none or some old vertex. Type I preserves every old adjacency and joins precisely the two selected old vertices. Type II deletes precisely the selected actual edge, preserves every other old adjacency, and joins precisely the three selected old vertices. These conclusions follow from the exhaustive Option adjacency equations of the move definitions."),
            Definition("history", "HasHistory", "An actual finite legal list",
                "HasHistory G means there is a finite list l of canonical states such that base::l is a Legal chain and G is isomorphic to its last graph. For l empty, that endpoint is base itself. No history is assumed in the counting-to-history direction."),
            Describe.Lean(DescribeId.Create("laman-history-equivalence"),
                DeclarationHandle.Create(Prefix + "laman_iff_history"),
                H("Laman counts if and only if a finite legal history exists"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Write e(G) for the number of unordered edges, card(V) for the finite vertex count, and G[S] for the induced graph on S. The left side requires e(G)+3=2 card(V) and, for every S with card(S)>=2, e(G[S])+3<=2 card(S). The equality already forces at least two vertices, so the Lean statement also covers the empty and singleton vertex types without an extra hypothesis.")),
                    Paragraph(Text("Completeness uses strong induction on the actual vertex cardinality. At cardinality two, tightness identifies G with K2. Otherwise the credited safe-repair theorem supplies a degree-two deletion or a degree-three deletion with a safe actual nonedge bridge. Both smaller graphs are Laman. The induction hypothesis supplies their actual histories; reconstruction identifies G with the corresponding Option operation. Transport the smaller endpoint through its graph isomorphism, append the guarded legal step, and enumerate the new finite vertex type by Fin. The strict subtype cardinality decrease proves termination. The standard reflexive-transitive-closure/list-chain theorem then produces the required finite list.")),
                    Paragraph(Text("Soundness starts from the Laman K2 base and propagates the count invariant along the actual legal chain. Type I preservation and the credited Type II proof of every induced-subset inequality handle the two step cases; endpoint isomorphism transports the result back to G. The final conversion between finite subsets and arbitrary induced vertex sets preserves their exact edge counts. This is the known general Henneberg characterization; the receiving contribution is a complete finite-history construction from the credited repair and preservation proof source."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Definition(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("henneberg-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), s = F.Id("S"), l = F.Id("l");
        Formula counts = And(Eq(Add(Call("edgeCount", g), D(3)), Mul(D(2), Call("card", v))),
            All("S", Call("Set", v), Implies(Le(D(2), Call("card", s)),
                Le(Add(Call("edgeCount", Call("induce", g, s)), D(3)),
                    Mul(D(2), Call("card", s))))));
        Formula chain = Call("Cons", F.Id("base"), l);
        Formula history = ExistsIn("l", Call("List", F.Id("State")),
            And(Call("IsChain", F.Id("Legal"), chain),
                Call("Nonempty", Call("GraphIso", g, Call("graph", Call("Last", chain))))));
        return Disp(All("V", F.Id("Type"), Seq(OpenBracket, Call("Finite", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), Logic(counts, FormulaLogicOperator.Iff, history)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula ExistsIn(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
}
