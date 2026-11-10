using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class EliminationForestDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universe u is arbitrary. IsPEO(G,ord) has exactly two fields: ord is injective, and for each v the set of neighbors u with ord(v) < ord(u) is a clique. RelativeSimplicial(G,S,z) means that for all distinct a,b in S, adjacency of z to a and b implies adjacency of a to b. Nonempty(S) means that S contains an element. EliminatesEveryFiniteSet(G) says that each nonempty finite set contains such a z. LaterIn(G,S,f,v) is exactly the set of u in S with f(v) < f(u) and G.Adj v u.",
        H("Elimination rankings and rooted clique forests"),
        Blocks(
            Describe.Lean(DescribeId.Create("relative-simplicial"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_simplicial_in_finset"),
                H("Simpliciality inside each finite set"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("IsChordal", F.Id("G")), FormulaLogicOperator.Implies, All("S", Call("Finset", F.Id("V")), Logic(Call("Nonempty", F.Id("S")), FormulaLogicOperator.Implies, Some("z", F.Id("V"), Logic(Rel(F.Id("z"), FormulaRelationOperator.MemberOf, F.Id("S")), FormulaLogicOperator.And, Call("RelativeSimplicial", F.Id("G"), F.Id("S"), F.Id("z"))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("Apply Dirac to the induced graph on the finite set. Neither a finite ambient vertex type nor a nonempty ambient type is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("erase-and-shift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_rank_of_simplicial_elimination"),
                H("Erase-and-shift rank construction"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("EliminatesEveryFiniteSet", F.Id("G")), FormulaLogicOperator.Implies, All("n", Call("Nat"), All("S", Call("Finset", F.Id("V")), Logic(Rel(Call("card", F.Id("S")), FormulaRelationOperator.Equal, F.Id("n")), FormulaLogicOperator.Implies, Some("f", new Formula.TypeArrow(F.Id("V"), Call("Nat")), Logic(Call("InjOn", F.Id("f"), F.Id("S")), FormulaLogicOperator.And, All("v", F.Id("V"), Logic(Rel(F.Id("v"), FormulaRelationOperator.MemberOf, F.Id("S")), FormulaLogicOperator.Implies, Call("IsClique", F.Id("G"), Call("LaterIn", F.Id("G"), F.Id("S"), F.Id("f"), F.Id("v"))))))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("At cardinality zero the constant zero function suffices on the empty set. At a successor cardinality, remove a relatively simplicial vertex, rank it zero, and increase every remaining rank by one. The ranking is injective on the chosen set; no bound on its values is part of the conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-chordal-peo"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/EliminationForest.exists_isPEO"),
                H("Perfect elimination of finite chordal graphs"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("Finite", F.Id("V")), FormulaLogicOperator.Implies, Logic(Call("IsChordal", F.Id("G")), FormulaLogicOperator.Implies, Some("ord", new Formula.TypeArrow(F.Id("V"), Call("Nat")), Call("IsPEO", F.Id("G"), F.Id("ord"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("An internal Fintype choice applies the rank construction to the full vertex set. The public hypothesis is Finite only. The clique-forest construction attaches the bag consisting of a vertex and its later neighbors, with the earliest later neighbor as its Option-valued parent. A count of vertices with higher rank decreases toward each root and distinguishes nodes. Local bag inheritance gives the ancestor/intersection property. Multiple roots and an empty vertex type require no additional connector."))),
                DescribeRole.Theorem))));


    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Logic(Formula l, FormulaLogicOperator op, Formula r) =>
        new Formula.Logic(l, op, r);
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) =>
        new Formula.Relation(l, op, r);
}
