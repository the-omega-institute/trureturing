using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class DiracDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The vertex type may lie in any universe u. IsChordal means that every cycle of length at least four has an adjacency between two supported vertices whose unordered edge is absent from that cycle. IsSimplicial means that the entire neighbor set is a clique.",
        H("Chordal graphs and simplicial vertices"),
        Blocks(
            Describe.Lean(DescribeId.Create("induced-heredity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Dirac.induce"),
                H("Induced-subgraph heredity"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("IsChordal", F.Id("G")), FormulaLogicOperator.Implies, All("W", Call("Set", F.Id("V")), Call("IsChordal", Call("induce", F.Id("G"), F.Id("W"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("Pulling a cycle through the subtype embedding preserves its cycle property and support and transfers a chord back to the induced graph. No finiteness hypothesis is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dirac-simplicial"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/Dirac.exists_isSimplicial"),
                H("Dirac simplicial-vertex theorem"),
                StatementSource.FromAuthor(Disp(All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), Logic(Call("Finite", F.Id("V")), FormulaLogicOperator.Implies, Logic(Call("Nonempty", F.Id("V")), FormulaLogicOperator.Implies, Logic(Call("IsChordal", F.Id("G")), FormulaLogicOperator.Implies, Some("v", F.Id("V"), Call("IsSimplicial", F.Id("G"), F.Id("v")))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text("A nonempty finite chordal graph has a simplicial vertex. The cardinal induction handles complete graphs, a proper connected component in the disconnected case, and a minimal separator in the remaining case. Minimal separators are cliques because two internally disjoint induced paths would otherwise form a chordless cycle. The result uses classical existence and gives no running-time bound."))),
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
}
