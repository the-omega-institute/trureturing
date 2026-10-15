using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class PathRingSplicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/PathRingSplicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual graph pieces with independent full support and real connecting edges splice into one Hamilton cycle with exact vertex and edge inventories.",
        H("Splicing Actual Paths around a Ring"),
        Blocks(
            Paragraph(Text(
                "Let G be a simple graph on a type V with decidable equality. A Piece(G) has a start, "
                + "a finish and an actual G-walk between them. Choose a first piece p and a list ps "
                + "of subsequent pieces. The list is Linked when each piece's finish is adjacent in G "
                + "to the next piece's start. The function finish(p,ps) is the finish of the final piece. "
                + "Write flatMapSupport(p,ps) for the concatenation of all full piece supports. "
                + "The list chainEdges(p,ps) contains all original piece edges, in order, with exactly "
                + "one actual connecting edge inserted between consecutive pieces.")),
            Describe.Lean(DescribeId.Create("chain-edge-cases"),
                DeclarationHandle.Create(Prefix + "chain_edge_cases"),
                H("Every Chain Edge Has an Actual Piece or Consecutive Seam Owner"),
                StatementSource.FromAuthor(EdgeCasesFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every edge in the literal chainEdges list belongs to an actual indexed piece "
                    + "or is the connection between two consecutive actual pieces. Recursive list "
                    + "membership earns the exhaustive classification, including the exact natural "
                    + "index and its successor bound. No support partition, adjacency or equality "
                    + "decision assumption is needed. The full native T/E surgery inventories "
                    + "consume this classification to prove that no additional edges occur."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spliced-hamiltonian-cycle"),
                DeclarationHandle.Create(Prefix + "exists_spliced_hamiltonian_cycle"),
                H("One Actual Hamilton Cycle with Literal Inventories"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the list is Linked, its final finish is adjacent to the first start, "
                        + "every vertex of V occurs exactly once in flatMapSupport(p,ps), and that list "
                        + "has at least three entries. There is an actual Hamilton cycle c based at "
                        + "the first start. Its support with the first entry removed equals the reverse "
                        + "of flatMapSupport(p,ps). Its edge list is the real closing edge followed by "
                        + "the reverse of chainEdges(p,ps). No candidate cycle, endpoint pairing or "
                        + "connectedness hypothesis is assumed.")),
                    Paragraph(Text(
                        "Recursively append each piece, its real connection, and the recursively joined "
                        + "remaining pieces. The vertex at a connection is already the next piece's "
                        + "start, so the full support is exactly the concatenation of the independent "
                        + "piece supports. A second induction preserves the literal edge list. "
                        + "The support counts then make the joined walk Hamiltonian and simple. "
                        + "Reverse it and prepend the supplied closing edge. A closing edge already "
                        + "present in a simple path would force the path to have length one; at least "
                        + "three support entries exclude this. Thus the actual return creates a cycle "
                        + "and its tail contains every vertex exactly once."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a native switching construction, the separate mathematical obligations are to "
                + "obtain the actual pieces, prove their complete independent support partition, and "
                + "verify every specified connection as a real generator edge. This theorem then "
                + "constructs the full cycle without a Hamiltonian search.")))));

    private static Formula EdgeCasesFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), p = F.Id("p"), ps = F.Id("ps");
        Formula e = F.Id("e"), r = F.Id("r"), i = F.Id("i");
        Formula pieces = Call("cons", p, ps), next = Call("add", i, D(1));
        Formula member(Formula x, Formula xs) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, xs);
        Formula piece = Some("r", Call("Piece", g), And(member(r, pieces), member(e, Call("edges", Call("walk", r)))));
        Formula bound = new Formula.Relation(next, FormulaRelationOperator.LessThan, Call("length", pieces));
        Formula seam = Some("i", Call("Nat"), And(bound, Eq(e, Call("Sym2",
            Call("finish", Call("get", pieces, i)), Call("start", Call("get", pieces, next))))));
        Formula conclusion = new Formula.Logic(piece, FormulaLogicOperator.Or, seam);
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", v),
            All("p", Call("Piece", g), All("ps", Call("List", Call("Piece", g)),
                All("e", Call("Sym2Type", v), Implies(member(e, Call("chainEdges", p, ps)), conclusion)))))));
    }

    private static Formula CycleFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), p = F.Id("p"), ps = F.Id("ps");
        Formula full = Call("flatMapSupport", p, ps);
        Formula start = Call("start", p), finish = Call("finish", p, ps), c = F.Id("c");
        Formula counts = All("v", v, Eq(Call("count", F.Id("v"), full), D(1)));
        Formula hypotheses = And(Call("Linked", p, ps),
            And(Call("Adj", g, finish, start), And(counts, Le(D(3), Call("length", full)))));
        Formula closing = Call("Sym2", start, finish);
        Formula conclusion = Some("c", Call("Walk", g, start, start),
            And(Call("IsHamiltonianCycle", c),
                And(Eq(Call("tail", Call("support", c)), Call("reverse", full)),
                    Eq(Call("edges", c),
                        Call("cons", closing, Call("reverse", Call("chainEdges", p, ps)))))));
        return Disp(All("V", Call("Type"), Seq(
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), All("p", Call("Piece", g),
                All("ps", Call("List", Call("Piece", g)), Implies(hypotheses, conclusion)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
