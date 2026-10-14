using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class OrderedTwoCutSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/OrderedTwoCutSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two ordered edges of an actual path determine three actual paths with specified endpoints, preserving the entire original vertex list and exactly all uncut edges.",
        H("Three Actual Path Pieces from Two Ordered Cuts"),
        Blocks(
            Paragraph(Text(
                "Let G be a simple graph on V with decidable equality. Let p be an actual path from "
                + "a to b. Its undirected edge at position i is the Sym2 pair of getVert(p,i) and "
                + "getVert(p,i+1). List append below preserves the literal traversal order. "
                + "The operator filterOutTwo(p,e0,e1) is p.edges filtered by the predicate that its "
                + "edge differs from both e0 and e1. NatSub denotes truncated natural subtraction.")),
            Describe.Lean(DescribeId.Create("two-ordered-actual-edge-cuts"),
                DeclarationHandle.Create(Prefix + "exists_path_slicing_at_two_ordered_edges"),
                H("Ordered Endpoints, Full Support, and Exact Uncut Edge List"),
                StatementSource.FromAuthor(OrderedFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume i<j<length(p), with getVert(p,i)=l0, getVert(p,i+1)=r0, "
                        + "getVert(p,j)=l1, and getVert(p,j+1)=r1. Then there are actual paths "
                        + "q0:a to l0, q1:r0 to l1, and q2:r1 to b. Their full support lists "
                        + "concatenate to p.support. The original edge list is exactly "
                        + "q0.edges ++ [Sym2(l0,r0)] ++ q1.edges ++ [Sym2(l1,r1)] ++ q2.edges. "
                        + "Deleting the two cut edges therefore leaves exactly q0.edges ++ q1.edges "
                        + "++ q2.edges, still in its original order. The three lengths are i, "
                        + "j-i-1, and length(p)-j-1.")),
                    Paragraph(Text(
                        "The first piece is take(p,i), the middle is take(drop(p,i+1),j-(i+1)), "
                        + "and the last is drop(p,j+1), with endpoint equalities used only to retype "
                        + "these same walks. The take/drop support identities prove complete vertex "
                        + "preservation directly, rather than inferring it from a length count. The "
                        + "original path has no repeated undirected edges, so neither cut can also "
                        + "occur in any retained piece; this proves the exact filtered-edge identity.")),
                    Paragraph(Text(
                        "Adjacent cuts are allowed. When j=i+1 the middle piece is a genuine nil "
                        + "walk with its common vertex retained. A first or last cut can likewise "
                        + "leave a nil outer piece. No positivity assumption discards these cases."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a recursive prefix-reversal construction, the consumer must supply the actual "
                + "path, prove the order of the two actual edge positions, and identify their oriented "
                + "endpoints. This theorem then gives the three actual pieces and their complete "
                + "inventories. It does not establish those native endpoint identities or their order.")))));

    private static Formula OrderedFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), p = F.Id("p"), i = F.Id("i"), j = F.Id("j");
        Formula a = F.Id("a"), b = F.Id("b"), l0 = F.Id("l0"), r0 = F.Id("r0");
        Formula l1 = F.Id("l1"), r1 = F.Id("r1");
        Formula q0 = F.Id("q0"), q1 = F.Id("q1"), q2 = F.Id("q2");
        Formula e0 = Call("Sym2", l0, r0), e1 = Call("Sym2", l1, r1);
        Formula premises = And(Call("IsPath", p),
            And(Lt(i, j), And(Lt(j, Call("length", p)),
                And(Equal(Call("getVert", p, i), l0),
                    And(Equal(Call("getVert", p, Add(i, D(1))), r0),
                        And(Equal(Call("getVert", p, j), l1),
                            Equal(Call("getVert", p, Add(j, D(1))), r1)))))));
        Formula fullSupport = Equal(Append(Call("support", q0), Call("support", q1), Call("support", q2)),
            Call("support", p));
        Formula originalEdges = Equal(Append(Call("edges", q0), Call("singleton", e0),
            Call("edges", q1), Call("singleton", e1), Call("edges", q2)), Call("edges", p));
        Formula retainedEdges = Equal(Append(Call("edges", q0), Call("edges", q1), Call("edges", q2)),
            Call("filterOutTwo", p, e0, e1));
        Formula lengths = And(Equal(Call("length", q0), i),
            And(Equal(Call("length", q1), Sub(Sub(j, i), D(1))),
                Equal(Call("length", q2), Sub(Sub(Call("length", p), j), D(1)))));
        Formula conclusion = Some("q0", Call("Walk", g, a, l0),
            Some("q1", Call("Walk", g, r0, l1), Some("q2", Call("Walk", g, r1, b),
                And(Call("IsPath", q0), And(Call("IsPath", q1), And(Call("IsPath", q2),
                    And(fullSupport, And(originalEdges, And(retainedEdges, lengths)))))))));
        Formula body = All("p", Call("Walk", g, a, b),
            All("i", Call("Nat"), All("j", Call("Nat"), Implies(premises, conclusion))));
        foreach (string name in new[] { "r1", "l1", "r0", "l0", "b", "a" })
            body = All(name, v, body);
        return Disp(All("V", Call("Type"), Seq(OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), body))));
    }

    private static Formula Append(params Formula[] lists)
    {
        Formula result = lists[^1];
        for (int n = lists.Length - 2; n >= 0; --n)
            result = Call("append", lists[n], result);
        return result;
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => Call("NatSub", left, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
