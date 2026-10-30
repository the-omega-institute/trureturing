using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class WeightedCycleWalkDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Even-Cycle Traversals",
        H("Actual Even-Cycle Traversals"), Blocks(
            Paragraph(Text("The graph evenCycleGraph(n) is identified with the usual cycleGraph(2(n+2)) by L(i)->2i+1 and R(i)->2i. The inverse uses parity and integer division. Both directions of adjacency, including the wrap edge, follow from the actual finite cyclic arithmetic. Its circuit begins at L(0) and traverses L(i), R(i+1), L(i+1) in cyclic order. These are actual graph walks, not supplied lists of independent edge weights.")),
            Describe.Lean(DescribeId.Create("circuit-length"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_length"),
                H("Length of the actual circuit"), StatementSource.FromAuthor(CircuitLengthFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The recursively constructed walk adds exactly two edges for each of n+2 indices; endpoint reduction closes it at L(0). Its length is 2(n+2)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circuit-is-cycle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_isCycle"),
                H("The traversal is a simple cycle"), StatementSource.FromAuthor(CircuitIsCycleFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("After deleting its initial vertex, the support contains R(i+1),L(i+1) once for each cyclic index. Successor is a permutation, so this list has no repeated vertices. The length is at least four; the path-tail criterion proves IsCycle."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circuit-alpha"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_alpha"),
                H("Alternating product and actual matchings"), StatementSource.FromAuthor(CircuitAlphaFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any commutative group and any symmetric edge-weight function w, the existing public WeightedVertexProducts.alpha on this actual circuit equals the product over the actual successor matching divided by the product over the actual paired matching. The proof unfolds the public alpha definition, applies the pinned list alternating-product append identity inside the induction, and reindexes the second edge family by the successor permutation. It does not assume a product bridge."))),
                DescribeRole.Theorem))));

    private static Formula CircuitLengthFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", Nat(), Eq(Call("length", Call("circuit", n)), Mul(D(2), Add(n, D(2))))));
    }

    private static Formula CircuitIsCycleFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", Nat(), Call("IsCycle", Call("circuit", n))));
    }

    private static Formula CircuitAlphaFormula()
    {
        Formula a = F.Id("A"), n = F.Id("n"), w = F.Id("w");
        Formula index = Fin(Add(n, D(2)));
        Formula vertex = Sum(Fin(Add(n, D(2))), Fin(Add(n, D(2))));
        Formula edge = Call("Sym2", vertex);
        Formula weight = Arrow(edge, a);
        Formula i = F.Id("i");
        Formula successor = ProductOver(i, index,
            Call("w", Call("s", Inl(i), Inr(Call("finRotate", Add(n, D(2)), i)))));
        Formula paired = ProductOver(i, index, Call("w", Call("s", Inl(i), Inr(i))));
        Formula conclusion = Eq(Call("alpha", w, Call("circuit", n)), Div(successor, paired));
        return Disp(All("A", F.Id("Type"),
            Seq(Instance("CommGroup", a), All("n", Nat(), All("w", weight, conclusion)))));
    }

    private static Formula ProductOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(variable, Sp, InMacro, Sp, type)), Sp, body);

    private static Formula Inl(Formula value) => Qualified("Sum", "inl", value);
    private static Formula Inr(Formula value) => Qualified("Sum", "inr", value);
    private static Formula Qualified(string owner, string name, params Formula[] args)
    {
        Formula head = Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Sum(Formula left, Formula right) => Call("Sum", left, right);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => Call("Nat");
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
}
