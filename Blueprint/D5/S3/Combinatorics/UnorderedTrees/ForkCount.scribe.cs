using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ForkCountDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/ForkCount.";
    private static Formula N => F.Id("n");
    private static Formula B => F.Id("b");
    private static Formula C => F.Id("c");
    private static Formula M => F.Id("m");
    private static Formula Base => F.Id("base");
    private static Formula K => F.Id("k");
    private static Formula I => F.Id("i");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bound => Call("Fin", Seq(N, Plus, D(1)));
    private static Formula Bv => Seq(B, Dot, F.Id("val"));
    private static Formula Cv => Seq(C, Dot, F.Id("val"));
    private static Formula Mv => Seq(M, Dot, F.Id("val"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two bounded binomial sums give the actual unordered rooted-tree count.",
        H("Counting normalized fork decorations"),
        Blocks(
            Node("slots", "Slots", "Weak compositions with a base weight",
                Equal(Call("Slots", N, Base, K),
                    Subtype(F.Id("f"), new Formula.TypeArrow(Call("Fin", K), Nat),
                        Equal(Seq(Base, Plus, new Formula.Subscript(Sum, Member(I, Call("Fin", K))),
                            Sp, Call("f", I)), N))),
                "Every slot contributes a nonnegative leaf count to the prescribed total weight.", DescribeRole.Definition),
            Node("equal", "Equal", "Equal-arm slots",
                Equal(Call("Equal", N), SigmaOver(B, Bound, SigmaOver(M, Bound,
                    Call("Slots", N, Seq(Bv, Plus, D(5), Plus, D(2), Mv), Seq(Bv, Plus, D(2)))))),
                "The b+1 spine multiplicities and the difference of the two tip offsets are the b+2 slots. The smaller tip offset m contributes twice to the base weight.", DescribeRole.Definition),
            Node("unequal", "Unequal", "Unequal-arm slots",
                Equal(Call("Unequal", N), SigmaOver(B, Bound, SigmaOver(C, Bound,
                    Subtype(F.Id("f"), Call("Slots", N, Seq(Bv, Plus, Cv, Plus, D(5)),
                        Seq(Bv, Plus, Cv, Plus, D(3))),
                        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Cv))))),
                "A positive c separates the arms. Both offsets contribute independently together with the b+c+1 spine multiplicities.", DescribeRole.Definition),
            Node("split", "weightSplit", "The two decoration families",
                Seq(Call("weightSplit", N), Colon, Sp, new Formula.Relation(
                    Call("Weighted", N), FormulaRelationOperator.Equivalent,
                    Call("Sum", Call("Equal", N), Call("Unequal", N)))),
                "For c=0 the two sorted tip offsets have the unique form (m,m+d), including d=0. For c>0 the two offsets are stored as separate slots. Decoding restores the original normalized decoration and its weight.", DescribeRole.Definition),
            Node("count-by-arms", "count_by_arms", "The equal-arm and unequal-arm contributions",
                CountFormula(),
                "All sum indices are natural numbers. The equal-arm summand uses the b+2 slots after subtracting the base weight. For unequal arms put u=b+c. There are u decompositions with c positive and u+3 free slots. The Lean sum uses v=u−1, and the displayed reindexing covers precisely the same feasible values, including empty ranges.", DescribeRole.Theorem))));

    private static Formula CountFormula()
    {
        var u = F.Id("u");
        var feasible = new Formula.Relation(Seq(B, Plus, D(5), Plus, D(2), M),
            FormulaRelationOperator.LessThanOrEqual, N);
        var equal = new Formula.Subscript(Sum, Seq(B, Comma, M, Sp, Colon, Sp, Nat, Sp, Mid, Sp, feasible));
        var unequal = new Formula.Subscript(Sum, new Formula.RelationChain(
            FormulaRelationOperator.LessThanOrEqual, [D(1), u, Seq(N, Minus, D(5))]));
        var total = Seq(equal, Sp, Call("choose", Seq(N, Minus, D(4), Minus, D(2), M), Seq(B, Plus, D(1))),
            Sp, Plus, Sp, unequal, Sp, u, Sp, Call("choose", Seq(N, Minus, D(3)), Seq(u, Plus, D(2))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Nat,
            Equal(Call("a", N), total));
    }

    private static Formula Subtype(Formula value, Formula type, Formula condition) =>
        Seq(OpenBrace, value, Colon, Sp, type, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula SigmaOver(Formula variable, Formula type, Formula body) =>
        Seq(Sigma, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);


    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Scope(string name, Formula body) => name switch
    {
        "Slots" => new Formula.BindMany(FormulaQuantifier.ForAll, [
            new(FormulaIdentifier.Create("n"), Nat),
            new(FormulaIdentifier.Create("base"), Nat),
            new(FormulaIdentifier.Create("k"), Nat)], Parenthesized(body)),
        "count_by_arms" => body,
        _ => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Nat, Parenthesized(body))
    };

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fork-count-" + id), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(Scope(name, formula))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
