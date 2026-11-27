using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class ForkDecorationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/ForkDecoration.";
    private static Formula B => F.Id("b");
    private static Formula C => F.Id("c");
    private static Formula I => F.Id("i");
    private static Formula N => F.Id("n");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("T");
    private static Formula Datum => F.Id("d");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula SpineLength => Seq(B, Plus, C, Plus, D(1));
    private static Formula SpineIndex => Call("Fin", SpineLength);
    private static Formula Short => Field(R, "short");
    private static Formula Long => Field(R, "long");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized fork decorations correspond bijectively to the actual qualifying rooted-tree classes.",
        H("Unordered fork decorations"),
        Blocks(
            Node("counts", "Counts", "Normalized leaf offsets", CountsFormula(),
                "The spine multiplicities are unrestricted naturals. Each tip has one mandatory leaf beyond its offset, and equal arms require the short offset to be at most the long offset.", DescribeRole.Definition),
            Node("data", "Data", "Data over both fork parameters",
                Equal(Call("Data"), Seq(Sigma, Sp, B, Colon, Sp, Nat, Comma, Sp,
                    Sigma, Sp, C, Colon, Sp, Nat, Comma, Sp, Call("Counts", B, C))),
                "The dependent sum includes the fork parameters and their corresponding multiplicity data.", DescribeRole.Definition),
            Node("weight", "weight", "Total size of the inflated fork",
                Equal(Call("weight", Seq(Langle, Sp, B, Comma, Sp, C, Comma, Sp, R, Rangle)),
                    Seq(B, Plus, C, Plus, D(5), Plus,
                        new Formula.Subscript(Sum, new Formula.Relation(I, FormulaRelationOperator.MemberOf, SpineIndex)),
                        Sp, Apply(Field(R, "spine"), I), Plus, Short, Plus, Long)),
                "The constant term in the size accounts for the two tips, two mandatory tip leaves and the extra spine vertex.", DescribeRole.Definition),
            Node("weighted", "Weighted", "Decorations of prescribed size",
                Equal(Call("Weighted", N), Subtype(Datum, Call("Data"), Equal(Call("weight", Datum), N))),
                "The subtype consists of the decorations with total size n.", DescribeRole.Definition),
            Node("qualifying", "Qualifying", "Actual qualifying tree classes",
                Equal(Call("Qualifying", N), Subtype(T, Call("TreeClass", N),
                    Equal(Call("classHeight", T), Call("classInternalCount", T)))),
                "The subtype uses the quotient of actual parent data on Fin n and tests equality of the two class observables.", DescribeRole.Definition),
            Node("leaves", "Counts.leaves", "Leaf counts on the spine and tips", LeavesFormula(),
                "The two tips use their offsets plus one. On every spine vertex the multiplicity is the corresponding spine coordinate.", DescribeRole.Definition),
            Node("classification", "classification", "A bijection at each total size",
                HasType(Call("classification", N), new Formula.Relation(
                    Call("Weighted", N), FormulaRelationOperator.Equivalent, Call("Qualifying", N))),
                "Inflation followed by labelling the complete carrier gives the forward map. Pruning recovers the canonical fork and reads the leaf multiplicities. Fork depth and maximum depth determine b and c. The spine is fixed by automorphisms, and sorting removes the tip-swap ambiguity at c=0, including equal tip counts.", DescribeRole.Definition),
            Node("card", "card_weighted", "The decoration count equals the actual tree count",
                Equal(Apply(Field(F.Id("Nat"), "card"), Call("Weighted", N)), Call("a", N)),
                "Cardinality is preserved by the size-matched classification.", DescribeRole.Theorem))));

    private static Formula CountsFormula() => Equal(Call("Counts", B, C),
        Subtype(Seq(Langle, Sp, F.Id("spine"), Comma, Sp, F.Id("short"), Comma, Sp, F.Id("long"), Rangle),
            Seq(Parenthesized(new Formula.TypeArrow(SpineIndex, Nat)), Sp, Times, Sp, Nat, Sp, Times, Sp, Nat),
            new Formula.Logic(Equal(C, D(0)), FormulaLogicOperator.Implies,
                new Formula.Relation(F.Id("short"), FormulaRelationOperator.LessThanOrEqual, F.Id("long")))));

    private static Formula LeavesFormula() => new Formula.Aligned([
        Seq(Amp, Equal(Apply(Field(R, "leaves"), Call("inl", I)), Apply(Field(R, "spine"), I))),
        Seq(Amp, Equal(Apply(Field(R, "leaves"), Call("inr", F.Id("false"))), Seq(Short, Plus, D(1)))),
        Seq(Amp, Equal(Apply(Field(R, "leaves"), Call("inr", F.Id("true"))), Seq(Long, Plus, D(1))))
    ]);

    private static Formula Subtype(Formula value, Formula type, Formula condition) =>
        Seq(OpenBrace, HasType(value, type), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula HasType(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Field(Formula owner, string name) => Seq(owner, Dot, Grp(F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);


    private static Formula Scope(string name, Formula body)
    {
        var b = Parenthesized(HasType(B, Nat));
        var c = Parenthesized(HasType(C, Nat));
        var r = Parenthesized(HasType(R, Call("Counts", B, C)));
        return name switch
        {
            "Data" => body,
            "Counts" => Seq(Forall, Sp, b, Sp, c, Comma, Sp, Parenthesized(body)),
            "weight" or "Counts.leaves" => Seq(Forall, Sp, b, Sp, c, Sp, r, Comma, Sp,
                Parenthesized(name == "Counts.leaves"
                    ? Seq(Forall, Sp, Parenthesized(HasType(I, SpineIndex)), Comma, Sp, Parenthesized(body))
                    : body)),
            _ => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), Nat, Parenthesized(body))
        };
    }

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fork-decoration-" + id), DeclarationHandle.Create(Owner + name.Split('.')[^1]),
            H(title), StatementSource.FromAuthor(Disp(Scope(name, formula))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
