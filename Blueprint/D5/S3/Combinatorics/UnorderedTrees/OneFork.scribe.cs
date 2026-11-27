using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class OneForkDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/OneFork.";
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BodyForSpine(Formula tree, Formula vertex, Formula omitted) =>
        And(
            All("x", F.Id("V"), Le(Call("depth", tree, F.Id("x")), Call("depth", tree, vertex))),
            And(
                new Formula.Not(Mem(omitted, Call("spine", tree, vertex))),
                And(
                    All("x", F.Id("V"), Iff(new Formula.Not(Mem(F.Id("x"), Call("spine", tree, vertex))), Eqn(F.Id("x"), omitted))),
                    And(
                        new Formula.Not(Call("Internal", tree, omitted)),
                        And(Mem(Call("parent", tree, omitted), Call("spine", tree, vertex)),
                            Ne(Call("parent", tree, omitted), vertex))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual finite rooted tree whose size exceeds its vertex-height by one has exactly one leaf outside a deepest root path. The leaf attaches to a nonterminal vertex of that path.",
        H("The one-off-path skeleton"),
        Blocks(
            Node("spine", "The original root path", "spine", SpineFormula(),
                "The spine is the finite set of parent iterates from v through the root, including both endpoints. It is closed under the parent map and has one vertex for each depth level.", DescribeRole.Definition),
            Node("classification", "A unique omitted leaf", "one_off_spine",
                Imp(Eqn(Call("card", F.Id("V")), Seq(Call("height", F.Id("T")), Sp, Plus, Sp, D(1))),
                    Some("v", F.Id("V"), Some("w", F.Id("V"), BodyForSpine(F.Id("T"), F.Id("v"), F.Id("w"))))),
                "When the carrier has one more vertex than the height, a deepest spine leaves a singleton complement. The omitted vertex is a leaf, its parent lies on the spine, and attachment at the deepest endpoint is excluded by maximality.", DescribeRole.Theorem),
            Node("fork", "The canonical fork carrier", "Fork", Eqn(Call("Fork", F.Id("b"), F.Id("c")),
                    Call("Sum", SpineType, F.Id("Bool"))),
                "Fork b c is the sum of the b+c+1 indexed spine vertices and two Boolean-tagged tips.", DescribeRole.Definition),
            Node("fork-point", "The fork point", "forkPoint", Eqn(Seq(Call("forkPoint", F.Id("b"), F.Id("c")), Dot, F.Id("val")), F.Id("b")),
                "The fork point is the spine vertex at index b where the short tip attaches.", DescribeRole.Definition),
            Node("fork-tree", "The canonical fork parent map", "fork", ForkFormula(),
                "The canonical parent map sends each indexed spine vertex to its predecessor and sends the false and true tips to the fork point and terminal spine vertex.", DescribeRole.Definition),
            Node("card-fork", "Cardinality of the fork", "card_fork",
                Eqn(Call("card", Call("Fork", F.Id("b"), F.Id("c"))), Seq(F.Id("b"), Sp, Plus, Sp, F.Id("c"), Sp, Plus, Sp, D(3))),
                "The sum carrier has b+c+1 spine vertices and two tips.", DescribeRole.Theorem),
            Node("height-fork", "Height of the fork", "height_fork",
                Eqn(Call("height", Call("fork", F.Id("b"), F.Id("c"))), Seq(F.Id("b"), Sp, Plus, Sp, F.Id("c"), Sp, Plus, Sp, D(2))),
                "The long tip attains the maximum depth b+c+1, so the vertex-height is b+c+2.", DescribeRole.Theorem),
            Node("canonical", "The canonical fork", "exists_fork_iso",
                Imp(Eqn(Call("card", F.Id("V")), Seq(Call("height", F.Id("T")), Sp, Plus, Sp, D(1))),
                    Some("b", Nat, Some("c", Nat, Call("Nonempty", Call("Iso", Call("fork", F.Id("b"), F.Id("c")), F.Id("T")))))),
                "A deepest spine, its omitted leaf and the parent edges give a bidirectional labelling by the canonical fork.", DescribeRole.Theorem),
            Node("fork-internal-spine", "Internal indexed spine vertices", "fork_internal_spine",
                All("i", SpineType, Call("Internal", ForkTree, Call("inl", F.Id("i")))),
                "Every indexed spine vertex has a child, with the terminal position supplied by the long tip.", DescribeRole.Theorem),
            Node("fork-terminal", "The fork tips are terminal", "fork_terminal",
                All("p", F.Id("Bool"), new Formula.Not(Call("Internal", ForkTree, Call("inr", F.Id("p"))))),
                "The Boolean tips have no nonroot children in the canonical parent map.", DescribeRole.Theorem),
            Node("iso-parameters", "Fork parameters are invariant", "fork_iso_parameters",
                IsoParameters(),
                "An isomorphism between canonical forks identifies the unique branching depth b and then the maximum-depth excess c.", DescribeRole.Theorem),
            Node("iso-spine", "Fork isomorphisms fix the spine", "fork_iso_spine",
                BindIso(ForkTree, All("i", SpineType,
                    Eqn(Image(Call("inl", F.Id("i"))), Call("inl", F.Id("i"))))),
                "Depth and internality uniquely identify each indexed nonterminal.", DescribeRole.Theorem),
            Node("iso-tips", "Fork isomorphisms permute the tips", "fork_iso_tips",
                TipsFormula(),
                "The two tips are the only terminal vertices outside the spine. Their depths distinguish them when c is positive, while c=0 permits the swap.", DescribeRole.Theorem),
            Node("swap", "The equal-arm tip swap", "swapTips", Seq(Call("swapTips", F.Id("b")), Colon, Sp,
                    Call("Iso", Call("fork", F.Id("b"), D(0)), Call("fork", F.Id("b"), D(0)))),
                "When c=0, exchanging the two Boolean tips is a rooted parent-map isomorphism.", DescribeRole.Definition))));

    private static Formula SpineType => Call("Fin", Seq(F.Id("b"), Plus, F.Id("c"), Plus, D(1)));
    private static Formula ForkTree => Call("fork", F.Id("b"), F.Id("c"));
    private static Formula Image(Formula vertex) =>
        new Formula.Apply(Seq(F.Id("e"), Dot, F.Id("equiv")), [vertex]);
    private static Formula BindIso(Formula target, Formula body) =>
        Seq(Forall, Sp, F.Id("e"), Colon, Sp, Call("Iso", ForkTree, target), Comma, Sp,
            Parenthesized(body));

    private static Formula SpineFormula()
    {
        var t = F.Id("T");
        var v = F.Id("v");
        var k = F.Id("k");
        var depth = Call("depth", t, v);
        return Eqn(Call("spine", t, v), new Formula.SetBuilder(
            Call("iterate", Call("parent", t), k, v), k, Call("range", Seq(depth, Plus, D(1)))));
    }

    private static Formula ForkFormula()
    {
        var i = F.Id("i");
        var b = F.Id("b");
        var c = F.Id("c");
        var predecessor = Seq(Langle, Sp, i, Dot, F.Id("val"), Minus, D(1), Rangle);
        return new Formula.Aligned([
            Seq(Amp, Eqn(Call("root", ForkTree), Call("inl", D(0)))),
            Seq(Amp, All("i", SpineType, Eqn(Call("parent", ForkTree, Call("inl", i)), Call("inl", predecessor)))),
            Seq(Amp, Eqn(Call("parent", ForkTree, Call("inr", F.Id("false"))), Call("inl", Call("forkPoint", b, c)))),
            Seq(Amp, Eqn(Call("parent", ForkTree, Call("inr", F.Id("true"))), Call("inl", Seq(Langle, Sp, b, Plus, c, Rangle))))
        ]);
    }

    private static Formula IsoParameters()
    {
        var bp = Seq(F.Id("b"), Apos);
        var cp = Seq(F.Id("c"), Apos);
        return BindIso(Call("fork", bp, cp), And(Eqn(F.Id("b"), bp), Eqn(F.Id("c"), cp)));
    }

    private static Formula TipsFormula()
    {
        var shortTip = Call("inr", F.Id("false"));
        var longTip = Call("inr", F.Id("true"));
        var fixedTips = And(Eqn(Image(shortTip), shortTip), Eqn(Image(longTip), longTip));
        var swappedTips = And(Eqn(F.Id("c"), D(0)),
            And(Eqn(Image(shortTip), longTip), Eqn(Image(longTip), shortTip)));
        return BindIso(ForkTree, new Formula.Logic(Parenthesized(fixedTips),
            FormulaLogicOperator.Or, Parenthesized(swappedTips)));
    }

    private static Formula Parameter(string name, Formula type) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Finite(Formula carrier) =>
        Seq(OpenBracket, Call("Fintype", carrier), CloseBracket);
    private static Formula For(Formula body, params Formula[] parameters) =>
        Seq(Forall, Sp, Seq(parameters.Select(parameter => Seq(parameter, Sp)).ToArray()), Comma, Sp,
            Parenthesized(body));

    private static Formula Scope(string name, Formula body)
    {
        var v = F.Id("V");
        var b = Parameter("b", Nat);
        var c = Parameter("c", Nat);
        var tree = Parameter("T", Call("Tree", v));
        return name switch
        {
            "spine" => For(body, Parameter("V", F.Id("Type")), tree, Parameter("v", v)),
            "one_off_spine" or "exists_fork_iso" => For(body, Parameter("V", F.Id("Type")), Finite(v), tree),
            "swapTips" => For(body, b),
            "fork_iso_parameters" => For(body, b, c,
                Parameter("b", Nat, Apos), Parameter("c", Nat, Apos)),
            _ => For(body, b, c)
        };
    }

    private static Formula Parameter(string name, Formula type, Formula modifier) =>
        Parenthesized(Seq(F.Id(name), modifier, Colon, Sp, type));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("one-fork-" + id), DeclarationHandle.Create(Owner + declaration), H(title),
        StatementSource.FromAuthor(Disp(Scope(declaration, formula))), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
}
