using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ErdosGrahamOrderGadgetDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ErdosGrahamOrderGadget.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/kasel2026erdos197");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every order gadget on the integers from M plus one through twice M fails once M is "
            + "at least sixteen: arithmetic-progression constraints propagate two neighbouring "
            + "centres around ladders whose guard endpoints force both possible rank orders.",
        H("The Erdos-Graham Order Gadget Is Impossible at Every Scale"),
        Blocks(
            Node("dyadic-block", "The dyadic block", "block", BlockFormula(),
                "For each natural M, the block consists of exactly the natural numbers from "
                    + "M plus one through twice M, with both endpoints included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("progression-free-rank", "No monotone three-term progression", "APFree",
                APFreeFormula(),
                "A ranking is progression-free when no increasing three-term arithmetic "
                    + "progression inside the block has ranks increasing from left to right or "
                    + "increasing from right to left.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("guard-inequalities", "The guard inequalities", "Guards", GuardsFormula(),
                "For each of fifteen and sixteen, every index from one through half that value "
                    + "places the corresponding top, twice M plus twice the index minus the "
                    + "value, before the bottom M plus the index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("order-gadget", "Feasibility of the order gadget", "OrderGadget",
                OrderGadgetFormula(),
                "An order gadget at scale M is a natural-valued ranking that is injective on the "
                    + "block and obeys both the progression-free condition and all guard "
                    + "inequalities.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("all-scales-claim", "Impossibility from scale sixteen", "claim",
                ClaimFormula(),
                "The assertion says that no order gadget exists for any natural scale M at "
                    + "least sixteen.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("all-scales-result", "The order gadget is impossible", "result",
                ResultFormula(),
                "Split once on the rank order of two adjacent block elements; this determines "
                    + "which parity leads on the difference-one ladder. In each branch choose "
                    + "two centres c and c plus two just below three M over two. Two floods on "
                    + "the relevant parity class carry c and c plus two before a guard top, and "
                    + "the guards carry them before the corresponding bottoms. Two further "
                    + "floods on classes modulo four then give c before c plus two and c plus "
                    + "two before c. For even M the four guards are (15,2), (15,4), (16,1), and "
                    + "(16,3); for odd M they are (15,1), (15,3), (16,2), and (16,4). The "
                    + "phase-independent flood applies to even as well as odd classes modulo "
                    + "four, so both initial rank orders end in the same contradiction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("erdos-197-order-gadget-all-residues"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula BlockFormula()
    {
        var m = F.Id("M");
        var n = F.Id("n");
        var interval = Seq(
            OpenBrace, n, Sp, InMacro, Sp, Naturals(), Sp, Bar, Sp,
            new Formula.RelationChain(
                FormulaRelationOperator.LessThanOrEqual,
                [Add(m, D(1)), n, Multiply(D(2), m)]),
            CloseBrace);
        return Disp(ForAll("M", Naturals(), Equal(Call("block", m), interval)));
    }

    private static Formula APFreeFormula()
    {
        var m = F.Id("M");
        var rank = F.Id("rank");
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var premise = And(
            Member(a, Call("block", m)),
            Member(b, Call("block", m)),
            Member(c, Call("block", m)),
            Less(a, b),
            Less(b, c),
            Equal(Add(a, c), Multiply(D(2), b)));
        var conclusion = And(
            new Formula.Not(Parenthesized(new Formula.RelationChain(
                FormulaRelationOperator.LessThan,
                [Call("rank", a), Call("rank", b), Call("rank", c)]))),
            new Formula.Not(Parenthesized(new Formula.RelationChain(
                FormulaRelationOperator.LessThan,
                [Call("rank", c), Call("rank", b), Call("rank", a)]))));
        var body = ForAllMany(
            [Bound("a", Naturals()), Bound("b", Naturals()), Bound("c", Naturals())],
            Implies(premise, conclusion));
        return Disp(ForAllMany(
            [Bound("M", Naturals()), Bound("rank", RankType())],
            Iff(Call("APFree", m, rank), body)));
    }

    private static Formula GuardsFormula()
    {
        var m = F.Id("M");
        var rank = F.Id("rank");
        var x = F.Id("x");
        var j = F.Id("j");
        var premise = And(
            LessThanOrEqual(D(1), j),
            LessThanOrEqual(j, new Formula.Floor(new Formula.Fraction(x, D(2)))));
        var top = Subtract(
            Add(Multiply(D(2), m), Multiply(D(2), j)),
            x);
        var bottom = Add(m, j);
        var body = ForAll(
            "x",
            new Formula.SetLiteral([D(1, 5), D(1, 6)]),
            ForAll("j", Naturals(),
                Implies(premise, Less(Call("rank", top), Call("rank", bottom)))));
        return Disp(ForAllMany(
            [Bound("M", Naturals()), Bound("rank", RankType())],
            Iff(Call("Guards", m, rank), body)));
    }

    private static Formula OrderGadgetFormula()
    {
        var m = F.Id("M");
        var rank = F.Id("rank");
        var a = F.Id("a");
        var b = F.Id("b");
        var injective = ForAllMany(
            [Bound("a", Call("block", m)), Bound("b", Call("block", m))],
            Implies(Equal(Call("rank", a), Call("rank", b)), Equal(a, b)));
        var conditions = And(
            injective,
            Call("APFree", m, rank),
            Call("Guards", m, rank));
        var existence = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("rank"),
            RankType(),
            conditions);
        return Disp(ForAll(
            "M", Naturals(), Iff(Call("OrderGadget", m), existence)));
    }

    private static Formula ClaimFormula()
    {
        var m = F.Id("M");
        var statement = ForAll(
            "M",
            Naturals(),
            Implies(
                LessThanOrEqual(D(1, 6), m),
                new Formula.Not(Call("OrderGadget", m))));
        return Disp(Iff(F.Id("claim"), statement));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula RankType() =>
        new Formula.TypeArrow(Naturals(), Naturals());

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula ForAllMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
