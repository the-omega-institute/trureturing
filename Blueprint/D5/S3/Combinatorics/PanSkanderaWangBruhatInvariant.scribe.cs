using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class PanSkanderaWangBruhatInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pan2026permanental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selection positions and their invariance under reverse-complementation and matched insertion.",
        H("Pan-Skandera-Wang Selection Invariant"),
        Blocks(
            Node("selection-positions", "Selection positions", "selectionPositions",
                SelectionPositionsFormula(),
                "The selected zero-based positions consist of an initial interval followed by every other position in a window of width twice d.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("selection", "Selected entries", "selection", SelectionFormula(),
                "The selection is the list of entries at the selected positions, with zero used outside the word.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("count-ge", "Threshold count", "countGE", CountGEFormula(),
                "The threshold count records how many entries in a word are at least q.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("selection-invariant", "Selection invariant", "SelectionInvariant",
                SelectionInvariantFormula(),
                "The invariant compares threshold counts in the first p source entries with every legal selection of the target word.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("ru-is-perm", "Reverse-complement preserves permutations", "ru_isPerm",
                RuIsPermFormula(),
                "Reverse-complementation sends every permutation of the interval from one through n to another permutation of that interval.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("selection-invariant-ru", "Reverse-complement preserves the invariant", "selectionInvariant_ru",
                SelectionInvariantRuFormula(),
                "The selection invariant is unchanged when both words are reverse-complemented.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("insert-max", "Ordinary maximum insertion", "insertMax", InsertMaxFormula(),
                "Ordinary insertion places the new maximum n at the one-based position r.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("selection-invariant-insert", "Matched insertion preserves the invariant", "selectionInvariant_insert",
                SelectionInvariantInsertFormula(),
                "Matched ordinary insertion and suffix-swapping insertion preserve the full selection invariant under the stated parity and position conditions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula SelectionPositionsFormula() => Disp(ForAllMany(
        [Bound("p", Naturals()), Bound("d", Naturals())],
        Equal(Call("selectionPositions", P(), DVar()),
            Call("append", Call("range", Subtract(P(), DVar())),
                Call("map", Seq(Lambda, Sp, F.Id("k"), Sp, Mapsto, Sp,
                    Add(Add(Subtract(P(), DVar()), Multiply(D(2), F.Id("k"))), D(1))),
                    Call("range", DVar()))))));

    private static Formula SelectionFormula() => Disp(ForAllMany(
        [Bound("x", ListType()), Bound("p", Naturals()), Bound("d", Naturals())],
        Equal(Call("selection", F.Id("x"), P(), DVar()),
            Call("map", Seq(Lambda, Sp, F.Id("i"), Sp, Mapsto, Sp,
                    Call("getD", F.Id("x"), F.Id("i"), D(0))),
                Call("selectionPositions", P(), DVar())))));

    private static Formula CountGEFormula() => Disp(ForAllMany(
        [Bound("q", Naturals()), Bound("x", ListType())],
        Equal(Call("countGE", Q(), F.Id("x")),
            Call("countP", F.Id("x"), Seq(Lambda, Sp, F.Id("v"), Sp, Mapsto, Sp,
                LessEqual(Q(), F.Id("v")))))));

    private static Formula SelectionInvariantFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("x", ListType()), Bound("y", ListType())],
        Iff(Call("SelectionInvariant", N(), F.Id("x"), F.Id("y")),
            ForAllMany(
                [Bound("p", Naturals()), Bound("d", Naturals()), Bound("q", Naturals())],
                Implies(And(LessEqual(P(), N()), LessEqual(DVar(), P()),
                        LessEqual(DVar(), Subtract(N(), P())), LessEqual(D(1), Q()),
                        LessEqual(Q(), Add(N(), D(1)))),
                    LessEqual(Call("countGE", Q(), Call("take", F.Id("x"), P())),
                        Call("countGE", Q(), Call("selection", F.Id("y"), P(), DVar()))))))));

    private static Formula RuIsPermFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("x", ListType())],
        Implies(Call("IsPerm", N(), F.Id("x")),
            Call("IsPerm", N(), Call("RU", N(), F.Id("x"))))));

    private static Formula SelectionInvariantRuFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("x", ListType()), Bound("y", ListType())],
        Implies(And(Call("IsPerm", N(), F.Id("x")), Call("IsPerm", N(), F.Id("y")),
                Call("SelectionInvariant", N(), F.Id("x"), F.Id("y"))),
            Call("SelectionInvariant", N(), Call("RU", N(), F.Id("x")),
                Call("RU", N(), F.Id("y"))))));

    private static Formula InsertMaxFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("r", Naturals()), Bound("a", ListType())],
        Equal(Call("insertMax", N(), F.Id("r"), F.Id("a")),
            Call("append", Call("take", F.Id("a"), Subtract(F.Id("r"), D(1))),
                Cons(N(), Call("drop", F.Id("a"), Subtract(F.Id("r"), D(1))))))));

    private static Formula SelectionInvariantInsertFormula() => Disp(ForAllMany(
        [Bound("n", Naturals()), Bound("m", Naturals()), Bound("r", Naturals()),
            Bound("s", Naturals()), Bound("a", ListType()), Bound("b", ListType())],
        Implies(And(Equal(N(), Add(F.Id("m"), D(1))),
                Call("IsPerm", F.Id("m"), F.Id("a")),
                Call("IsPerm", F.Id("m"), F.Id("b")),
                Call("SelectionInvariant", F.Id("m"), F.Id("a"), F.Id("b")),
                LessEqual(D(1), F.Id("r")), LessEqual(F.Id("r"), N()),
                Equal(F.Id("s"), Subtract(Multiply(D(2), F.Id("r")), N())),
                LessEqual(D(1), F.Id("s"))),
            Call("SelectionInvariant", N(),
                Call("insertMax", N(), F.Id("r"), F.Id("a")),
                Call("inss", F.Id("s"), F.Id("b"))))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula DVar() => F.Id("d");
    private static Formula Naturals() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula ListType() => Call("List", Naturals());
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);
    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cons(Formula head, Formula tail) => Call("cons", head, tail);
}
