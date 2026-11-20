using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class UXPentominoBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/UXPentominoBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/condon2026polyominodensity");
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Boards => Call("Finset", F.Id("Point"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive threshold the fewest board cells needed for U and X pentomino translates agree.",
        H("The U and X Pentomino Instance Sequences"),
        Blocks(
            Paragraph(Text("Section 10 of Condon, Dugan, Goldman and Williams poses the equality for finite nonempty square-grid boards connected by horizontal and vertical unit edges. The minimum counts all distinct translation anchors and requires at least N of them. Both sides use the board, translation, and minimum definitions from LPolyominoSkippedSequence.")),
            Node("U", "The U pentomino",
                Eq(F.Id("U"), new Formula.SetLiteral([Pair(NegOne(), D(0)), Pair(D(0), D(0)),
                    Pair(D(1), D(0)), Pair(NegOne(), D(1)), Pair(D(1), D(1))])),
                "The origin is the middle cell of the bottom row.", DescribeRole.Definition),
            Node("X", "The X pentomino",
                Eq(F.Id("X"), new Formula.SetLiteral([Pair(D(0), D(0)), Pair(NegOne(), D(0)),
                    Pair(D(1), D(0)), Pair(D(0), NegOne()), Pair(D(0), D(1))])),
                "The origin is the center of the cross.", DescribeRole.Definition),
            Node("u_card_bound", "The U board lower bound", BoardBound("U"),
                "Each nonempty anchor column supplies an extra cell in either outer arm column. In each parity, send columns to the arm directed away from a maximum and keep both arms of that maximum. This counts disjoint columns even for profiles with gaps. The two parity counts and the center-cell constraint give the quadratic bound."),
            Node("x_card_bound", "The X board lower bound", BoardBound("X"),
                "Condon, Dugan, Goldman and Williams derive the X optimum in Section 5 and state its explicit formula in Theorem 6.4. The finite-set bound here uses the center and two vertical arms in integer coordinates (x + y, y)."),
            Node("u_board_of_x_board", "Compressing X boards to U boards", Transfer(),
                "Section 3, Lemmas 3.1–3.3 and Figure 8 of the cited paper give the comparison that the U minimum is at most the X minimum. Here each diagonal column is stacked at height zero while preserving its cardinality. An original board edge changes x + y by one, so original paths give paths along the new bottom row. Stacking the translation-anchor fibers fits every U arm by the same column bound."),
            Node("same_minimum", "Equality for every positive threshold", Equality(),
                "The reverse U lower bound supplies the missing inequality in the Section 10 conjecture. It bounds the slack above N + 2. In coordinates (x + y, x − y), a balanced checkerboard rectangle realizes the corresponding anchor capacity. Trim a suffix of its last anchor row and delete the associated cells of the outer board row. Each deleted outer cell could only support deleted anchors. The full lower rows connect the resulting X board. The area-preserving transfer gives the Section 3 comparison.",
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("condon-dugan-goldman-williams-2026-ux-pentomino-instance-sequence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role = DescribeRole.Theorem, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ux-pentomino-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            role == DescribeRole.Definition ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula BoardBound(string shape)
    {
        Formula p = F.Id("P");
        Formula count = Count(p, shape);
        Formula area = Call("card", p);
        Formula slack = Sub(Sub(area, count), D(2));
        return Bind(Forall, "P", Boards, Logic(Lt(D(0), count), FormulaLogicOperator.Implies,
            Logic(Le(Add(count, D(2)), area), FormulaLogicOperator.And,
                Le(new Formula.Binary(D(8), FormulaBinaryOperator.Multiply, count),
                    Add(new Formula.Power(Paren(slack), D(2)), D(4))))));
    }

    private static Formula Transfer()
    {
        Formula p = F.Id("P"), q = F.Id("Q");
        return Bind(Forall, "P", Boards, Logic(Call("IsPolyomino", p), FormulaLogicOperator.Implies,
            Bind(Exists, "Q", Boards, Logic(Call("IsPolyomino", q), FormulaLogicOperator.And,
                Logic(Le(Count(p, "X"), Count(q, "U")), FormulaLogicOperator.And,
                    Eq(Call("card", q), Call("card", p)))))));
    }

    private static Formula Equality()
    {
        Formula n = F.Id("N");
        return Bind(Forall, "N", Nats, Logic(Lt(D(0), n), FormulaLogicOperator.Implies,
            Eq(Call("a", F.Id("U"), n), Call("a", F.Id("X"), n))));
    }

    private static Formula Count(Formula p, string shape) => Call("card", Call("instances", p, F.Id(shape)));
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula x, Formula y) => Paren(Seq(x, Comma, Sp, y));
    private static Formula NegOne() => Seq(Minus, Sp, D(1));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Paren(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(Paren(x), op, Paren(y));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
}
