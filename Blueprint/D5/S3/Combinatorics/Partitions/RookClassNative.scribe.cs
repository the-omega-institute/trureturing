using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class RookClassNativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/RookClassNative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native m-level placements give a finite unrestricted class carrier and a common padding bound.",
        H("Native rook classes and common padding"),
        Blocks(
            Definition("cells", "Bottom-aligned cells",
                "The existing normalizedColumnsEquiv sends a positive increasing column tuple to its actual finite Young diagram. Its first coordinate is the row counted from the bottom and its second coordinate counts columns from the right. This horizontal reflection preserves column conflicts and bottom-aligned levels. No zero column or horizontal translation is a new normalized shape."),
            Definition("area", "Literal area", "The area is the sum of the positive column heights, equal to the cardinality of cells."),
            Definition("Nonattacking", "The native conflict rule",
                "For every two distinct cells in the subset, the second coordinates differ and the integer quotients of the first coordinates by m differ. Thus there is at most one rook in each column and in each bottom-aligned block of m rows. For m greater than one, individual row distinctness is insufficient."),
            Definition("placements", "Unlabeled placements",
                "Filter the k-element subsets of the actual cells by Nonattacking. Each cell subset has weight one, independent of any ordering of its rooks."),
            Definition("rookCount", "Finite native rook numbers", "The native rook number is the cardinality of placements, a finite subset enumeration. It is not defined from a root polynomial or from an assumed paper theorem."),
            Theorem("rookCount_zero", "The empty placement", CountAt(D(0), D(1)),
                "The unique zero-element subset is empty and satisfies both conflict conditions."),
            Theorem("rookCount_one", "One rook counts the area", CountAt(D(1), Call("area", F.Id("b"))),
                "Every singleton cell subset is legal. Its count equals the sum of the source column heights via the existing normalization equivalence and Young-diagram area identity."),
            Theorem("rookCount_eq_zero_of_area_lt", "Vanishing above the area",
                All("m", Nat(), All("b", Boards(), All("k", Nat(), Imp(
                    Lt(Call("area", F.Id("b")), F.Id("k")),
                    Eq(Call("rookCount", F.Id("m"), F.Id("b"), F.Id("k")), D(0)))))),
                "No subset of the board has more cells than the area. This bound does not assume a width or singleton condition."),
            Definition("RookEquivalent", "Every native rook number", "Two normalized shapes are equivalent exactly when their rookCount values agree for every natural k, including zero."),
            Theorem("rookEquivalent_iff", "A complete finite comparison", FiniteVector(),
                "The common area follows from the one-rook count. The positive indices through that area suffice: the zero index is one and every larger index is zero. Icc denotes the inclusive interval of natural indices."),
            Definition("RookClass", "The unrestricted native class", "The subtype contains every normalized positive-column shape with the same native rook numbers. Its definition imposes no width or height bound."),
            Theorem("rookClass_finite", "Finiteness before cardinality conventions",
                All("m", Nat(), All("b", Boards(), Call("Finite", Call("RookClass", F.Id("m"), F.Id("b"))))),
                "For a cell with coordinates i and j, lower closure supplies i+1 cells in its column and j+1 in its row. Both coordinates are strictly below the area. Equal rook numbers force equal area. Sending a class member to its actual cells therefore embeds the entire class into the powerset of the area by area square. Finite is established without using Nat.card on an unproved finite carrier."),
            Definition("pad", "One fixed padding", "At length N, prepend N minus the positive-column length zero entries. This is the lower-right alignment convention."),
            Theorem("class_padding", "All registered common lengths", Padding(),
                "For every native class member and every N at least area(b)+1, its positive-column length is below N, its padding has length N, the head is zero, and the padded sum is area(b). The empty board and zero padding are included. In the formula, columns(a) is the underlying positive list of the class member, board(a) is that normalized shape, and head returns an Option natural.")
        ), []));

    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("rookclassnative-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("rookclassnative-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Nat() => F.Id("Nat");
    private static Formula Boards() => F.Id("PositiveColumns");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, Seq(Open, y, Close));
    private static Formula CountAt(Formula k, Formula result) => All("m", Nat(), All("b", Boards(),
        Eq(Call("rookCount", F.Id("m"), F.Id("b"), k), result)));
    private static Formula FiniteVector() => All("m", Nat(), All("a", Boards(), All("b", Boards(),
        new Formula.Logic(Call("RookEquivalent", F.Id("m"), F.Id("a"), F.Id("b")), FormulaLogicOperator.Iff,
            Seq(Open, And(Eq(Call("area", F.Id("a")), Call("area", F.Id("b"))),
                All("k", Nat(), Imp(Call("mem", F.Id("k"), Call("Icc", D(1), Call("area", F.Id("b")))),
                    Eq(Call("rookCount", F.Id("m"), F.Id("a"), F.Id("k")),
                        Call("rookCount", F.Id("m"), F.Id("b"), F.Id("k")))))), Close)))));
    private static Formula Padding() => All("m", Nat(), All("b", Boards(), All("n", Nat(), Imp(
        Le(new Formula.Binary(Call("area", F.Id("b")), FormulaBinaryOperator.Add, D(1)), F.Id("n")),
        All("a", Call("RookClass", F.Id("m"), F.Id("b")),
            And(Lt(Call("length", Call("columns", F.Id("a"))), F.Id("n")),
                And(Eq(Call("length", Call("pad", F.Id("n"), Call("board", F.Id("a")))), F.Id("n")),
                    And(Eq(Call("head", Call("pad", F.Id("n"), Call("board", F.Id("a")))), Call("some", D(0))),
                        Eq(Call("sum", Call("pad", F.Id("n"), Call("board", F.Id("a")))), Call("area", F.Id("b")))))))))));
}
