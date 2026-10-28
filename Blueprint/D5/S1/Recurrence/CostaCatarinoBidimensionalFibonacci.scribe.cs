using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CostaCatarinoBidimensionalFibonacciDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Scale/costacatarino2025bidimensional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bidimensional Fibonacci matrices have nonzero determinant at every pair of natural indices.",
        H("Costa–Catarino Bidimensional Fibonacci Matrices"),
        Blocks(
            Node("sequence", "The two-coordinate Fibonacci sequence", "IsSourceSequence",
                All("f", Parenthesized(ArrayType()), Iff(Call("IsSourceSequence", X("f")),
                    Parenthesized(SequenceBody()))), SequenceProse(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("closed-form", "The Fibonacci closed form", "sourceClosedForm",
                All("m", Naturals(), All("n", Naturals(),
                    Equal(Call("sourceClosedForm", X("m"), X("n")), ClosedFormBody()))),
                ClosedFormProse(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("matrix", "The order-two matrix", "sourceMatrix",
                All("f", Parenthesized(ArrayType()), All("m", Naturals(), All("n", Naturals(),
                    Equal(Call("sourceMatrix", X("f"), X("m"), X("n")), MatrixBody())))),
                MatrixProse(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The nonsingularity conjecture", "claim",
                Iff(X("claim"), Parenthesized(ClaimBody())), ClaimProse(),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All bidimensional Fibonacci matrices are nonsingular", "result",
                ClaimBody(),
                Prose("The closed form satisfies the two recurrences and four corner values, which "
                    + "determine the sequence uniquely. Cassini's identity expresses the imaginary "
                    + "part of the determinant as a signed sum of two positive consecutive "
                    + "Fibonacci products. These products strictly increase with the index. "
                    + "Equal signs give a nonzero sum; opposite signs cannot cancel at distinct "
                    + "indices, and equal indices have equal signs. Thus the imaginary part, "
                    + "and hence the determinant, never vanishes."),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        BlockSequence prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("costa-catarino-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            prose, role, openProblemResolutionClaim: resolution);

    private static BlockSequence Prose(string text) => Blocks(Paragraph(Text(text)));

    private static BlockSequence SequenceProse() => Blocks(Paragraph(
        Text("Definition 2.1, p. 63: “For integers "), Math(Nonnegative(X("m"))),
        Text(" and "), Math(Nonnegative(X("n"))), Text(", the bidimensional Fibonacci numbers "),
        Math(SourceSequence(false)), Text(" are defined recursively by” (2.1) and (2.2), “with initial terms "),
        Math(Equal(SourceEntry(D(0), D(0)), D(0))), Text(", "),
        Math(Equal(SourceEntry(D(1), D(0)), D(1))), Text(", "),
        Math(Equal(SourceEntry(D(0), D(1)), X("i"))), Text(", "),
        Math(Equal(SourceEntry(D(1), D(1)), Add(D(1), X("i")))),
        Text(", where "), Math(X("i")), Text(" is the imaginary unit and "),
        Math(Equal(new Formula.Power(X("i"), D(2)), Seq(Minus, D(1)))),
        Text(".” The two guarded equalities below state those recurrences on natural indices, with values in the complex numbers.")));

    private static BlockSequence ClosedFormProse() => Blocks(Paragraph(
        Text("Lemma 2.5, p. 64: “For non-negative integers "), Math(X("n")),
        Text(" and "), Math(X("m")), Text(", the bidimensional Fibonacci numbers are described as follows:” "),
        Math(Equal(SourceEntry(X("m"), X("n")), Add(
            Mul(new Formula.Subscript(X("f"), X("m")), new Formula.Subscript(X("f"), Add(X("n"), D(1)))),
            Mul(Mul(X("i"), new Formula.Subscript(X("f"), Add(X("m"), D(1)))),
                new Formula.Subscript(X("f"), X("n")))))),
        Text(", equation (2.6). Here Nat.fib is the ordinary Fibonacci sequence with initial terms zero and one; each occurrence is cast to ℂ.")));

    private static BlockSequence MatrixProse() => Blocks(Paragraph(
        Text("Definition 3.1, p. 67: “For all non-negative integers "), Math(X("m")),
        Text(" and "), Math(X("n")), Text(", the bidimensional Fibonacci matrices "),
        Math(SourceSequence(true)), Text(" are given by” (3.1), “where "),
        Math(SourceSequence(false)), Text(" is the bidimensional Fibonacci sequence.” The matrix below retains both negative entries and uses Matrix (Fin 2) (Fin 2) ℂ.")));

    private static BlockSequence ClaimProse() => Blocks(Paragraph(
        Text("Unnumbered Conjecture, §4, p. 73: “Let "), Math(SourceSequence(true)),
        Text(" be the sequence of bidimensional Fibonacci matrices of order 2. For all non-negative integers "),
        Math(X("m")), Text(" and "), Math(X("n")),
        Text(", the determinant is non-vanishing, that is, the determinant satisfies:” "),
        Math(new Formula.Relation(Seq(Bar, SourceMatrixEntry(), Bar), FormulaRelationOperator.NotEqual, D(0))),
        Text(". The bars denote determinant. The proposition below also asserts existence of the recursively specified sequence; its universal statement includes both axes and the diagonal.")));

    private static Formula SourceSequence(bool matrix) => new Formula.Subscript(
        Seq(OpenBrace, matrix ? SourceMatrixEntry() : SourceEntry(X("m"), X("n")), CloseBrace),
        Nonnegative(Seq(X("m"), Comma, X("n"))));
    private static Formula SourceEntry(Formula m, Formula n) => new Formula.Subscript(
        X("f"), Parenthesized(Seq(m, Comma, n)));
    private static Formula SourceMatrixEntry() => new Formula.Subscript(
        Seq(Mathcal, Grp(X("F"))), Parenthesized(Seq(X("m"), Comma, X("n"))));
    private static Formula Nonnegative(Formula x) =>
        new Formula.Relation(x, FormulaRelationOperator.GreaterThanOrEqual, D(0));

    private static Formula SequenceBody()
    {
        var m = X("m");
        var n = X("n");
        var first = All("m", Naturals(), All("n", Naturals(), Imp(AtMost(D(2), m),
            Equal(Apply(X("f"), m, n), Add(Apply(X("f"), Sub(m, D(1)), n),
                Apply(X("f"), Sub(m, D(2)), n))))));
        var second = All("m", Naturals(), All("n", Naturals(), Imp(AtMost(D(2), n),
            Equal(Apply(X("f"), m, n), Add(Apply(X("f"), m, Sub(n, D(1))),
                Apply(X("f"), m, Sub(n, D(2))))))));
        return And(Parenthesized(first), And(Parenthesized(second),
            And(Equal(Apply(X("f"), D(0), D(0)), D(0)),
            And(Equal(Apply(X("f"), D(1), D(0)), D(1)),
            And(Equal(Apply(X("f"), D(0), D(1)), Qualified("Complex", "I")),
                Equal(Apply(X("f"), D(1), D(1)), Add(D(1), Qualified("Complex", "I"))))))));
    }

    private static Formula ClosedFormBody() => Add(
        Mul(FibCast(X("m")), FibCast(Add(X("n"), D(1)))),
        Mul(Mul(Qualified("Complex", "I"), FibCast(Add(X("m"), D(1)))),
            FibCast(X("n"))));

    private static Formula MatrixBody() => Seq(Bang, Bang, OpenBracket,
        Apply(X("f"), Add(X("m"), D(2)), Add(X("n"), D(2))), Comma, Sp,
        Minus, Apply(X("f"), Add(X("m"), D(1)), Add(X("n"), D(1))), Semi, Sp,
        Apply(X("f"), Add(X("m"), D(1)), Add(X("n"), D(1))), Comma, Sp,
        Minus, Apply(X("f"), X("m"), X("n")), CloseBracket);

    private static Formula ClaimBody() => And(
        Parenthesized(new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("f"), Parenthesized(ArrayType()), Call("IsSourceSequence", X("f")))),
        Parenthesized(All("f", Parenthesized(ArrayType()), Imp(Call("IsSourceSequence", X("f")),
            All("m", Naturals(), All("n", Naturals(),
                new Formula.Relation(Apply(Qualified("Matrix", "det"),
                    Call("sourceMatrix", X("f"), X("m"), X("n"))),
                    FormulaRelationOperator.NotEqual, D(0))))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(X("C")));
    private static Formula ArrayType() => new Formula.TypeArrow(Naturals(),
        new Formula.TypeArrow(Naturals(), ComplexNumbers()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FibCast(Formula index) => Parenthesized(
        Seq(Apply(Qualified("Nat", "fib"), index), Colon, Sp, ComplexNumbers()));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
