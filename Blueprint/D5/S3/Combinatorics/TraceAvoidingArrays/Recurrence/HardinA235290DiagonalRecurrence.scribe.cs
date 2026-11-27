using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235290DiagonalRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Result = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/"
        + "HardinA235290DiagonalRecurrence.hardin_a235290";
    private const string Note = "D5/L/Automata/hardin2014a235290";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eleven-lag recurrence for literal stress-three square arrays.",
        H("Hardin's diagonal recurrence for stress-three arrays"),
        Blocks(Describe.Lean(
            DescribeId.Create("hardin-a235290"),
            DeclarationHandle.Create(Result),
            H("The signed eleven-lag recurrence"),
            StatementSource.FromAuthor(Disp(RecurrenceStatement())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(
                Paragraph(Text("The count C(3,3,h,w) is the number of indexed arrays of height h+1 "
                    + "and width w+1 with entries 0 through 3. Every contiguous two-by-two block "
                    + "has an absolute difference of three between its diagonal and antidiagonal sums. "
                    + "The integer a(n) is C(3,3,n,n). Indices and their differences are natural "
                    + "numbers, and the recurrence is an equality over the integers.")),
                Paragraph(Text("Apply the signed eleven-lag recurrence as a residual on rectangles, "
                    + "shifting the two side parameters together. At each positive fixed side, "
                    + "the rectangular count obeys the common order-ten recurrence in the other "
                    + "coordinate. The finite sum defining the residual commutes with the order-ten "
                    + "rule, so the residual obeys that rule separately in both coordinates.")),
                Paragraph(Text("A sparse row transfer and a six-state column continuation count "
                    + "give the literal counts for both side parameters from one through ten. "
                    + "The axial recurrences determine the table through side parameter twenty-one. "
                    + "The residual vanishes on the full ten-by-ten window of starting side parameters. "
                    + "The order-ten recurrence propagates those zeros along both axes. "
                    + "Taking the two side parameters equal gives the displayed identity."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin-a235290-diagonal-recurrence"),
                ResolutionKind.Proved)))));

    private static Formula RecurrenceStatement()
    {
        var n = F.Id("n");
        Formula At(Formula index) => Call("a", index);
        Formula Lag(params byte[] digits) => At(Subtract(n, D(digits)));

        var right = Add(Multiply(D(4), Lag(1)), Multiply(D(2, 3), Lag(2)));
        right = Subtract(right, Multiply(D(9, 2), Lag(3)));
        right = Subtract(right, Multiply(D(2, 0, 0), Lag(4)));
        right = Add(right, Multiply(D(8, 0, 0), Lag(5)));
        right = Add(right, Multiply(D(8, 2, 0), Lag(6)));
        right = Subtract(right, Multiply(D(3, 2, 8, 0), Lag(7)));
        right = Subtract(right, Multiply(D(1, 5, 8, 4), Lag(8)));
        right = Add(right, Multiply(D(6, 3, 3, 6), Lag(9)));
        right = Add(right, Multiply(D(1, 1, 5, 2), Lag(1, 0)));
        right = Subtract(right, Multiply(D(4, 6, 0, 8), Lag(1, 1)));

        return Seq(Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Open, D(1, 2), Sp, Le, Sp, n, Sp, Implies, Sp,
            Equal(At(n), right), Close);
    }

    private static Formula Call(string name, Formula index) => new Formula.Apply(F.Id(name), [index]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
