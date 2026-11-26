using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235291RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235291Recurrence";
    private const string Source = "D5/L/Automata/hardin2014a235291";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's signed order-four recurrence for indexed two-column arrays.",
        H("The A235291 two-column recurrence"),
        Blocks(Describe.Lean(
            DescribeId.Create("a235291-order-four"),
            DeclarationHandle.Create(Owner + ".result"),
            H("The A235291 signed recurrence"),
            StatementSource.FromAuthor(Disp(Recurrence())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Source)),
            Blocks(
                Paragraph(Text("Let a(n) be the integer cast of C(3,3,n,1), the number of indexed "
                    + "(n+1)-by-2 arrays with entries 0 through 3. Each contiguous 2-by-2 block has "
                    + "absolute difference 3 between the diagonal and antidiagonal sums. The first "
                    + "complete recurrence window ends at index 5.")),
                Paragraph(Text("A row with signed difference d between its entries has 4−|d| "
                    + "possible fillings. Two rows may be adjacent exactly when their differences "
                    + "d differ by 3 in absolute value. The transfer sums over admissible next "
                    + "differences, with the number of fillings as the weight of each.")),
                Paragraph(Text("One step makes the function values at differences −3 and 3 equal, since "
                    + "both lead only to 0. On functions with that equality, two steps multiply "
                    + "the component {−3,0,3} by 8 and each of {−2,1} and {−1,2} by 6. "
                    + "Thus (X²−6)(X²−8) annihilates the transfer after the first step, for "
                    + "arbitrary terminal weights. Taking unit terminal weights and summing over "
                    + "first rows gives the signed recurrence for the number of arrays."))),
            DescribeRole.Theorem))));

    private static Formula Recurrence()
    {
        var n = F.Id("n");
        Formula Count(Formula index) => Call("a", index);
        var right = Subtract(Multiply(D(1, 4), Count(Subtract(n, D(2)))),
            Multiply(D(4, 8), Count(Subtract(n, D(4)))));
        return Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(5), Sp, Le, Sp, n, Sp, Implies, Sp, Equal(Count(n), right));
    }
}
