using System.Globalization;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235270DiagonalRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235270DiagonalRecurrence";
    private const string Source = "D5/L/Automata/hardin2014a235270";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's eleven-lag recurrence for indexed constant-stress squares.",
        H("The A235270 diagonal recurrence"),
        Blocks(A235270Recurrence())));

    private static DocumentBlock A235270Recurrence()
    {
        var n = F.Id("n");
        int[] coefficients = [1, 23, -23, -200, 200, 820, -820, -1584, 1584, 1152, -1152];
        return Describe.Lean(DescribeId.Create("a235270-order11"),
            DeclarationHandle.Create(Owner + ".a235270_order11"), H("The A235270 eleven-lag recurrence"),
            StatementSource.FromAuthor(Disp(SignedRecurrence(n, coefficients))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Source)),
            Blocks(
                Paragraph(Text("The integer cast of C(4,5,n,n) counts indexed square "
                    + "arrays of side n+1 over entries 0 through 4. Every contiguous 2×2 block has absolute "
                    + "difference 5 between its diagonal and antidiagonal sums. Each lag shifts both sides of "
                    + "the square. The first full window uses indices 1 through 12.")),
                Paragraph(Text("For a row with a prescribed horizontal edge-sum profile, a forward shift "
                    + "raises the even-column entries and lowers the odd-column entries. The minimum odd-column "
                    + "entry counts the forward steps available. Counting pairs from complementary profiles "
                    + "with prescribed numbers of available steps reduces to independent column choices. "
                    + "Mixed second differences give the exact frequencies of the two fiber sizes.")),
                Paragraph(Text("The profile expansion on the square diagonal has constant terms, zero terms "
                    + "and terms multiplied by 2, 3, 4, 6 or 8 under a two-index advance. The polynomial "
                    + "(X−1)(X²−2)(X²−3)(X²−4)(X²−6)(X²−8) annihilates the sum for the forward shift X. "
                    + "Its expansion gives the signed recurrence."))),
            DescribeRole.Theorem);
    }

    private static Formula SignedRecurrence(Formula index, int[] coefficients)
    {
        Formula Count(int shift)
        {
            var side = shift == 0 ? index : Add(index, Number(shift));
            return Seq(Open, Call("C", D(4), D(5), side, side), Sp, Colon, Sp,
                Mathbb, Grp(F.Id("Z")), Close);
        }

        var rows = new List<Formula>();
        var row = new List<Formula> { Count(coefficients.Length), Sp, Amp, F.Eq };
        for (var i = 0; i < coefficients.Length; i++)
        {
            if (i > 0 && i % 3 == 0)
            {
                rows.Add(Seq([.. row]));
                row = [Amp, Quad];
            }

            var coefficient = coefficients[i];
            if (i > 0)
                row.Add(coefficient > 0 ? Plus : Minus);
            var magnitude = coefficient < 0 ? -coefficient : coefficient;
            if (magnitude != 1)
                row.AddRange([Number(magnitude), Cdot]);
            row.Add(Count(coefficients.Length - i - 1));
        }

        rows.Add(Seq([.. row]));
        return new Formula.Aligned([
            Seq(Amp, Forall, Sp, index, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(1), Sp, Le, Sp, index, Sp, Implies),
            .. rows,
        ]);
    }

    private static Formula Number(int value) =>
        D(value.ToString(CultureInfo.InvariantCulture).Select(digit => (byte)(digit - '0')).ToArray());
}
