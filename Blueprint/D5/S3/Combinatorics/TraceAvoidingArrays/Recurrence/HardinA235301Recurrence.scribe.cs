using System.Globalization;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235301RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Directory = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/";
    private const string Owner = Directory + "HardinA235301Recurrence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's common order-ten recurrence for stress-three rectangles.",
        H("The A235301 recurrence"),
        Blocks(Describe.Lean(DescribeId.Create("hardin-a235301"),
            DeclarationHandle.Create(Owner + ".hardin_a235301"),
            H("The recurrence in both coordinates"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Automata/hardin2014a235301"),
                LibraryNoteRef.Create("D5/L/Automata/hardin2014a235292")),
            Blocks(
                Paragraph(Text("The integer cast of C(3,3,h,w) counts indexed arrays "
                    + "of shape (h+1) by (w+1) over 0 through 3. Each contiguous "
                    + "2×2 block has absolute diagonal-minus-antidiagonal sum 3. "
                    + "Both identities use a positive fixed side and a varying index at least eleven. "
                    + "The first full window uses indices 1 through 11.")),
                Paragraph(Text("Subtracting three times the product of the row and column "
                    + "indices in the ring modulo six turns the mixed differences into zero. "
                    + "The resulting grid is reconstructed from two boundary words, with the "
                    + "local crossing conditions ensuring that every reconstructed entry and block is legal.")),
                Paragraph(Text("The weighted row transfer records the current type, parity and intersection "
                    + "of compatible column-edge masks. Its acceptance value at any positive width depends "
                    + "only on the mask. The signed residual vectors R0, R1 and R2 satisfy "
                    + "R2 = −3R1 − 2R0, and the first two residual weights sum to zero at every mask. "
                    + "Linearity propagates these equalities to every subsequent residual. "
                    + "This gives one axis, and transposition gives the other."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin-a235301-common-recurrence"), ResolutionKind.Proved)))));

    private static Formula Statement()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        int[] coefficients = [3, 17, -57, -86, 372, 76, -972, 360, 864, -576];
        Formula Count(Formula row, Formula column) =>
            Parenthesized(Seq(new Formula.Apply(F.Id("C"), [D(3), D(3), row, column]),
                Sp, Colon, Sp, Mathbb, Grp(F.Id("Z"))));
        Formula Lag(int amount) => amount == 0 ? n : Seq(n, Sp, Minus, Sp, Number(amount));
        return new Formula.Aligned([
            Seq(Amp, Forall, Sp, k, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(1), Sp, Le, Sp, k, Sp, Implies, Sp, D(1,1), Sp, Le, Sp, n, Sp, Implies),
            .. Axis(coefficients, lag => Count(Lag(lag), k)),
            Seq(Amp, Land),
            .. Axis(coefficients, lag => Count(k, Lag(lag))),
        ]);
    }

    private static IEnumerable<Formula> Axis(int[] coefficients, Func<int, Formula> count)
    {
        var rows = new List<Formula>();
        var row = new List<Formula> { Open, count(0), Sp, Amp, F.Eq };
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
            var magnitude = coefficient > 0 ? coefficient : -coefficient;
            row.AddRange([Number(magnitude), Cdot, count(i + 1)]);
        }
        row.Add(Close);
        rows.Add(Seq([.. row]));
        return rows;
    }

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);

    private static Formula Number(int value) =>
        D(value.ToString(CultureInfo.InvariantCulture).Select(digit => (byte)(digit - '0')).ToArray());
}
