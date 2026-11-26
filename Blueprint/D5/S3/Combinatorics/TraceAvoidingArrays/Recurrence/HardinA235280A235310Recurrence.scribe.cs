using System.Globalization;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235280A235310RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Directory = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/";
    private const string Owner = Directory + "HardinA235280A235310Recurrence";
    private const string Alphabet = Directory + "HardinA235280A235310Alphabet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's three common recurrences for literal constant-stress rectangles.",
        H("Hardin's common recurrences for constant-stress rectangles"),
        Blocks(
            Paragraph(Text("The count C(M,S,n,k) counts literal indexed grids with n+1 rows and k+1 columns. "
                + "Their entries range from 0 to M, and every contiguous 2×2 block has absolute "
                + "difference S between its diagonal and antidiagonal sums. See "), Ref(Alphabet + ".C"), Text(".")),
            Paragraph(Text("The equivalence "), Ref(Alphabet + ".fixedDeficitEquiv"),
                Text(" gives two copies of the grids with block sum d = 2M−S when 0 ≤ d < M and S = 2M−d. In each copy the "
                + "horizontal edge sums in successive rows alternate between a profile and its "
                + "complement in d. An initial entry determines a row from its edge sums. If the "
                + "first edge sum is s, the two complementary row fibers have at most s+1 and "
                + "d−s+1 choices. The resulting one- and two-step laws apply to each profile's "
                + "contribution. The same shift polynomial annihilates every contribution, so it also "
                + "annihilates their sum. This gives the first-axis recurrence, and transposition gives the second.")),
            Endpoint("a235280", "A235280", "a235279", 4, 5,
                [1, 15, -15, -80, 80, 180, -180, -144, 144],
                "A235279 supplies the signed row for column 9. At deficit three the shift polynomial is "
                + "(X−1)(X²−2)(X²−3)(X²−4)(X²−6). The first varying index on either axis is 10."),
            Endpoint("a235310", "A235310", "a235304", 5, 6,
                [4, 25, -112, -231, 1260, 875, -7280, -224, 22736, -7980, -36288, 21456, 23040, -17280],
                "A235304 supplies the signed row for column 2. At deficit four the shift polynomial is "
                + "(X−1)(X−3)(X²−2)(X²−3)(X²−4)(X²−5)(X²−6)(X²−8). "
                + "The first varying index on either axis is 15."),
            A235319())));

    private static DocumentBlock Endpoint(string slugPart, string sequence, string coefficientSource,
        int maximum, int stress, int[] coefficients, string detail) =>
        Describe.Lean(DescribeId.Create(slugPart),
            DeclarationHandle.Create(Owner + "." + slugPart + "_all_rows_and_columns"),
            H(sequence + " recurrence for all rows and columns"),
            StatementSource.FromAuthor(Disp(Statement(maximum, stress, coefficients))),
            AssessedProvenance.FromRepo(Note(slugPart), Note(coefficientSource)),
            Blocks(Paragraph(Text("The table proposes one recurrence for every row and every column. "
                + detail + " The fixed index can be as small as one in both identities."))),
            DescribeRole.Theorem);

    private static DocumentBlock A235319() =>
        Describe.Lean(DescribeId.Create("a235319-all-rows-and-columns"),
            DeclarationHandle.Create(Owner + ".a235319_all_rows_and_columns"),
            H("The common A235319 order-18 recurrence"),
            StatementSource.FromAuthor(Disp(Statement(6, 7,
                [4, 47, -200, -901, 4204, 8957, -48440, -47194, 334096, 101948, -1410080, 170136, 3549696, -1446912, -4861440, 2954880, 2764800, -2073600]))),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Automata/hardin2014a235319"),
                LibraryNoteRef.Create("D5/L/Automata/hardin2014a235317")),
            Blocks(
                Paragraph(Text("C(6,7,n,k) counts the literal indexed rectangles with alphabet 0 through 6 and absolute diagonal difference 7 in every contiguous block. Its integer cast appears in each signed term. The first full window uses indices 1 through 19 in either direction.")),
                Paragraph(Text("At deficit five, complementary row fibers have sizes whose sum is at most seven. The two-step shifts multiply their profile contribution by the product of the fiber sizes. Equal sizes one and three give first-order factors. Expanding the annihilating polynomial gives the published lag coefficients, and transposition supplies the second axis."))),
            DescribeRole.Theorem);

    private static LibraryNoteRef Note(string sequence) =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2014" + sequence);

    private static Formula Statement(int maximum, int stress, int[] coefficients)
    {
        var n = F.Id("n");
        var k = F.Id("k");
        Formula Count(Formula row, Formula column) =>
            Parenthesized(Seq(new Formula.Apply(F.Id("C"), [Number(maximum), Number(stress), row, column]),
                Sp, Colon, Sp, Mathbb, Grp(F.Id("Z"))));
        Formula Shift(Formula index, int amount) =>
            amount == 0 ? index : Seq(index, Sp, Plus, Sp, Number(amount));

        return new Formula.Aligned([
            Seq(Amp, Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Forall, Sp, k, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(0), Sp, Lt, Sp, n, Sp, Implies, Sp, D(0), Sp, Lt, Sp, k, Sp, Implies),
            .. Axis(coefficients, amount => Count(Shift(n, amount), k)),
            Seq(Amp, Land),
            .. Axis(coefficients, amount => Count(n, Shift(k, amount))),
        ]);
    }

    private static IEnumerable<Formula> Axis(int[] coefficients, Func<int, Formula> count)
    {
        var rows = new List<Formula>();
        var row = new List<Formula> { Open, count(coefficients.Length), Sp, Amp, F.Eq };
        for (var index = 0; index < coefficients.Length; index++)
        {
            if (index > 0 && index % 3 == 0)
            {
                rows.Add(Seq([.. row]));
                row = [Amp, Quad];
            }

            var coefficient = coefficients[index];
            if (index > 0)
                row.Add(coefficient > 0 ? Plus : Minus);
            var magnitude = coefficient < 0 ? -coefficient : coefficient;
            if (magnitude != 1)
                row.AddRange([Number(magnitude), Cdot]);
            row.Add(count(coefficients.Length - index - 1));
        }

        row.Add(Close);
        rows.Add(Seq([.. row]));
        return rows;
    }

    private static Formula Number(int value) =>
        D(value.ToString(CultureInfo.InvariantCulture).Select(digit => (byte)(digit - '0')).ToArray());

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
}
