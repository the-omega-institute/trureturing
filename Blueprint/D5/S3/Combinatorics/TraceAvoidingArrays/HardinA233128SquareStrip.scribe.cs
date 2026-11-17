using System.Globalization;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233128SquareStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233128");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's order-fourteen recurrence for seven-column square strips.",
        H("One-row certification and all-height recurrence"),
        Blocks(
            Paragraph(Text(
                "All counts use the literal filter in HardinA233128Rows. All names below "
                + "are full Lean names. Fin.val is the natural value of a finite index. "
                + "Nat.div denotes natural quotient and Nat.mod its nonnegative remainder; "
                + "neither occurs in the formulas. At width 7 the generic "
                + "width_counting_bridge applies with rowLegal, labels, compatible and "
                + "bonds. The colour_bond_iff theorem identifies each vertical bond with "
                + "inequality of complementary-pair labels, while widthNormal supplies "
                + "the row-major precedence conditions.")),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Single-row certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The scanner_fibres theorem reduces 6^7 individual rows to 3^7 label "
                    + "rows. The first_fibres owner fixes the initial zero before summing "
                    + "the six remaining label positions. The 192 proper label rows form "
                    + "20 relabelling-and-reversal classes after colour 2; the unseen "
                    + "sector gives one additional state with eigenvalue 128."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The recurrence at every positive source height"),
                StatementSource.FromAuthor(Disp(Result())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The exact one-step counts preserve class-constant continuation vectors. "
                    + "Iteration is the finite-class instance of Function.Semiconj.iterate_right. "
                    + "The first distribution has total 528. Its successive products with "
                    + "the 21-by-21 transfer obey the displayed fourteen-term linear identity. "
                    + "That vector identity is stronger than the corresponding scalar "
                    + "identity: multiplying it by the continuation vector at any height "
                    + "proves the recurrence for the literal counts. The index n is any "
                    + "natural number, so the left side covers every height at least 15. "
                    + "Every count is cast to Int before signed arithmetic."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233128"),
                    ResolutionKind.Proved)))));

    private static Formula Seen() => Name(Scanner + "Seen");
    private static Formula PairRow() => Name(BoundaryOwner + "PairRow");
    private static Formula Certificate()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return And(All("s", Seen(), All("p", PairRow(), Imp(Call(Root + "Valid", s, p),
            All("k", Fin(21), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k)))))),
            All("k", Fin(21), Eq(Call(Root + "firstCount", k),
                At(Vector(Number("32"), Number("0"), Number("32"), Number("32"), Number("32"),
                Number("16"), Number("32"), Number("32"), Number("32"), Number("32"),
                Number("16"), Number("32"), Number("32"), Number("16"), Number("32"),
                Number("16"), Number("32"), Number("16"), Number("32"), Number("16"),
                Number("16")), k))));
    }

    private static Formula Result()
    {
        var n = V("n");
        Formula A(int k) => Typed(Call(Root + "a",
            Add(n, Number(((int)k).ToString(CultureInfo.InvariantCulture)))), Name("Int"));
        var coefficients = new[] {
            "7168",
            "-19070976",
            "26086473728",
            "-21081846972416",
            "10809917287956480",
            "-3649692508960587776",
            "824336623994081902592",
            "-124561639357723747287040",
            "12414326720213201465638912",
            "-792885332473813431379558400",
            "31062140009178282014900486144",
            "-704387882353381376417601683456",
            "8398185226512019784915658735616",
            "-40564819207303340847894502572032"
        };
        Formula term = Mul(Number(coefficients[0]), A(14));
        for (var j = 1; j < coefficients.Length; j++)
        {
            var c = coefficients[j];
            var magnitude = c.StartsWith('-') ? c.Substring(1, c.Length - 1) : c;
            var product = Mul(Number(magnitude), A(14 - j));
            term = c.StartsWith('-') ? Sub(term, product) : Add(term, product);
        }
        return All("n", Name("Nat"), Eq(A(15), term));
    }

    private static Formula Number(string n) => D(n.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((p, i) =>
        (i == 0 ? Array.Empty<Formula>() : new Formula[] { Dot }).Append(
            Seq(Operatorname, Grp(p.Select((c, j) => c >= '0' && c <= '9'
                ? D((byte)(c - '0')) : V(p.Substring(j, 1))).ToArray())))).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Fin(byte k) =>
        Call("Fin", Number(((int)k).ToString(CultureInfo.InvariantCulture)));
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
}
