using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127SquareStripDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233127");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin’s recurrence for normalized six-column complementary-pair square strips.",
        H("The finite certificate and the all-height recurrence"),
        Blocks(
            Describe.Lean(DescribeId.Create("distribution"),
                DeclarationHandle.Create(Gid + "distribution"), H("Forward boundary distributions"),
                StatementSource.FromAuthor(Disp(Eq(Name(Root + "distribution"), Matrix(
                        [D(1,6), D(0), D(1,6), D(1,6), D(1,6), D(1,6), D(1,6), D(8), D(8), D(1,6), D(8)],
                        [D(1,0,2,4), D(1,0,2,4,0), D(1,8,4,3,2), D(1,4,3,3,6), D(1,9,4,5,6), D(1,7,4,0,8), D(1,1,2,6,4), D(8,1,9,2), D(3,5,8,4), D(1,3,3,1,2), D(7,6,8,0)],
                        [D(6,5,5,3,6), D(1,1,8,9,4,7,8,4), D(1,9,9,2,2,9,4,4), D(1,3,6,9,7,0,2,4), D(2,0,9,0,5,9,8,4), D(1,9,1,3,6,5,1,2), D(9,7,6,4,8,6,4), D(8,2,5,7,5,3,6), D(2,5,8,8,6,7,2), D(1,3,6,9,7,0,2,4), D(7,6,0,2,1,7,6)],
                        [D(4,1,9,4,3,0,4), D(1,2,7,3,1,8,0,9,7,9,2), D(2,1,1,2,6,7,0,9,2,4,8), D(1,3,8,2,0,2,3,1,6,8,0), D(2,2,0,6,6,2,3,3,3,4,4), D(2,0,4,5,1,4,2,6,3,0,4), D(9,4,7,9,1,2,7,0,4,0), D(8,5,2,2,8,2,5,7,2,8), D(2,3,1,9,4,5,0,1,1,2), D(1,4,3,9,0,6,5,7,0,2,4), D(7,7,6,9,9,4,8,1,6,0)],
                        [D(2,6,8,4,3,5,4,5,6), D(1,3,4,3,9,4,8,9,5,4,0,0,9,6), D(2,2,2,5,0,3,4,6,5,1,2,3,8,4), D(1,4,2,8,5,5,9,8,0,9,7,4,0,8), D(2,3,1,9,4,9,7,0,8,8,2,0,4,8), D(2,1,6,0,0,4,6,4,2,7,3,4,0,8), D(9,6,5,6,6,9,7,0,9,4,1,4,4), D(8,8,8,8,5,6,9,0,3,6,8,0,0), D(2,2,8,5,3,2,5,2,5,4,6,5,6), D(1,5,1,2,1,5,0,6,1,0,7,3,9,2), D(8,0,6,7,8,2,7,6,3,0,0,8,0)],
                        [D(1,7,1,7,9,8,6,9,1,8,4), D(1,4,1,2,9,5,2,3,2,8,0,8,3,8,6,5,6), D(2,3,3,7,5,6,3,4,3,8,6,3,8,6,9,4,4), D(1,4,9,0,5,2,8,8,8,6,3,7,7,6,7,6,8), D(2,4,3,5,0,3,6,8,6,2,4,2,7,9,5,5,2), D(2,2,7,1,6,0,1,3,3,0,9,0,6,7,2,6,4), D(1,0,0,2,1,8,5,9,5,0,8,6,1,7,2,1,6), D(9,3,0,5,2,2,7,0,3,5,4,1,0,4,3,2), D(2,3,4,1,1,6,9,4,9,3,1,8,0,4,1,6), D(1,5,8,7,5,5,0,4,7,9,6,0,7,3,9,8,4), D(8,4,3,1,1,8,4,0,1,0,8,0,5,2,4,8)],
                        [D(1,0,9,9,5,1,1,6,2,7,7,7,6), D(1,4,8,3,4,5,4,8,7,5,9,5,4,6,8,2,2,6,5,6), D(2,4,5,3,5,7,3,0,6,1,6,6,8,1,8,8,9,7,9,2), D(1,5,6,0,5,8,6,8,8,1,0,8,1,5,4,0,6,0,8,0), D(2,5,5,5,2,0,5,2,0,9,5,1,8,8,7,2,9,8,5,6), D(2,3,8,5,2,1,1,5,8,5,9,1,8,1,9,2,8,4,4,8), D(1,0,4,7,2,5,0,0,8,0,8,8,9,2,0,2,2,7,8,4), D(9,7,5,4,6,1,3,7,2,4,1,9,8,4,6,9,6,3,2), D(2,4,3,4,6,0,2,9,6,7,6,5,1,8,4,4,0,9,6), D(1,6,6,5,9,6,6,1,6,4,5,5,9,6,8,5,2,2,2,4), D(8,8,3,2,4,7,7,5,1,1,2,3,8,5,4,9,5,0,4)],
                        [D(7,0,3,6,8,7,4,4,1,7,7,6,6,4), D(1,5,5,6,7,1,0,8,2,3,7,5,7,4,8,1,4,0,4,0,0,6,4), D(2,5,7,4,4,9,9,1,9,3,2,7,2,4,8,1,6,1,1,7,7,6,0), D(1,6,3,6,0,1,0,9,2,7,2,7,5,8,4,8,9,1,8,6,3,0,4), D(2,6,8,0,8,8,1,2,1,1,1,2,4,1,4,3,9,8,7,0,9,7,6), D(2,5,0,3,1,0,0,0,5,3,6,4,7,5,7,2,9,1,3,3,5,6,8), D(1,0,9,7,0,8,8,4,6,5,9,9,6,4,9,3,3,0,4,6,2,7,2), D(1,0,2,3,0,6,6,7,7,8,2,7,3,8,8,7,7,0,8,7,7,4,4), D(2,5,4,5,9,2,3,3,9,6,2,3,9,9,7,8,6,5,9,8,4,0), D(1,7,4,7,9,3,9,0,5,7,6,9,9,8,7,3,8,8,2,1,1,2,0), D(9,2,6,1,2,4,7,3,0,9,7,2,0,9,6,1,6,7,9,3,6,0)],
                        [D(4,5,0,3,5,9,9,6,2,7,3,7,0,4,9,6), D(1,6,3,3,2,9,5,0,3,2,8,7,1,6,4,3,0,2,9,2,2,8,7,4,8,8), D(2,7,0,1,0,6,5,2,4,1,8,3,5,0,5,9,7,9,7,8,1,9,3,9,2,0), D(1,7,1,5,8,7,1,9,8,6,7,5,0,7,5,5,2,2,9,2,9,6,2,3,0,4), D(2,8,1,2,5,7,8,3,9,0,3,2,3,2,2,0,5,2,0,6,3,2,3,2,0,0), D(2,6,2,6,2,8,2,0,3,5,0,7,5,2,9,0,0,6,9,6,2,4,4,2,2,4), D(1,1,5,0,3,4,7,1,6,2,3,9,2,1,6,9,0,0,5,9,2,1,0,7,5,2), D(1,0,7,3,1,8,3,2,3,3,5,2,3,9,8,1,1,0,8,2,2,2,3,6,1,6), D(2,6,6,7,7,8,1,6,3,4,2,3,5,1,5,7,8,3,8,8,2,3,4,2,4), D(1,8,3,3,8,1,9,6,9,2,3,8,7,8,3,8,3,0,6,3,9,2,4,7,3,6), D(9,7,1,4,0,4,7,5,2,5,3,9,8,1,0,3,8,4,5,7,6,5,1,2,0)])))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("This 9 by 11 integer matrix has type Fin 9 → Fin 11 → Int. "
                    + "Its first row is the initial scanner distribution; each subsequent row "
                    + "is the preceding row multiplied by the boundary transfer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Gid + "w"),
                H("Boundary continuation powers"), StatementSource.FromAuthor(Disp(And(
                    All("i", Fin(11), Eq(Call(Root + "w", D(0), V("i")), D(1))),
                    All("n", Name("Nat"), All("i", Fin(11),
                        Eq(Call(Root + "w", Add(V("n"), D(1)), V("i")),
                            Seq(Sum, Underscore, Grp(V("k"), Colon, Sp, Fin(11)), Sp,
                                Parenthesized(Mul(Call(Root + "transfer", V("i"), V("k")),
                                    Call(Root + "w", V("n"), V("k"))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer-valued function w has type Nat → Fin 11 → Int. "
                    + "It starts at the constant one vector and applies the boundary transfer once per row."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Single-row certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Exact scanner fibres reduce the transition counts to 3^6 label rows. "
                    + "The single-row certificate supplies the numerical premises of the "
                    + "all-height induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Gid + "result"),
                H("The recurrence at every height"), StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The complementary-pair labels are the fibres {0,5}, {1,4}, {2,3} of "
                    + "D5.S3.Observer.Separation.BooleanRankThreeK4.beta. Exact scanner fibres "
                    + "retain the order restrictions and individual colour multiplicities. "
                    + "The first-row distribution is (16,0,16,16,16,16,16,8,8,16,8). "
                    + "The displayed matrix counts continuations from each valid boundary. "
                    + "A class-constant continuation remains class-constant after one row, "
                    + "hence after every number of rows by semiconjugacy iteration. The "
                    + "unseen sector has eigenvalue 64. The ten completed classes have "
                    + "characteristic polynomial x^3 times "
                    + "(x^7-1920x^6+1191936x^5-335020032x^4+48670703616x^3"
                    + "-3778497478656x^2+147884313935872x-2269391999729664). "
                    + "The full initial row vector is annihilated by (x-64) times that "
                    + "degree-seven cofactor. Its eighth transfer is exactly the indicated "
                    + "linear combination of its first eight distributions, coordinate by "
                    + "coordinate. Pairing this identity with any continuation height proves "
                    + "the recurrence for the literal filtered count at every n+9."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233127"),
                    ResolutionKind.Proved)))));

    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private static Formula Seen() => Name(Scanner + "Seen");
    private static Formula PairRow() => Name(BoundaryOwner + "Boundary");

    private static Formula RowCounts()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return All("s", Seen(), All("p", PairRow(), Imp(Call(Root + "Valid", s, p),
            All("k", Fin(11), Eq(Call(Root + "classCount", s, p, k),
                Call(Root + "transfer", Call(Root + "boundaryClass", s, p), k))))));
    }

    private static Formula Certificate()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        return And(RowCounts(),
            All("k", Fin(11), Eq(Call(Root + "firstCount", k),
                At(Vector(D(1,6), D(0), D(1,6), D(1,6), D(1,6), D(1,6), D(1,6), D(8), D(8),
            D(1,6), D(8)), k))));
    }

    private static Formula Result()
    {
        var n = V("n");
        Formula A(byte k) => Typed(Call(Root + "a", Add(n, D(k))), Name("Int"));
        return All("n", Name("Nat"), Eq(A(9),
            Sub(Add(Sub(Add(Sub(Add(Sub(Mul(D(1,9,8,4), A(8)), Mul(D(1,3,1,4,8,1,6), A(7))),
            Mul(D(4,1,1,3,0,3,9,3,6), A(6))), Mul(D(7,0,1,1,1,9,8,5,6,6,4), A(5))),
            Mul(D(6,8,9,3,4,2,2,5,1,0,0,8,0), A(4))), Mul(D(3,8,9,7,0,8,1,5,2,5,6,9,8,5,6),
            A(3))), Mul(D(1,1,7,3,3,9,8,8,0,9,1,6,2,5,4,7,2), A(2))),
            Mul(D(1,4,5,2,4,1,0,8,7,9,8,2,6,9,8,4,9,6), A(1)))));
    }

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
    private static Formula Numeral(byte k) => k switch
    {
        10 => D(1,0),
        11 => D(1,1),
        _ => D(k)
    };
    private static Formula Fin(byte k) => Call("Fin", Numeral(k));
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Matrix(params Formula[][] rows) => Seq(
        new Formula[] { Begin, Grp(F.Id("pmatrix")) }.Concat(rows.SelectMany((row, i) =>
            (i == 0 ? Array.Empty<Formula>() : new Formula[] { RowBreak }).Concat(
                row.SelectMany((entry, j) => j == 0 ? new[] { entry } : new[] { Amp, entry }))))
            .Concat(new Formula[] { End, Grp(F.Id("pmatrix")) }).ToArray());
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
