using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaA075885FloorGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/HannaA075885FloorGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/hanna2002a075885");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's floor-prefix sum has the positive root limit specified by its logarithmic series.",
        H("Hanna's A075885 root limit"),
        Blocks(
            Paragraph(Text("The maximal prefix product bounds the sum from below. "
                + "Multiplying that product by n+1 bounds the sum from above. "
                + "Their normalized logarithms have the same limit because log(n+1)/n tends to zero. "
                + "Counting floor quotients and dominated convergence evaluate this limit.")),
            Node("a", "The sum of prefixes", Disp(All("n", Naturals(),
                Equal(Call("a", V("n")), Add(D(1), Sum("m",
                    Call(Q("Finset", "Icc"), D(1), V("n")),
                    Product("k", Call(Q("Finset", "Icc"), D(1), V("m")),
                        Call(Q("Nat", "div"), V("n"), V("k")))))))),
                "OEIS A075885 revision 28, FORMULA (unpaginated): "
                + "\"a(n) = 1 + Sum_{m=1..n} Product_{k=1..m} floor(n/k).\" "
                + "The indices and values are natural numbers. Nat.div is integer division, hence floor(n/k) for positive k. Finset.Icc includes both endpoints. The outer empty sum gives a(0)=1, "
                + "and the source example gives a(5)=46.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("logSummand", "The source logarithmic series", Disp(All("j", Naturals(),
                Equal(Call("logSummand", V("j")), Div(
                    Call(Q("Real", "log"), Add(Cast(V("j"), Reals()), D(1))),
                    Mul(Parenthesized(Add(Cast(V("j"), Reals()), D(1))),
                        Parenthesized(Add(Cast(V("j"), Reals()), D(2)))))))),
                SourceSentence() + " The source index is j+1, so j ranges over all natural "
                + "numbers. All divisions in this formula are real divisions; its denominator "
                + "is positive.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Hanna's conjecture", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                SourceSentence() + " L is required to be positive. HasSum requires convergence "
                + "of the logarithmic series, with its source index shifted from one to j+1. "
                + "The root index n+1 ranges over exactly the positive integers; the exponent "
                + "is real and the base is the real image of a(n+1). The decimals identify the "
                + "source constant and are not extra numerical assertions.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The positive limit and its exact logarithm", Disp(ClaimBody()),
                "The logarithm of the full product is a finite sum of logarithmic increments "
                + "weighted by floor quotients. The quotient ratios converge pointwise and "
                + "the reciprocal-product series is a summable majorant. Finite summation by "
                + "parts identifies the sum with the source series. The sum/product bounds "
                + "then give convergence of normalized logarithms, and continuity of Real.exp "
                + "gives the real root limit.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static string SourceSentence() =>
        "OEIS A075885 revision 28, COMMENT (unpaginated): "
        + "\"Conjecture: limit a(n)^(1/n) = L where L = 2.200161058099... is the geometric mean "
        + "of Luroth expansions, where log(L) = Sum_{n>=1} log(n)/(n*(n+1)) = 0.7885305659115... "
        + "(cf. A085361).\"";

    private static Formula ClaimBody()
    {
        var root = new Formula.Power(Cast(Call("a", Add(V("n"), D(1))), Reals()),
            Div(D(1), Add(Cast(V("n"), Reals()), D(1))));
        return Seq(Exists, Sp, V("L"), Sp, InMacro, Sp, Reals(), Comma, Sp,
            Parenthesized(Seq(D(0), Sp, Lt, Sp, V("L"))), Sp, Land, Sp,
            Parenthesized(Call("HasSum", Lambda("j", Naturals(), Call("logSummand", V("j"))),
                Call(Q("Real", "log"), V("L")))), Sp, Land, Sp,
            Parenthesized(Call(Q("Filter", "Tendsto"), Lambda("n", Naturals(), root),
                Q("Filter", "atTop"), Call("nhds", V("L")))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("hanna-a075885-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(
        Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => Call(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula All(string name, Formula type, Formula body) => Seq(
        Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(
        V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Sum(string name, Formula range, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, range)), Sp, Parenthesized(body));
    private static Formula Product(string name, Formula range, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(V(name), Sp, InMacro, Sp, range)), Sp, Parenthesized(body));
}
