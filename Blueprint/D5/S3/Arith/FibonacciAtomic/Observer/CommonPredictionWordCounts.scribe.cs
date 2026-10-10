using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class CommonPredictionWordCountsDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Word counts, parity cancellation and coefficient capacity for common priority prediction.", H("Word Counts and Coefficient Capacity"), Blocks(
            Paragraph(Text("Window is the five-symbol alphabet zero, low, middle, ends, high. The two endpoint bits are first and last. A rare symbol is low, ends or high; rareN counts rare symbols, and highN counts high endpoints in a prefix. All words are admitted, with no seam conditioning.")),
            Paragraph(Text("The bivariate generating polynomial records both rare symbols and high endpoints. The slice with k high endpoints is choose(n,k) times (2X)^k times (2+X)^(n-k). The parity of the number of ends symbols supplies a coin. On every positive high-endpoint slice, fixing any one endpoint bit leaves equal polynomial weights for the two coin values.")),
            Paragraph(Text("A reduced word has a prefix of length m and three anchors. The reservoir requires its first anchor to be zero, middle or high, its second anchor to be high, and its third anchor to be low or ends. Every left-layer teacher has label zero there and every right-layer teacher has label two. Nz(m,z) counts reservoir words with exactly z rare symbols.")),
            Paragraph(Text("The binomial weights choose(j,k) times 2 to the k have total 3 to the j and first moment 2j times 3 to the j-1. The truncated tail at floor(m/3) satisfies a strengthened moment estimate and grows by at least a factor of three when the degree increases. These relations bound the signed discrepancy coefficients on both sides by the reservoir coefficients, including m=1 and m=2.")),
            Describe.Lean(DescribeId.Create("word-counts"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.integer_split_positive"),
                H("Integer reservoir capacity"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reservoir and discrepancy half coefficients are integers. Their two-sided bound makes the half difference a nonnegative integer, at most the complete reservoir coefficient. This supplies a legal split size in every rare-count class. Prefix and anchor generating functions identify the coefficients with actual word counts."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var capacity = Le(Call("int", V("t")),
            Seq(D(2), Cdot, Call("reservoir-half", V("m"), V("z"))));
        var balance = Eq(Seq(D(2), Cdot,
            Call("discrepancy-half", V("m"), V("z")), Minus, D(2), Cdot,
            Call("reservoir-half", V("m"), V("z")), Plus, D(2), Cdot,
            Call("int", V("t"))), D(0));
        return All("m", V("Nat"), All("z", V("Nat"),
            Imp(Seq(D(0), Sp, Lt, Sp, V("m")),
                Ex("t", V("Nat"), And(capacity, balance)))));
    }
}
