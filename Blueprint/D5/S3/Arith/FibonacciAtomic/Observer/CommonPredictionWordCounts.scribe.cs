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
        "Exact word counts and parity cancellation for the two-layer priority-teacher model.", H("Word Counts for Common Priority Prediction"), Blocks(
            Paragraph(Text("Window is the five-symbol alphabet zero, low, middle, ends, high. The two endpoint bits are first and last. A rare symbol is low, ends or high; rareN counts rare symbols, and highN counts high endpoints in a prefix. All words are admitted, with no seam conditioning.")),
            Paragraph(Text("The bivariate generating polynomial records both rare symbols and high endpoints. The slice with k high endpoints is choose(n,k) times (2X)^k times (2+X)^(n-k). The parity of the number of ends symbols supplies a coin. On every positive high-endpoint slice, fixing any one endpoint bit leaves equal polynomial weights for the two coin values.")),
            Paragraph(Text("A reduced word has a prefix of length m and three anchors. The reservoir requires its first anchor to be zero, middle or high, its second anchor to be high, and its third anchor to be low or ends. Every left-layer teacher has label zero there and every right-layer teacher has label two. Nz(m,z) counts reservoir words with exactly z rare symbols.")),
            Paragraph(Text("The majority selector compares the votes of the three labels. Its choice depends on the number of high endpoints, the three anchors and a tie coin. The seven nonzero regions, together with the zero region, exhaust every positive m and every prefix count from zero through m. These identities hold for arbitrary prefix lengths.")),
            Describe.Lean(DescribeId.Create("word-counts"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.actual_nz_identity"),
                H("Exact reservoir class cardinalities"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Separating prefix and anchor coordinates gives the reservoir polynomial 2 X squared times (2+X) times (2+3X) to the m. Taking its coefficient at z counts precisely the actual reservoir words of that mass class. The signed generating polynomial cancels the high-endpoint contribution; this is the parity balance used to integrate tied majority choices."))), DescribeRole.Theorem))));

    private static Formula ResultFormula() =>
        All("m", V("Nat"), All("z", V("Nat"),
            Eq(Call("Nz", V("m"), V("z")),
                Call("coeff", Call("ReservoirPolynomial", V("m")), V("z")))));
}
