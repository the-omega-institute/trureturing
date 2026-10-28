using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class EndpointShuffleSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/EndpointShuffleSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An endpoint-gap rectangle injects into distinct ordinary self-shuffle words.",
        H("Endpoint Gaps in Distinct Shuffle Support"),
        Blocks(
            Paragraph(Text("Represent zero by false and one by true. Ordinary shuffles may take "
                + "the next symbol from either source, preserving each source's internal order. "
                + "The list ordinaryShuffles retains schedule multiplicities; conversion to a "
                + "finite set discards them. All cardinalities below count output words.")),
            Node("endpointWord", "Two endpoint ones", DescribeRole.Definition,
                Equal(Call("endpointWord", F.Id("m")),
                    Call("concat", F.Id("one"), Call("zeros", F.Id("m")), F.Id("one"))),
                "The word consists of an initial one, m zeros and a final one. The value m=0 is allowed."),
            Node("endpointOutput", "Words parametrized by their outer gaps", DescribeRole.Definition,
                Equal(Call("endpointOutput", F.Id("m"), F.Id("a"), F.Id("c")),
                    Call("gap", F.Id("zero"), Call("list", Num(1), Num(1), Num(1), Num(1)),
                        Call("list", Num(0), F.Id("a"),
                            Add(Subtract(F.Id("m"), F.Id("a")), Subtract(F.Id("m"), F.Id("c"))),
                            F.Id("c"), Num(0)))),
                "The five zero gaps around four ones are 0, a, (m-a)+(m-c), c and 0. "
                + "When a and c are at most m, the total number of zeros is 2m."),
            Node("endpointFamily", "The finite rectangle of output words", DescribeRole.Definition,
                Equal(Call("endpointFamily", F.Id("m")),
                    Call("image", F.Id("endpointOutput"), Call("square", Call("Fin", Add(F.Id("m"), Num(1)))))),
                "Take the image of Fin(m+1) times Fin(m+1) under the output map. "
                + "This is a finite set of words, rather than a set of schedules."),
            Node("endpointOutput_mem", "Constructing every outer-gap pair", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, F.Id("a"), Comma, F.Id("c"), Comma, Sp,
                    AtMost(F.Id("a"), F.Id("m")), Land, AtMost(F.Id("c"), F.Id("m")), Implies,
                    Call("member", Call("endpointOutput", F.Id("m"), F.Id("a"), F.Id("c")),
                        Call("ordinaryShuffles", Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m"))))),
                "Label the copies A and B. Read A for its initial one and a zeros, then B's "
                + "initial one, then the remaining m-a zeros from A and m-c zeros from B, "
                + "then A's last one, and finally B's c zeros and last one. Both source "
                + "orders are preserved, including when any of these zero blocks is empty."),
            Node("endpointFamily_card", "Distinct parameter pairs give distinct words", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    Equal(Call("card", Call("endpointFamily", F.Id("m"))), Power(Add(F.Id("m"), Num(1)), Num(2)))),
                "The existing uniqueness theorem for unary-gap words recovers the outer gaps "
                + "from the resulting word. Thus the output map is injective and its finite "
                + "image has (m+1)^2 elements."),
            Node("endpoint_self_shuffle_card_lower", "A universal lower bound for distinct support", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    AtMost(Power(Add(F.Id("m"), Num(1)), Num(2)),
                        Call("card", Call("toFinset", Call("ordinaryShuffles",
                            Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m"))))))),
                "Every word in the parameter image belongs to the actual self-shuffle support. "
                + "Inclusion and the image cardinality give the displayed lower bound."),
            Paragraph(Text("The reverse inclusion of all self-shuffle outputs in the outer-gap "
                + "rectangle is a separate assertion. Equality of the support cardinality, "
                + "the ordinary-binary-numeral bridge for 2^k+1, and the eventual identity "
                + "for A193020 are not conclusions of these statements.")))));

    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);

    private static DocumentBlock.Describe Node(string declaration, string title,
        DescribeRole role, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("endpoint-shuffle-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
