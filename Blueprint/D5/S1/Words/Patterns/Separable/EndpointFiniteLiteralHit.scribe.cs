using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointFiniteLiteralHitDocument : IScribeDocumentDefinition
{
    private static Formula Offset => F.Id("e");
    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");
    private static Formula A => F.Id("a");
    private static Formula Probability => Call("P", Offset, N);
    private static Formula Statement => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Open, Forall, Sp, K, Comma, A, Comma, Sp, A, Lt,
        Call("firstKHitProbability", K, Offset), Longrightarrow, Sp,
        Call("Eventually", Seq(N, Mapsto, Sp, A, Lt, Probability)), Close, Sp, Land,
        RowBreak, Grp(),
        Open, Call("StreamHitsAlmostSurely", Offset), Longrightarrow, Sp,
        Lim, Underscore, Grp(N, To, Infty), Probability, Eq, D(1), Close,
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual fixed-prefix hit transfers to the whole original finite permutation.",
        H("Whole-permutation diagonal hits from fixed marked prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("whole-finite-literal-hit-probability"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.literalHitProbability"),
                H("Actual finite literal hit probability"),
                StatementSource.FromAuthor(Disp(Seq(Probability, Eq, Call("actualMass", N,
                    Call("hitsDiagonal", Offset))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P(e,n) is the actual uniform mass of length-n avoiding permutations having at least one original-coordinate point whose position minus value is the fixed integer e. The event is inspected on the original permutation, not on a parsed cycle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-literal-hit-limit-of-stream-hit"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointFiniteLiteralHit.finite_avoider_literal_hit_limit_of_stream_hit"),
                H("Fixed-prefix lower bounds and conditional probability-one limit"),
                StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For fixed e and every natural prefix length k, the first conjunct gives an eventual strict lower bound at each real a below the stream's first-k probability. The second assumes that almost every stream eventually has a marked-cycle hit at e plus the preceding discrepancy; it does not prove that premise.")),
                    Paragraph(Text("A successful finite-prefix hit already exhibits an original coordinate witnessing the whole-permutation event, and uniform outer mass is monotone. The first-k stream events increase to the event of any marked hit. Given a tolerance, first choose a single k from the stream law; only then send n to infinity using the fixed-prefix limit. The full mass is at most one. There is no growing offset, joint k,n limit, rate, or multiplicity claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
