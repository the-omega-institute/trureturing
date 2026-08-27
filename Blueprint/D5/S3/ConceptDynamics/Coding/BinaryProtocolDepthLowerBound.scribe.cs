using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class BinaryProtocolDepthLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identifying a target by adaptive binary questions requires logarithmic fiber depth.",
        H("Adaptive Binary Protocol Depth Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adaptive-binary-protocol-depth-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound."
                        + "adaptive_binary_protocol_depth_lower_bound"),
                H("Binary identification depth is bounded below by fiber diversity"),
                StatementSource.FromAuthor(DepthLowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The current concept partitions the finite state carrier into fibers. "
                            + "Worst fiber diversity is the greatest number of distinct target "
                            + "values realized inside any one of those fibers.")),
                    Paragraph(Text(
                        "A depth-d adaptive binary protocol records one bit per round. It "
                            + "identifies the target when equal current records and equal full "
                            + "transcripts force equal target values.")),
                    Paragraph(Text(
                        "Reading every transcript bit as a fixed-width auxiliary label makes "
                            + "that label target-determining. The least-label theorem then "
                            + "forces d to be at least the ceiling logarithm to base two of "
                            + "worst fiber diversity."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula DepthLowerBoundFormula()
    {
        Formula state = F.Id("X");
        Formula currentCarrier = F.Id("C");
        Formula targetCarrier = F.Id("Target");
        Formula current = F.Id("c");
        Formula target = F.Id("t");
        Formula depth = F.Id("d");
        Formula protocol = F.Id("pi");
        Formula identifies = F.Id("identifies");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula diversity = Call("worstFiberDiversity", current, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, currentCarrier, Comma, Sp, targetCarrier,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Fintype(state), Comma, Sp, Fintype(currentCarrier), Comma, RowBreak, Grp(),
            current, Colon, Sp, Call("Concept", state, currentCarrier), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetCarrier), Comma,
            RowBreak, Grp(),
            depth, Colon, Sp, naturalNumbers, Comma, Sp,
            protocol, Colon, Sp, Call("BinaryProtocol", state, depth), Comma,
            RowBreak, Grp(),
            identifies, Colon, Sp, Call("IdentifiesGiven", current, target, protocol),
            Comma, RowBreak, Grp(),
            Call("clog", D(2), diversity), Sp, Leq, Sp, depth, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
