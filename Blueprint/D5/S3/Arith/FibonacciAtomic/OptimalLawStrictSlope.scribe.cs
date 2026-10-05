using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawStrictSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var m = F.Id("m");
        var natural = Seq(Mathbb, Grp(F.Id("N")));
        var predecessor = Seq(Open, m, Sp, Minus, Sp, D(1), Close);
        var statement = Seq(
            Equal(Call("alpha", D(1)), D(0)), Sp, Land, Sp,
            Equal(Call("alpha", D(2)), D(2)), Sp, Land, Sp,
            Open, Forall, Sp, m, Colon, Sp, natural, Comma, Sp,
            Open, D(3), Sp, Le, Sp, m, Close, Sp, To, Sp,
            Call("alpha", predecessor), Sp, Lt, Sp, Call("alpha", m), Close);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The minimum ratio of dyadic sampling cost to least atom mass grows strictly with the label count.",
            H("Strict Growth of the Optimal Real-law Slope"), Blocks(
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope.result"),
                    H("Strict growth with the number of labels"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For a strictly positive normalized real law p on m labels, the dyadic cost is the sum over depths d of the unassigned floor remainder divided by 2^d. The function alpha is the infimum of this cost divided by the smallest mass, as defined by CarryGraphCriticalAttainment. The domain contains all such real laws, without a rationality or finite-depth restriction.")),
                        Paragraph(Text("A single label has zero cost. For two labels, the cost is at least one and the smallest mass is at most one half. The uniform two-label law has cost one and attains ratio two.")),
                        Paragraph(Text("Take an attaining law with at least three labels. Merging two atoms never increases any floor remainder. If the smallest atom is unique, merging it with another atom strictly raises the new minimum mass. If two atoms have the same smallest mass, their first positive binary digit produces a strict carry one depth earlier, so merging them strictly reduces the convergent cost sum. In each case the new law has a strictly smaller ratio, proving the strict inequality for consecutive label counts.")))))));
    }
}
