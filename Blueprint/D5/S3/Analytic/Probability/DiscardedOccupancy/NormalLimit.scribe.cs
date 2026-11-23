using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability.DiscardedOccupancy;

internal sealed class DiscardedOccupancyNormalLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The count of distinct ordinary bins hit has a standard Gaussian weak limit after exact row standardization.",
        H("Gaussian limit for occupancy with discarded throws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("occupancy-limit"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit"),
                H("Gaussian limit of literal occupancy"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Row N has N plus one ordinary bins and N independent throws. The ordinary-bin masses are one divided by k times the number of bins, and each remaining mass belongs to the discard outcome. Standardization uses the expectation and variance under the product measure in that row. The proof telescopes the conditional characteristic-function comparisons and applies Lévy continuity."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var k = F.Id("k");
        var n = F.Id("N");
        var rows = Lam("N", Nat, Call("literalLaw", k, n));
        var convergence = Call("Tendsto", rows, F.Id("atTop"),
            Call("nhds", Call("gaussianReal", D(0), D(1))));
        return All("k", Nat, Seq(D(2), Sp, Leq, Sp, k, Sp, Implies, Sp, convergence));
    }

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(Open, F.Id(x), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
}
