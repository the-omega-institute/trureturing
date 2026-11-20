using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class CommonBlockWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One integer weight family for all compatible grouped allocations.",
        H("Common weights for grouped allocations"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-weights-for-grouped-allocations"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_weights_for_allocations"),
            H("The digit budget gives one weight family for all compatible allocations"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let k be a positive natural number, and let n and q be natural numbers. "
                    + "CommonWeights(k,n,q) means there exist n natural weights with total q. "
                    + "For every positive number t of groups, every nonnegative natural U with "
                    + "U at least k times the predecessor of t, and every natural demand vector "
                    + "with total U times q, the same weights admit an allocation. Each weight "
                    + "has U identical copies to distribute, and each group must receive exactly its demand.")),
                Paragraph(Text(
                    "Choose powers of k plus one and clip at total q. If d is the next positive "
                    + "weight and T is the earlier total, then d minus one is at most k times T. "
                    + "The residual capacity after dividing the group demands by d and rounding "
                    + "down can discard at most t times d minus t units of mass. A total capacity "
                    + "below U would contradict the lower bound on U times T. After allocating "
                    + "the new copies, use the earlier weights for the remaining demands.")),
                Paragraph(Text(
                    "The scalar growth condition comes from Rødseth, Minimal r-Complete Partitions, "
                    + "Journal of Integer Sequences 10 (2007), Article 07.8.3, Lemmas 3.1–3.2."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        return Disp(Seq(Forall, Sp, k, Sp, n, Sp, q, Comma, Sp,
            D(0), Sp, Lt, Sp, k, Sp, Land, Sp,
            k, Cdot, Sp, q, Plus, D(1), Sp, Le, Sp, Open, k, Plus, D(1), Close, Caret, n,
            Sp, Rightarrow, Sp, new Formula.FunctionCall(FormulaIdentifier.Create("CommonWeights"), [k, n, q])));
    }
}
