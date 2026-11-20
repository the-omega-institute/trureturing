using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class CommonBlockWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common weight families for integer and fractional grouped demands.",
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
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-weights-with-fractional-bundles"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/CommonBlockWeights.common_fractional_allocations"),
                H("A fractional weight can be allocated in bundles"),
                StatementSource.FromAuthor(FractionalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All scalar parameters are natural numbers. FractionalWeights(k,n,A,b) "
                        + "means there exist n plus one natural weights, of total A, with the following "
                        + "simultaneous allocation property. For every positive number t of groups, "
                        + "every U divisible by b and at least k times the predecessor of t, and every "
                        + "natural demand vector x with b times its total equal to U times A, there is "
                        + "an allocation of U copies of every weight. The mass assigned to each group "
                        + "is b times its demand.")),
                    Paragraph(Text(
                        "Take T to be the smaller of the integer part of A divided by b and the sum "
                        + "of the first n powers of k plus one, starting with power zero. The capacity "
                        + "inequality makes the remaining weight A minus b times T small enough to "
                        + "allocate its U copies in bundles of b. Each bundle pays an integer demand "
                        + "in units of b. The remainder is covered by the common integer weight family "
                        + "of total T, scaled by b. The weights are chosen before the group demands."))),
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

    private static Formula FractionalStatement()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula a = F.Id("A");
        Formula b = F.Id("b");
        Formula factor = F.Id("K");
        return Disp(Seq(Forall, Sp, k, Sp, n, Sp, a, Sp, b, Sp, factor, Comma, Sp,
            D(0), Sp, Lt, Sp, k, Sp, Land, Sp, D(0), Sp, Lt, Sp, b, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, factor, Sp, Land, Sp, factor, Cdot, Sp, b, Sp, Eq, Sp, k, Sp,
            Land, Sp, b, Sp, Le, Sp, a, Sp, Land, Sp,
            new Formula.FunctionCall(FormulaIdentifier.Create("DoesNotDivide"), [b, a]), Sp, Land, Sp,
            factor, Cdot, Sp, a, Plus, D(1), Sp, Le, Sp,
            Open, factor, Plus, D(1), Close, Cdot, Open, k, Plus, D(1), Close, Caret, n, Sp,
            Rightarrow, Sp, new Formula.FunctionCall(FormulaIdentifier.Create("FractionalWeights"), [k, n, a, b])));
    }
}
