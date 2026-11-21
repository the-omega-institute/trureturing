using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class CovariantGridSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/CovariantGridSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite seed budgets for covariant binary calibration.",
        H("Seed budgets for covariant binary calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("covariant-grid"), DeclarationHandle.Create(Prefix + "CovariantGrid"),
                H("Covariant binary grid"),
                StatementSource.FromAuthor(Disp(Call("CovariantGrid", F.Id("m"), F.Id("S")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural denominator m and finite seed type S, a covariant grid specifies "
                    + "nonnegative real weights with sum one, a weight-preserving involution, and one "
                    + "event of mass k divided by m for each index k from zero through m. The involution "
                    + "takes the event at k to the complement of the event at m minus k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-support-budget"),
                DeclarationHandle.Create(Prefix + "odd_support_budget_iff"),
                H("Odd denominators"),
                StatementSource.FromAuthor(OddStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If m is odd and n is a natural budget, a covariant grid exists on at most n seeds "
                    + "if and only if 2 to the power n is at least m plus one. Different levels require "
                    + "different events, so the number of subsets gives the lower bound. Binary place "
                    + "weights, with a final weight chosen to make the sum correct, realize every level. "
                    + "Use the identity involution and pair a lower event with its complement above the midpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-support-budget"),
                DeclarationHandle.Create(Prefix + "even_support_budget_iff"),
                H("Even denominators"),
                StatementSource.FromAuthor(EvenStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If q is positive and r is a natural budget for the number of seed pairs, a "
                        + "covariant grid with denominator twice q exists on at most twice r seeds if and "
                        + "only if 3 to the power r is at least twice q plus one.")),
                    Paragraph(Text(
                        "The midpoint event gives exactly one representative of each two-element orbit. "
                        + "An event's mass is determined by the number of representatives and partners it "
                        + "contains from each orbit. Ternary place weights, with the final weight chosen "
                        + "to make the sum correct, realize every level when each weight is supplied twice. "
                        + "Swap the two seeds in each pair. The midpoint chooses one per pair.")),
                    Paragraph(Text(
                        "The bounded-digit construction is the complete-partition step of Bachet's "
                        + "weighing problem. The seed weights are inputs to the calibration model."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula GridBudget(Formula denominator, Formula budget)
    {
        Formula seeds = F.Id("S");
        return Seq(Open, Exists, Sp, seeds, Colon, F.Id("Type"), Sp,
            OpenBracket, Call("Fintype", seeds), CloseBracket, Comma, Sp,
            Call("card", seeds), Sp, Le, Sp, budget, Sp, Land, Sp,
            Call("Nonempty", Call("CovariantGrid", denominator, seeds)), Close);
    }

    private static Formula OddStatement()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        return Disp(Seq(Forall, Sp, m, Sp, n, Comma, Sp, Call("Odd", m), Sp, Rightarrow, Sp,
            Open, GridBudget(m, n), Sp, Iff, Sp, m, Sp, Plus, Sp, D(1), Sp, Le, Sp, D(2), Caret, n, Close));
    }

    private static Formula EvenStatement()
    {
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula denominator = Seq(D(2), Sp, Cdot, Sp, q);
        Formula budget = Seq(D(2), Sp, Cdot, Sp, r);
        return Disp(Seq(Forall, Sp, q, Sp, r, Comma, Sp, D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            Open, GridBudget(denominator, budget), Sp, Iff, Sp, denominator, Sp, Plus, Sp,
            D(1), Sp, Le, Sp, D(3), Caret, r, Close));
    }
}
