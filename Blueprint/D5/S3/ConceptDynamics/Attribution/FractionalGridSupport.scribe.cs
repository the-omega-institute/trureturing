using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FractionalGridSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/FractionalGridSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact seed budgets with fractional orbit weights on permutation-equivariant probability grids.",
        H("Fractional orbit weights on finite probability grids"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fractional-permutation-grid-budget"),
                DeclarationHandle.Create(Prefix + "fractional_grid_budget_iff"),
                H("Sharp support budget when the scaled weights may be fractional"),
                StatementSource.FromAuthor(FractionalBudgetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take at least two labels and a positive natural number q. The denominator "
                        + "m is (k minus one) times q. PrimeDivisibility means every prime at most k "
                        + "divides m. The budget is k factorial times n plus one, with n plus one "
                        + "as the upper bound on the number of orbits. SeedBudget uses the same shared calibrating law.")),
                    Paragraph(Text(
                        "The prime-cycle test forces regular seed orbits. Profiles with k minus one "
                        + "tied labels require all q plus one integer levels. The weights of the "
                        + "orbit digits sum to q divided by k. Its reduced denominator is k divided "
                        + "by the greatest common divisor of k and q. Apply the integer-level "
                        + "capacity bound to these weights and the tied profiles.")),
                    Paragraph(Text(
                        "For attainment, write q divided by k as A divided by b in lowest terms. "
                        + "Use the common fractional allocation construction with numerator total A "
                        + "and denominator b. For every profile, the integer group demands and the "
                        + "number of blocks satisfy the allocation balance. The stabilizer readout "
                        + "and transport along profile orbits then give one equivariant law. "
                        + "With eight labels and q equal to 210 or 270, the greatest common divisor "
                        + "is two. The first feasible budgets use three and four regular orbits, "
                        + "respectively, giving support sizes 120960 and 161280."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula FractionalBudgetStatement()
    {
        Formula k = F.Id("k");
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula denominator = Seq(Open, k, Minus, D(1), Close, Cdot, Sp, q);
        Formula budget = Seq(Call("factorial", k), Cdot, Open, n, Plus, D(1), Close);
        return Disp(Seq(Forall, Sp, k, Sp, q, Sp, n, Comma, Sp,
            D(2), Sp, Le, Sp, k, Sp, Land, Sp, D(0), Sp, Lt, Sp, q, Sp, Land, Sp,
            Call("PrimeDivisibility", k, denominator), Sp, Rightarrow, Sp,
            Open, Call("SeedBudget", k, denominator, budget), Sp, Iff, Sp,
            q, Plus, D(1), Sp, Le, Sp, Open, Call("gcd", k, q), Plus, D(1), Close, Cdot,
            Open, k, Plus, D(1), Close, Caret, n, Close));
    }
}
