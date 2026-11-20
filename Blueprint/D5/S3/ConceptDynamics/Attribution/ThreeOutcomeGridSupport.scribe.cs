using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ThreeOutcomeGridSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp seed budget for exact three-outcome calibration with label symmetries.",
        H("Seed budgets for covariant three-outcome calibration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-outcome-calibrating-law"),
                DeclarationHandle.Create(Prefix + "CalibratingLaw"),
                H("Calibrating law on a three-outcome grid"),
                StatementSource.FromAuthor(Disp(Call("CalibratingLaw", F.Id("S"), F.Id("w"), F.Id("f")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Profiles are triples of nonnegative integer coordinates with sum six times q. "
                    + "The finite seed set S carries an action of the permutation group on three labels. "
                    + "The real weights w are strictly positive, sum to one, and are invariant under this action. "
                    + "The deterministic readout f assigns each profile and seed to one label. Each label's mass "
                    + "equals its profile coordinate divided by six times q. Simultaneously permuting the profile "
                    + "and seed takes the readout to the permuted label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-outcome-grid-support-budget"),
                DeclarationHandle.Create(Prefix + "triple_grid_support_budget_iff"),
                H("Sharp three-outcome support budget"),
                StatementSource.FromAuthor(BudgetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive q and a natural budget n, a calibrating law exists on at most six times n "
                        + "seeds exactly when four to the power n is at least three times q plus one.")),
                    Paragraph(Text(
                        "A permutation that fixes a seed must fix the readout at the uniform profile. A nonidentity "
                        + "permutation of three labels has at most one fixed label. At the profile with zero weight on "
                        + "that label and equal weights on the other two, the seed would have to return the zero-mass "
                        + "label. Positivity then gives a contradiction. Each seed orbit therefore has six elements. "
                        + "A transposition at a profile with two equal coordinates gives equal label counts within "
                        + "each orbit, limiting either count to the four values from zero through three.")),
                    Paragraph(Text(
                        "The construction grows integer orbit weights with the bounded-digit constraint from "
                        + "complete partitions. Adding six seeds of a new weight preserves all ordered triple "
                        + "allocations, because the three integer capacities after division by the new weight "
                        + "have sum at least six. The same weights represent all tied-coordinate masses with "
                        + "four occupancy digits. The uniform profile uses the same count for all three labels "
                        + "in each orbit. Stabilizer-compatible readouts at representative profiles extend by "
                        + "permuting both inputs. Normalize the positive weights by the denominator.")),
                    Paragraph(Text(
                        "The seed law is an input. The statement concerns a finite probability grid that includes "
                        + "zero coordinates and uses a denominator divisible by six."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula BudgetStatement()
    {
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        return Disp(Seq(Forall, Sp, q, Sp, n, Comma, Sp, D(0), Sp, Lt, Sp, q, Sp, Rightarrow, Sp,
            Open, Call("SeedBudget", Seq(D(6), Sp, Cdot, Sp, q), Seq(D(6), Sp, Cdot, Sp, n)),
            Sp, Iff, Sp, D(3), Sp, Cdot, Sp, q, Sp, Plus, Sp, D(1), Sp, Le, Sp, D(4), Caret, n, Close));
    }
}
