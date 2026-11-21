using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ActiveOrbitBudgetDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The active orbit columns determine the eventual period of finite equivariant realizations.",
        H("Exact rational event budgets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-uniform-event-budgets"),
                DeclarationHandle.Create(Result),
                H("The eventual period of uniform event budgets"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A group acts on a finite target T. A finite family of events "
                        + "E(i) has prescribed rational masses q(i). Some event is all of T and "
                        + "has prescribed mass one. Assume the orbit event matrix A has a real "
                        + "nonnegative solution of A x = q, with A(i,O) the number of elements "
                        + "of orbit O in event E(i).")),
                    Paragraph(Text("Let m be the least common multiple of the reduced denominators. "
                        + "There is an integer vector w with w = m q. An orbit is active if its "
                        + "coordinate is positive in some nonnegative real solution of A x = w. "
                        + "Let M be the integer additive map formed by the active columns and h be "
                        + "the additive order of the class of w modulo the range of M.")),
                    Paragraph(Text("D consists of the positive seed budgets. A budget is realized "
                        + "by a finite seed set of that size with a group action and an equivariant "
                        + "map to T. The fraction of seeds mapping to each event is its prescribed "
                        + "mass. Each subgroup fixes a seed exactly when it fixes that seed's image.")),
                    Paragraph(Text("Average a feasible vector with witnesses for all active "
                        + "coordinates. Scaling that average and subtracting one at each active "
                        + "coordinate leaves a feasible system with integral right-hand side. "
                        + "The integer optimizer gives a scaled integral solution for this shifted "
                        + "system. Adding back the shift gives a strictly positive integer witness. "
                        + "The integer fiber theorem supplies the order and the eventual tail. "
                        + "The normalization event counts the entire seed set."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula w = F.Id("w");
        Formula m = F.Id("m");
        Formula q = F.Id("q");
        Formula h = F.Id("h");
        Formula n = F.Id("N");
        Formula t = F.Id("t");
        Formula c = F.Id("C");
        Formula d = F.Id("D");

        return Disp(Seq(
            Exists, Sp, w, Comma, Sp, w, Sp, Eq, Sp, m, q, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, h, Sp, Land, Sp,
            Open, Forall, Sp, n, Sp, InMacro, Sp, d, Comma, Sp,
            m, h, Sp, Mid, Sp, n, Close, Sp, Land, Sp,
            Open, Exists, Sp, c, Comma, Sp, Forall, Sp, t, Comma, Sp,
            D(0), Sp, Lt, Sp, t, Sp, Land, Sp, c, Sp, Leq, Sp, t, Sp, Rightarrow, Sp,
            m, h, t, Sp, InMacro, Sp, d, Close));
    }
}
