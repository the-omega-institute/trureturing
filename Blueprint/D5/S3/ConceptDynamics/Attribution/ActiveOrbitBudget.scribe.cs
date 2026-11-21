using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ActiveOrbitBudgetDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/ConceptDynamics/Attribution/ActiveOrbitBudget.eventual_uniform_event_budgets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The active orbit columns classify exact finite equivariant budgets and give a sufficient cutoff.",
        H("Exact rational event budgets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-uniform-event-budgets"),
                DeclarationHandle.Create(Result),
                H("Exact uniform event budgets and their eventual period"),
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
                    Paragraph(Text("For each positive budget N, the equation uses a natural degree k "
                        + "and a nonnegative integer vector n on the active orbit set J. "
                        + "Every realized budget is divisible by m h.")),
                    Paragraph(Text("A positive degree B admits an integer vector p that is strictly "
                        + "positive on J. Write B = h b. There exists a signed integer vector u "
                        + "with M u = h w. For each such u the displayed cutoff applies to every "
                        + "positive normalized degree t.")),
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
        Formula k = F.Id("k");
        Formula v = F.Id("n");
        Formula b = F.Id("b");
        Formula degree = F.Id("B");
        Formula p = F.Id("p");
        Formula u = F.Id("u");
        Formula t = F.Id("t");
        Formula d = F.Id("D");
        Formula j = F.Id("j");
        Formula map = F.Id("M");
        Formula signed = Seq(map, u, Sp, Eq, Sp, h, w);

        return Disp(new Formula.Aligned([
            Seq(Exists, Sp, w, Comma, Sp, w, Sp, Eq, Sp, m, q, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, h, Sp, Land),
            Seq(Open, Forall, Sp, n, Sp, Gt, Sp, D(0), Comma, Sp, n, Sp, InMacro, Sp, d,
                Sp, Iff, Sp, Exists, Sp, k, Comma, Sp, v, Comma, Sp, n, Sp, Eq, Sp, m, k,
                Sp, Land, Sp, v, Sp, Geq, Sp, D(0), Sp, Land, Sp, map, v, Sp, Eq, Sp, k, w,
                Close, Sp, Land),
            Seq(Open, Forall, Sp, n, Sp, InMacro, Sp, d, Comma, Sp, m, h, Sp, Mid, Sp, n,
                Close, Sp, Land),
            Seq(Open, Exists, Sp, degree, Comma, Sp, p, Comma, Sp, b, Comma, Sp,
                D(0), Sp, Lt, Sp, degree, Sp, Land, Sp, D(0), Sp, Lt, Sp, p, Sp, Land, Sp,
                map, p, Sp, Eq, Sp, degree, w, Sp, Land, Sp, degree, Sp, Eq, Sp, h, b, Sp, Land),
            Seq(Open, Exists, Sp, u, Comma, Sp, signed, Close, Sp, Land, Sp,
                Open, Forall, Sp, u, Comma, Sp, signed, Sp, Rightarrow, Sp,
                Forall, Sp, t, Sp, Gt, Sp, D(0), Comma, Sp),
            Seq(Open, b, Minus, D(1), Close, b, Open, D(1), Sp, Plus, Sp,
                new Formula.Subscript(Sum, j), Sp, Vert, Sp, new Formula.Subscript(u, j), Vert, Close,
                Sp, Leq, Sp, t, Sp, Rightarrow, Sp, m, h, t, Sp, InMacro, Sp, d, Close, Close)
        ]));
    }
}
