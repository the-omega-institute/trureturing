using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenFutureEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenFutureEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum priced divisor benefit over positive multiples is the least upper "
            + "envelope that decreases under multiplication by a prime.",
        H("Golden Future Envelope"),
        Blocks(
            Paragraph(Text(
                "For a positive real price lambda, let goldenResourceObjective(lambda,n) "
                    + "be log(sigma(n)/n) minus lambda times log(n) on positive integers. "
                    + "Define goldenFutureEnvelope(lambda,n) as the supremum of these "
                    + "objectives over all positive multiples of n. This supremum is attained "
                    + "by a positive multiple, so it is a maximum.")),
            Describe.Lean(
                DescribeId.Create("golden-future-envelope-least"),
                DeclarationHandle.Create(Prefix + "golden_future_envelope_least"),
                H("The least safe envelope"),
                StatementSource.FromAuthor(LeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Prime(p) means that p is a prime natural number. The envelope "
                            + "majorizes the current objective and does not increase "
                            + "when any prime is multiplied into a positive integer. Every "
                            + "other function with both properties is at least this envelope "
                            + "at every positive integer.")),
                    Paragraph(Text(
                        "If n divides a positive integer m, write m=nq. Induction over the "
                            + "prime factors of q extends the prime-step inequality to "
                            + "U(m)<=U(n). At a maximizing multiple m, the objective is at "
                            + "most U(m), hence at most U(n). Self-majorization follows by "
                            + "including n among its own multiples, and envelope monotonicity "
                            + "follows by inclusion of the sets of positive multiples.")),
                    Paragraph(Text(
                        "The domain includes all positive integers and all prime factors, "
                            + "with no restriction on the order in which factors are multiplied."))),
                DescribeRole.Theorem))));

    private static Formula LeastFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula u = F.Id("U");
        Formula Envelope(Formula x) => Call("goldenFutureEnvelope", lambda, x);
        Formula Objective(Formula x) => Call("goldenResourceObjective", lambda, x);
        Formula Major(Func<Formula, Formula> f) => ForAll(
            [Bound("n", Naturals())], Implies(Le(D(1), n), Le(Objective(n), f(n))));
        Formula Step(Func<Formula, Formula> f) => ForAll(
            [Bound("p", Naturals())], Implies(Call("Prime", p), ForAll(
                [Bound("n", Naturals())], Implies(Le(D(1), n), Le(f(Multiply(p, n)), f(n))))));
        Formula ApplyU(Formula x) => new Formula.Apply(u, [x]);
        Formula least = ForAll(
            [Bound("U", Seq(Open, Naturals(), Sp, To, Sp, Reals(), Close))],
            Implies(Major(ApplyU), Implies(Step(ApplyU), ForAll(
                [Bound("n", Naturals())], Implies(Le(D(1), n), Le(Envelope(n), ApplyU(n)))))));
        return Disp(ForAll([Bound("lambda", Reals())], Implies(Lt(D(0), lambda),
            And(Major(Envelope), And(Step(Envelope), least)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
