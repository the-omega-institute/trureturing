using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class FibonacciNearReturnDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci times return the inverse-golden circle rotation with exact alternating defect.",
        H("Fibonacci Near Return"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-times-have-exact-alternating-return-defect"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn."
                        + "fibonacci_near_return"),
                H("Fibonacci times have exact alternating return defect"),
                StatementSource.FromAuthor(NearReturnFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the additive circle modulo one, goldenRotation adds the reciprocal "
                            + "golden ratio. The real return defect at n is constructed as "
                            + "fib(n) divided by the golden ratio minus fib(n-1); it is not "
                            + "defined by the alternating-power conclusion.")),
                    Paragraph(Text(
                        "For every positive Fibonacci index, the corresponding iterate is "
                            + "translation by that defect. The same public theorem gives its exact "
                            + "alternating inverse-golden form, its absolute value, convergence of "
                            + "the absolute defects to zero, and its alternating sign.")),
                    Paragraph(Text(
                        "The proof applies the frozen D5 Fibonacci golden residual. Pinned Mathlib "
                            + "supplies additive-translation iterates, the additive-circle quotient "
                            + "criterion, geometric-power convergence, and sign multiplication. "
                            + "Searches found no exact theorem combining all five clauses.")),
                    Paragraph(Text(
                        "The source's description of Fibonacci times as canonical return times is "
                            + "qualitative and has no in-scope predicate; the displayed mathematical "
                            + "clauses are formalized without inventing one."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula NearReturnFormula()
    {
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula circle = Seq(
            Mathbb, Grp(F.Id("R")), Slash, Mathbb, Grp(F.Id("Z")));
        Formula fib = new Formula.Subscript(F.Id("F"), n);
        Formula previousFib = new Formula.Subscript(F.Id("F"), Seq(n, Minus, D(1)));
        Formula defect = Seq(Varepsilon, Underscore, Grp(n));
        Formula rotation = F.Id("T");
        Formula alternating = new Formula.Power(
            Seq(Open, Minus, D(1), Close), Seq(n, Minus, D(1)));
        Formula goldenDepth = new Formula.Power(Varphi, Seq(Minus, n));
        Formula naturalIndex = Seq(n, InMacro, nat);
        Formula positiveIndex = Seq(n, InMacro, nat, Comma, Sp, D(1), Le, Sp, n);

        Formula iterateClause = Seq(
            Forall, Sp, naturalIndex, Comma, Sp,
            Forall, Sp, x, InMacro, circle, Comma, Esc,
            Call("iterate", rotation, fib, x), Sp, Eq, Sp,
            x, Plus, defect);
        Formula exactClause = Seq(
            Forall, Sp, positiveIndex, Comma, Esc,
            defect, Sp, Eq, Sp, alternating, goldenDepth);
        Formula absoluteClause = Seq(
            Forall, Sp, positiveIndex, Comma, Esc,
            new Formula.Absolute(defect), Sp, Eq, Sp, goldenDepth);
        Formula limitClause = Seq(
            Lim, Underscore, Grp(n, To, Infty), Sp,
            new Formula.Absolute(defect), Sp, Eq, Sp, D(0));
        Formula signClause = Seq(
            Forall, Sp, positiveIndex, Comma, Esc,
            Call("sgn", defect), Sp, Eq, Sp, alternating);

        return Disp(Seq(
            rotation, Open, x, Close, Sp, Eq, Sp, x, Plus,
            Frac, Grp(D(1)), Grp(Varphi), Sp, Call("mod", D(1)), Comma, Esc,
            defect, Sp, Eq, Sp, Frac, Grp(fib), Grp(Varphi), Minus, previousFib,
            Comma, Esc,
            iterateClause, Sp, Land, Esc,
            exactClause, Sp, Land, Esc,
            absoluteClause, Sp, Land, Esc,
            limitClause, Sp, Land, Esc,
            signClause, Dot));
    }
}
