using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MonotoneTailSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharpness for monotone counting tails",
        H("Compactly supported quadratic tails"),
        Blocks(Describe.Lean(
            DescribeId.Create("quadratic-depth-cubic-mass"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MonotoneTailSharpness.monotone_tail_quadratic_depth_cubic_mass"),
            H("A monotone count with quadratic depth and cubic mass"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The real integrable kernel K is (A(t)−t)/t². Write Q(z) for its tail integral "
                    + "from z to infinity and N for the integral of max(−Q(z),0)/√z from 1 to 3.")),
                Paragraph(Text(
                    "Use A(t)=t−t²(t−2)/16 for 2−s<t≤2+s and A(t)=t elsewhere. The polynomial "
                    + "is nondecreasing on [3/2,5/2]. At the lower cutoff its value is at least "
                    + "2−s. At the upper cutoff it is at most 2+s. These comparisons preserve "
                    + "monotonicity across both joins.")),
                Paragraph(Text(
                    "The kernel equals (2−t)/16 on the window and vanishes outside it. Its tail "
                    + "therefore vanishes outside the closed window and equals ((z−2)²−s²)/32 within it. "
                    + "In particular the value at 2 is −s²/32. The negative part is bounded by s²/32 "
                    + "on a set of length 2s, where 1/√z≤1, so N≤s³/16.")),
                Paragraph(Text(
                    "Let s tend to zero. A depth bound C times the window mass to the power α "
                    + "cannot hold uniformly over these monotone counts when α>2/3. The construction "
                    + "uses the real monotone count class. The extra arithmetic structure of the "
                    + "Chebyshev prime count remains relevant to any stronger bound there."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var s = F.Id("s");
        var t = F.Id("t");
        var one = F.D(1);
        var two = F.D(2);
        var zero = F.D(0);
        var function = F.Seq(real, F.To, real);
        var value = Call("A", t);
        var width = And(Lt(zero, s), Le(s, new Formula.Fraction(one, two)));
        var monotone = Call("Monotone", F.Id("A"));
        var nonnegative = Bind(FormulaQuantifier.ForAll, "t", real,
            Imp(Le(one, t), Le(zero, value)));
        var outside = new Formula.Logic(Lt(t, F.Seq(two, F.Minus, s)),
            FormulaLogicOperator.Or, Lt(F.Seq(two, F.Plus, s), t));
        var cutoff = Bind(FormulaQuantifier.ForAll, "t", real,
            Imp(outside, new Formula.Relation(value, FormulaRelationOperator.Equal, t)));
        var depth = new Formula.Relation(Call("Q", two), FormulaRelationOperator.Equal,
            F.Seq(F.Minus, new Formula.Fraction(new Formula.Power(s, two), F.D(3, 2))));
        var mass = Le(F.Id("N"), new Formula.Fraction(new Formula.Power(s, F.D(3)), F.D(1, 6)));
        var properties = And(monotone, And(nonnegative, And(cutoff,
            And(Call("Integrable", F.Id("K")), And(depth, mass)))));
        return F.Disp(Bind(FormulaQuantifier.ForAll, "s", real,
            Imp(width, Bind(FormulaQuantifier.Exists, "A", function, properties))));
    }

    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.Bind(kind, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
