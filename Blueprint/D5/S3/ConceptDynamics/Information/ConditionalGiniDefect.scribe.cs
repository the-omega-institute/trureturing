using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class ConditionalGiniDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The increase in conditional logical impurity equals a weighted squared posterior difference.",
        H("Exact Conditional Gini Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("conditional-gini-exact-defect"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Information/ConditionalGiniDefect."
                + "conditional_gini_exact_defect"),
            H("Coarsening charges exactly the squared change of the posterior"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let p be a probability mass function, r the refined readout, t the target, "
                    + "and f the coarsening map. I(s) denotes conditional logical impurity for "
                    + "readout s and the same p and t. M(d) is the refined fiber mass. P(d,a) "
                    + "and Q(f(d),a) are the refined and coarse joint target masses divided by "
                    + "their respective fiber masses. The ratios and sums use extended "
                    + "nonnegative reals. Each ratio is converted to a real before subtraction.")),
                Paragraph(Text(
                    "For one target value, the posterior ratio represents the conditional "
                    + "expectation of the target indicator almost everywhere. Nested "
                    + "conditional expectations split its squared prediction loss into the "
                    + "refined loss and the squared change of the two estimates. The sum of "
                    + "indicator losses equals ordered-pair impurity by the complementary "
                    + "collision identity. Summing the squared changes and grouping by refined "
                    + "fiber gives the displayed formula.")),
                Paragraph(Text(
                    "Zero-mass fibers contribute zero. The formula allows arbitrary carrier "
                    + "types and imposes no countability restriction on their ambient types. "
                    + "It concerns probability mass functions and deterministic readouts."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula Statement()
    {
        Formula x = F.Id("X");
        Formula c = F.Id("C");
        Formula d = F.Id("D");
        Formula a = F.Id("A");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula f = F.Id("f");
        Formula fiber = F.Id("d");
        Formula target = F.Id("a");
        Formula refined = Call("toReal", Call("P", fiber, target));
        Formula coarse = Call("toReal", Call("Q", Call("f", fiber), target));
        Formula square = new Formula.Power(Seq(Open, refined, Sp, Minus, Sp, coarse, Close), D(2));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, c, Comma, Sp, d, Comma, Sp, a,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            p, Colon, Sp, Call("PMF", x), Comma, Sp,
            r, Colon, Sp, x, Sp, To, Sp, d, Comma, Sp,
            t, Colon, Sp, x, Sp, To, Sp, a, Comma, Sp,
            f, Colon, Sp, d, Sp, To, Sp, c, Comma, RowBreak, Grp(),
            Call("I", Seq(f, Sp, Circ, Sp, r)), Sp, Eq, Sp, Call("I", r), Sp, Plus, Sp,
            Sum, Underscore, Grp(fiber), Sp, Sum, Underscore, Grp(target), Sp,
            Call("M", fiber), Sp, Cdot, Sp, Call("ofReal", square), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
