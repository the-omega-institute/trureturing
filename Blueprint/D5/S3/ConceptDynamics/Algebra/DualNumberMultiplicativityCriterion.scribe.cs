using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Algebra;

internal sealed class DualNumberMultiplicativityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion."
            + "dual_number_lift_preserves_mul_iff_product_rule";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical dual-number lift is multiplicative exactly under the product rule.",
        H("Dual Number Multiplicativity Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("dual-number-multiplicativity-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Multiplicativity is equivalent to the product rule"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be an algebra over a commutative scalar semiring R, and let "
                        + "D : A -> A be R-linear.")),
                Paragraph(Text(
                    "The displayed map uses the canonical inclusions into the square-zero "
                        + "extension. It preserves products exactly when D obeys the "
                        + "displayed left-right product rule."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("R");
        Formula algebra = F.Id("A");
        Formula differential = F.Id("D");
        Formula left = F.Id("a");
        Formula right = F.Id("b");
        Formula product = Seq(left, Sp, Cdot, Sp, right);
        Formula setup = Seq(
            Call("CommSemiring", scalar), Sp, Land, Sp,
            Call("Semiring", algebra), Sp, Land, Sp,
            Call("Algebra", scalar, algebra), Sp, Land, Sp,
            Call("LinearMap", scalar, differential, algebra, algebra));
        Formula preservesProducts = Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, algebra, Comma, Sp,
            Lift(differential, product), Sp, Eq, Sp,
            Lift(differential, left), Sp, Cdot, Sp, Lift(differential, right));
        Formula productRule = Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, algebra, Comma, Sp,
            Apply(differential, product), Sp, Eq, Sp,
            left, Sp, Cdot, Sp, Apply(differential, right), Sp, Plus, Sp,
            Apply(differential, left), Sp, Cdot, Sp, right);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, algebra, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            differential, Colon, Sp, algebra, Sp, To, Sp, algebra, Comma,
            RowBreak, Grp(),
            setup, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, preservesProducts, Close, Sp, Iff, Sp,
            Open, productRule, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Lift(Formula differential, Formula value) =>
        Seq(
            Open,
            Call("inl", value), Sp, Plus, Sp,
            Call("inr", Apply(differential, value)),
            Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
