using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class SelfWeightedHankelPositivityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/SelfWeightedHankelPositivity."
            + "selfWeightedHankel_quadraticForm";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite self-weighted Hankel quadratic form is exactly a sum of weighted "
            + "polynomial norm squares.",
        H("Finite Self-Weighted Hankel Positivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-self-weighted-hankel-quadratic-form"),
            DeclarationHandle.Create(Declaration),
            H("The self-weighted Hankel form has an exact norm-square expansion"),
            StatementSource.FromAuthor(QuadraticFormFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let R be a finite node set, with real multiplicities m and real nodes v. "
                        + "The matrix is built as the sum of rank-one monomial Gram matrices, "
                        + "where node r carries the source-prescribed weight m(r)v(r). Its "
                        + "(i,j) entry is therefore the shifted moment sum of "
                        + "m(r)v(r)^(i+j+1).")),
                Paragraph(Text(
                    "For every complex coefficient vector c, the corresponding quadratic form "
                        + "is the sum over r of m(r)v(r) times the squared modulus of the "
                        + "polynomial evaluated at v(r). Nonnegative multiplicities and nodes "
                        + "make the matrix positive semidefinite; one positive-weight node with "
                        + "nonzero evaluation makes that particular quadratic form strictly "
                        + "positive.")),
                Paragraph(Text(
                    "This finite theorem is the algebraic core of the proposed Hamburger "
                        + "criterion. It does not assert the source's RH equivalence: the reverse "
                        + "direction needs a Hamburger representation theorem and meromorphic "
                        + "continuation machinery that are not present in the formal library."))),
            DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula FiniteSum(Formula index, Formula upper, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, Eq, Sp, D(0)), Caret, Grp(upper), Sp, body);

    private static Formula NodeSum(Formula index, Formula carrier, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, carrier), Sp, body);

    private static Formula QuadraticFormFormula()
    {
        Formula carrier = F.Id("R");
        Formula size = F.Id("N");
        Formula multiplicity = F.Id("m");
        Formula node = F.Id("v");
        Formula coefficient = F.Id("c");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula r = F.Id("r");

        Formula moment = NodeSum(r, carrier, Seq(
            Indexed(multiplicity, r), Sp, Indexed(node, r), Caret,
            Grp(i, Sp, Plus, Sp, j, Sp, Plus, Sp, D(1))));
        Formula left = FiniteSum(i, size, FiniteSum(j, size, Seq(
            Overline, Grp(Indexed(coefficient, i)), Sp,
            Indexed(coefficient, j), Sp, moment)));

        Formula evaluation = FiniteSum(k, size, Seq(
            Indexed(coefficient, k), Sp,
            Indexed(node, r), Caret, Grp(k)));
        Formula right = NodeSum(r, carrier, Seq(
            Indexed(multiplicity, r), Sp, Indexed(node, r), Sp,
            new Formula.Absolute(evaluation), Caret, Grp(D(2))));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, carrier, Sp, Mathrm, Grp(F.Id("finite")), Comma, Sp,
                size, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                multiplicity, Comma, Sp, node, Colon, Sp, carrier, Sp, To, Sp,
                Mathbb, Grp(F.Id("R")), Comma),
            Seq(
                coefficient, Colon, Sp, Call("Fin", Seq(size, Sp, Plus, Sp, D(1))),
                Sp, To, Sp, Mathbb, Grp(F.Id("C")), Comma),
            Seq(left, Sp, Eq, Sp, right, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
