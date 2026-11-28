using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThetaShearMonotonicityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The planar theta function strictly decreases in the shear coordinate on the reduced " +
        "half-strip at every positive temperature.",
        H("Strict shear monotonicity"), Blocks([.. Section0.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("shear_derivative_neg", "Negative shear derivative", Derivative(),
                "Poisson summation in the first integer coordinate rewrites the " +
                "planar theta series as the square root of y over t times a sum " +
                "of one-dimensional Fourier theta functions. Pairing positive and " +
                "negative second coordinates isolates a constant zero row. A " +
                "Gaussian first moment bounds the row derivatives uniformly, " +
                "so termwise differentiation is valid. Write s equal to y over t " +
                "and v equal to t y. The first row contributes a negative term " +
                "of size A times exp of negative pi v times sin of two pi x; " +
                "the remaining rows contribute at most B times the same factors " +
                "times the normalized Gaussian tail at v. For s at least one half, take " +
                "A = 4 pi exp(-pi s) (1 - G(s)) and B = 4 pi exp(-pi s) (1 + G(s)), " +
                "where G is the normalized Gaussian tail. The bound G(s) < 1/15 and the " +
                "tail bound at v give B times gaussianTail(v) < A. For s at most one half, " +
                "the strengthened small-parameter derivative " +
                "bounds again give a positive first-row margin against the tail. The relation " +
                "v s equal to y squared makes the exponentially scaled tail " +
                "less than one over thirty-nine thousand nine hundred ninety-nine. " +
                "Thus the first row dominates in both cases when t is at least " +
                "one. Reciprocal-temperature duality transfers the strict sign " +
                "to every positive temperature. This is the shear step of the " +
                "proof of Montgomery's planar theta theorem."),
            Entry("shear_minimum", "Unique horizontal minimum", Minimum(),
                "The Gaussian series is differentiable and hence continuous in " +
                "the shear parameter. Its derivative is negative at every point " +
                "in the interior of the closed interval from zero to one half. " +
                "The mean value theorem therefore gives strict decrease on the " +
                "whole closed interval, including its endpoints. The right " +
                "endpoint is the unique horizontal minimizer.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body) =>
        Describe.Lean(
            DescribeId.Create("theta-shear-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaShearMonotonicity." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Montgomery),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Half => Div(D(1), D(2));
    private static Formula HexHeight => Div(Call("sqrt", D(3)), D(2));
    private static Formula ForTXY(Formula p) => All("t", R, All("y", R, All("x", R, p)));
    private static Formula Conditions(Formula p) =>
        Imp(Lt(D(0), V("t")), Imp(Le(HexHeight, V("y")), p));
    private static Formula Derivative() => ForTXY(Conditions(
        Imp(Lt(D(0), V("x")), Imp(Lt(V("x"), Half),
            Lt(Call("deriv", Lam("z", R, Call("F", V("t"), V("z"), V("y"))),
                V("x")), D(0))))));
    private static Formula Minimum() => ForTXY(Conditions(
        Imp(Le(D(0), V("x")), Imp(Le(V("x"), Half),
            And(Le(Call("F", V("t"), Half, V("y")),
                Call("F", V("t"), V("x"), V("y"))),
                Iff(Equal(Call("F", V("t"), V("x"), V("y")),
                    Call("F", V("t"), Half, V("y"))), Equal(V("x"), Half)))))));
    }
}
