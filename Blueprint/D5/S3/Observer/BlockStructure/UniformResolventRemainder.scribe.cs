using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class UniformResolventRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/BlockStructure/UniformResolventRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spectral floor of two gives a quadratic resolvent remainder constant of one quarter.",
        H("Uniform Resolvent Remainder"),
        Blocks(
            Paragraph(Text("Let A and E be real square matrices on any finite decidable index "
                + "type, including the empty type. Write I for the identity. Matrix order is "
                + "the positive semidefinite order: X is at most Y when Y-X is positive "
                + "semidefinite. Herm denotes symmetry and Unit denotes invertibility. "
                + "Every matrix norm below is the spectral norm induced by the Euclidean "
                + "vector norm. The inverse is the nonsingular matrix inverse. "
                + "The real number c in the first statement is arbitrary.")),
            Describe.Lean(
                DescribeId.Create("inverse-controlled-by-positive-floor"),
                DeclarationHandle.Create(Prefix + "inverse_control_of_lower_bound"),
                H("An inverse controlled by a positive floor"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(
                    And(Herm(A()), And(Lt(D(0), F.Id("c")), Floor(F.Id("c"), A()))),
                    And(Call("Unit", A()), Le(Norm(Inv(A())), Inv(F.Id("c"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every real spectral value of A is at least c. "
                    + "When c is positive, zero is absent from the spectrum, so A is invertible. "
                    + "Continuous functional calculus represents the inverse by the scalar "
                    + "function x mapped to its reciprocal. The norm estimate for this "
                    + "calculus bounds the inverse norm by the reciprocal of c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-preserves-floor-one"),
                DeclarationHandle.Create(Prefix + "perturbed_lower_bound"),
                H("The perturbed spectral floor"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(
                    And(Floor(D(2), A()), And(Herm(E()), Le(Norm(E()), D(1)))),
                    Le(F.Id("I"), Add(A(), E()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute value of each real spectral value of E "
                    + "is at most its spectral norm, hence at most one. Symmetry therefore "
                    + "gives E at least minus I in matrix order. Add this to A at least "
                    + "twice I to obtain the stated lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dimension-independent-inverse-bounds"),
                DeclarationHandle.Create(Prefix + "inverse_bounds"),
                H("The two inverse norms"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(Assumptions(),
                    And(Le(Norm(Inv(A())), new Formula.Fraction(D(1), D(2))),
                        Le(Norm(Inv(Add(A(), E()))), D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the general inverse estimate to A with c=2 "
                    + "and to A+E with c=1. The sum is symmetric, and the preceding "
                    + "spectral floor supplies its positive lower bound. Neither constant "
                    + "contains the size of the index type."))),
                DescribeRole.Theorem),
            Paragraph(Text("Define R=A inverse E A inverse E (A+E) inverse, with the factors "
                + "in that order. This is the five-factor term in the first-order inverse "
                + "expansion. The following estimate concerns that matrix product.")),
            Describe.Lean(
                DescribeId.Create("uniform-quadratic-resolvent-bound"),
                DeclarationHandle.Create(Prefix + "remainder_bound"),
                H("The quadratic remainder bound"),
                StatementSource.FromAuthor(Disp(ImpliesFormula(Assumptions(),
                    Le(Norm(F.Id("R")), new Formula.Fraction(Pow(Norm(E()), 2), D(4)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Submultiplicativity bounds the product norm by the "
                    + "product of its five norms. The two factors A inverse each contribute "
                    + "at most one half, the last inverse contributes at most one, and the "
                    + "two perturbation factors contribute the square of the norm of E. "
                    + "The resulting constant one quarter is the same in every finite dimension."))),
                DescribeRole.Theorem))));

    private static Formula A() => F.Id("A");
    private static Formula E() => F.Id("E");
    private static Formula Herm(Formula value) => Call("Herm", value);
    private static Formula Floor(Formula c, Formula value) => Le(Mul(c, F.Id("I")), value);
    private static Formula Assumptions() =>
        And(Herm(A()), And(Herm(E()), And(Floor(D(2), A()), Le(Norm(E()), D(1)))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) => Seq(left, Plus, right);
    private static Formula Mul(Formula left, Formula right) => Seq(left, Cdot, Sp, right);
    private static Formula Pow(Formula value, byte exponent) => Seq(value, Caret, Grp(D(exponent)));
    private static Formula Inv(Formula value) => Seq(Open, value, Close, Caret, Grp(Minus, D(1)));
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert, Sp);
    private static Formula And(Formula left, Formula right) => Seq(Grp(left), Land, Sp, Grp(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Seq(Grp(left), Implies, Sp, Grp(right));
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
