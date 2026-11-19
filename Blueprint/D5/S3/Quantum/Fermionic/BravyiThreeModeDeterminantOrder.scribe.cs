using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BravyiThreeModeDeterminantOrderDocument : IScribeDocumentDefinition
{
    private const string ModulePath = "D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder";
    private const string Digest = "Shifted determinant order for the real isotropic three-mode Bravyi blocks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Digest, H("Shifted determinants of the three-mode Bravyi blocks"), Blocks(
            Paragraph(Text("Bravyi studies the isotropic three-mode channel in Classical capacity of fermionic product channels "
                + "(arXiv:quant-ph/0507282, Section V.B). The chiral and complementary real blocks have sizes four and two. "
                + "Each comparator takes the first and third amplitudes to be the positive square root of one half and the second to be zero.")),
            Entry("chiral_det_polynomial_difference", "The three chiral coefficient differences",
                PolynomialDifference(ChiralDifference()),
                "The Laplace expansion depends on the squares of the amplitudes. Eliminating the third square by normalization "
                + "gives the quadratic, linear and constant coefficients. Homogenizing the constant term using invariantX + invariantZ + invariantR = 1 "
                + "expresses it as a sum of nonnegative terms at every channel parameter from zero through one."),
            Entry("complement_det_polynomial_difference", "The complementary constant difference",
                PolynomialDifference(Equal(
                    Subtract(DetPolynomial(Call("complement", Variable("lam"), Variable("c"), Variable("q"))),
                        DetPolynomial(Call("complementComparator", Variable("lam")))),
                    Coefficient(Call("complementDelta", Square(Variable("lam")), InvariantX(), InvariantZ())))),
                "The complementary trace is independent of the amplitudes, so the difference comes entirely from the unshifted determinant."),
            Entry("det_shift_order", "Both comparator determinants are lower bounds", ShiftOrder(),
                "Evaluate both difference polynomials at the nonnegative shift. The chiral difference has three nonnegative terms, "
                + "and the complementary constant is nonnegative. The argument uses the closed parameter interval, including zero and one."))));

    private static DocumentBlock Entry(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create("bravyi-three-mode-" + name.Replace('_', '-')),
            DeclarationHandle.Create(ModulePath + "." + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula ChiralDifference()
    {
        Formula t = Square(Variable("lam"));
        Formula shift = Qualified("Polynomial", "X");
        Formula quadratic = Coefficient(Call("delta2", t, InvariantX(), InvariantZ()));
        Formula linear = Coefficient(Call("delta3", t, InvariantX(), InvariantZ()));
        Formula constant = Coefficient(Call("delta4", t, InvariantX(), InvariantZ(), Call("invariantR", Variable("c"), Variable("q"))));
        return Equal(
            Subtract(DetPolynomial(Call("chiral", Variable("lam"), Variable("c"), Variable("p"), Variable("q"))),
                DetPolynomial(Call("chiralComparator", Variable("lam")))),
            Add(Add(Multiply(quadratic, Square(shift)), Multiply(linear, shift)), constant));
    }

    private static Formula ShiftOrder()
    {
        Formula lam = Variable("lam");
        Formula chiralOrder = Le(ShiftedDet(4, Call("chiralComparator", lam)),
            ShiftedDet(4, Call("chiral", lam, Variable("c"), Variable("p"), Variable("q"))));
        Formula complementOrder = Le(ShiftedDet(2, Call("complementComparator", lam)),
            ShiftedDet(2, Call("complement", lam, Variable("c"), Variable("q"))));
        return All("s", AllInputs(Implies(Le(D(0), Variable("s")), Implies(Le(D(0), lam),
            Implies(Le(lam, D(1)), Implies(Normalized(), new Formula.Logic(
                chiralOrder, FormulaLogicOperator.And, complementOrder)))))));
    }

    private static Formula ShiftedDet(int dimension, Formula matrix)
    {
        Formula indices = Call("Fin", Num(dimension));
        Formula identity = Seq(Open, D(1), Colon, Sp, Call("Matrix", indices, indices, Reals()), Close);
        Formula scalar = Seq(Variable("s"), Sp, Cdot, Sp, identity);
        return new Formula.Apply(Qualified("Matrix", "det"), [Add(scalar, matrix)]);
    }

    private static Formula PolynomialDifference(Formula equality) => AllInputs(Implies(Normalized(), equality));
    private static Formula AllInputs(Formula body) => All("lam", All("c", All("p", All("q", body))));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Reals(), body);
    private static Formula Normalized() => Equal(Add(Add(Square(Variable("c")), Square(Variable("p"))), Square(Variable("q"))), D(1));
    private static Formula Reals() => Seq(Mathbb, Grp(Variable("R")));
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula InvariantX() => Call("invariantX", Variable("c"));
    private static Formula InvariantZ() => Call("invariantZ", Variable("c"), Variable("p"));
    private static Formula DetPolynomial(Formula matrix) => Call("shiftedDetPolynomial", matrix);
    private static Formula Coefficient(Formula value) => new Formula.Apply(Qualified("Polynomial", "C"), [value]);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Variable(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Qualified(string module, string name) =>
        Seq(Operatorname, Grp(Seq(Variable(module), Dot, Variable(name))));
}
