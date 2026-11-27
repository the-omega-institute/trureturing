using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class QuaternionHeapRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/Comparison/QuaternionHeapRecurrence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quaternion heap iterates admit a Chebyshev formula at every index.",
        H("Chebyshev formulas for the quaternion heap recurrence"),
        Blocks(Describe.Lean(DescribeId.Create("quaternion-heap-chebyshev"),
            DeclarationHandle.Create(Module + ".normSq_and_chebyshev"),
            H("The cubic recurrence and the Chebyshev formulas"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The manuscript states the forward formula in F4 and Theorem recur, part (ii). "
                + "It credits Ottmar Loos, Symmetric Spaces I, for the geodesic recurrence and "
                + "J. C. Mason and D. C. Handscomb, Chebyshev Polynomials, for the polynomial formulas. "
                + "The forward formula and the recurrence equivalence give the characterization. "
                + "Write c(a,b) for the real inner product and bar for quaternion conjugation. "
                + "The squared norm is multiplicative, so the cubic recurrence preserves unit norm. "
                + "For a unit center, reflection has the form twice the projection onto the center "
                + "minus the original vector. Pairing the reflection with its center preserves the "
                + "adjacent inner product, which is therefore constant. The resulting linear "
                + "recurrence has the second-kind Chebyshev solution with the given first two "
                + "samples. Pairing that solution with the initial sample yields the first-kind "
                + "Chebyshev polynomial. The formulas use the integer indices of the polynomials, "
                + "with U at minus one equal to zero and U at minus two equal to minus one. "
                + "Conversely, the sample formula satisfies the same linear recurrence. "
                + "Pairing it with a unit sample recovers the constant adjacent comparison, "
                + "so the reflection formula recovers the cubic recurrence. "
                + "The sequences (0,1,0,0,...) and (1,0,0,0,...) obey the cubic recurrence "
                + "and show that each initial unit assumption is necessary. The sequence "
                + "(1,1,0,0,...) has two unit initial samples and fails the unit conclusion at "
                + "index two when the recurrence is omitted. These examples were checked by direct "
                + "substitution and were not compiled in Lean."))),
            DescribeRole.Theorem))));

    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("H")));
    private static Formula All(string name, Formula type, Formula value) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula At(Formula index) => Call("x", index);
    private static Formula Conj(Formula x) => Seq(Overline, Grp(x));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Unit(Formula x) => Eq(new Formula.Power(new Formula.Norm(x), D(2)), D(1));
    private static Formula Eval(string polynomial, Formula index, Formula x) =>
        new Formula.Apply(Seq(F.Id(polynomial), Underscore, Grp(index)), [x]);

    private static Formula Statement()
    {
        Formula n = F.Id("n"), j = F.Id("j"), zero = D(0), one = D(1), two = D(2);
        Formula initial = Call("c", At(zero), At(one));
        Formula recurrence = All("j", N, Eq(At(Add(j, two)),
            Mul(Mul(At(Add(j, one)), Conj(At(j))), At(Add(j, one)))));
        Formula closed = Eq(At(Add(n, one)),
            Sub(Mul(Eval("U", n, initial), At(one)), Mul(Eval("U", Sub(n, one), initial), At(zero))));
        Formula comparison = Eq(Call("c", At(zero), At(n)), Eval("T", n, initial));
        return Disp(All("x", Seq(N, Sp, To, Sp, Q),
            Iff(And(Unit(At(zero)), And(Unit(At(one)), recurrence)),
                All("n", N, And(Unit(At(n)), And(closed, comparison))))));
    }
}
