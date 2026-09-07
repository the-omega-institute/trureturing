using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class GramSchmidtCoefficientFieldDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Moments/GramSchmidtCoefficientField."
            + "gram_schmidt_coordinates_mem_coefficient_field";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace Hankel inner product preserves the coefficient field during Gram--Schmidt.",
        H("Gram--Schmidt Coordinates in the Coefficient Field"),
        Blocks(Describe.Lean(
            DescribeId.Create("gram-schmidt-coordinates-mem-coefficient-field"),
            DeclarationHandle.Create(Declaration),
            H("Every orthogonalized coordinate belongs to the coefficient-generated subfield"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a real polynomial, d its natural degree, and power a real basis "
                        + "of an inner product space E indexed by Fin d. Set S to the canonical "
                        + "coefficientMultiplicationMatrix of q and m(n) to trace(S^n)/d. "
                        + "Assume that the inner product equals coefficientHankelValue power m "
                        + "for every pair of vectors. Let F be the subfield of the reals generated "
                        + "by all coefficients of q.")),
                Paragraph(Text(
                    "Every entry of S belongs to F. Induction on matrix powers, finite sums, "
                        + "and division by the natural number d place all moments in F. "
                        + "The finite Hankel sum therefore pairs vectors with F-valued "
                        + "coordinates to an element of F.")),
                Paragraph(Text(
                    "Induction on the Gram--Schmidt index now preserves coordinate membership. "
                        + "A basis vector starts with zero-one coordinates. Each projection "
                        + "subtracts a previous orthogonalized vector multiplied by the ratio "
                        + "of its inner product with the input vector to its inner product "
                        + "with itself. Both inner products and all previous coordinates "
                        + "belong to F, which is closed under these field operations.")),
                Paragraph(Text(
                    "The basis is unnormalized. No square-root closure is asserted. Monicity "
                        + "and positive degree are unnecessary for this invariant. The theorem "
                        + "assumes the trace Hankel identity; it neither constructs that inner "
                        + "product nor identifies traces with an enumeration of roots. "
                        + "Membership of later Jacobi parameters and chain weights is not "
                        + "part of this declaration."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula power = F.Id("power");
        Formula field = F.Id("F");
        Formula moment = F.Id("m");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula degree = Call("natDegree", q);
        Formula matrix = Call("coefficientMultiplicationMatrix", q);
        Formula orthogonal = Call("gramSchmidtBasis", power);

        return Disp(new Formula.Aligned([
            Seq(field, Sp, Eq, Sp, Call("subfieldClosure", Call("range", Call("coeff", q)))),
            Seq(Call("m", n), Sp, Eq, Sp, Frac,
                Grp(Call("trace", new Formula.Power(matrix, n))), Grp(degree)),
            Seq(Open, Forall, Sp, x, Comma, Sp, y, Sp, InMacro, Sp, F.Id("E"), Comma, Sp,
                Call("inner", x, y), Sp, Eq, Sp,
                Call("coefficientHankelValue", power, moment, x, y), Close, Sp, Rightarrow),
            Seq(Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, Call("Fin", degree), Comma, Sp,
                Call("repr", power, new Formula.Apply(orthogonal, [i]), j),
                Sp, InMacro, Sp, field, Dot),
        ]));
    }
}
