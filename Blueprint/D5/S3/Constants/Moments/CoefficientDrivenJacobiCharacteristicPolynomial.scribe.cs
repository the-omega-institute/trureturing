using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CoefficientDrivenJacobiCharacteristicPolynomialDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial."
            + "coefficient_driven_jacobi_characteristic_polynomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict coefficient Hankel data and self-adjoint companion multiplication produce "
            + "a monic orthogonal basis whose positive Jacobi recurrence has charpoly q.",
        H("Coefficient-Driven Jacobi Characteristic Polynomial"),
        Blocks(Describe.Lean(
            DescribeId.Create("coefficient-driven-jacobi-characteristic-polynomial"),
            DeclarationHandle.Create(Declaration),
            H("Coefficient data produce a positive Jacobi recurrence with charpoly q"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be monic and let b be a power basis indexed below its degree. "
                        + "Equip the coefficient space with an inner product represented by "
                        + "a strictly positive finite Hankel form. The multiplication operator "
                        + "is the explicit companion-shaped matrix read from the coefficients "
                        + "of q, and is assumed self-adjoint for this Hankel inner product.")),
                Paragraph(Text(
                    "Gram--Schmidt in degree order gives an orthogonal basis p whose leading "
                        + "power-basis coordinate is one. Degree triangularity makes companion "
                        + "multiplication upper Hessenberg, while self-adjointness supplies the "
                        + "reflected zeros, so its matrix J in the p basis is tridiagonal.")),
                Paragraph(Text(
                    "For every positive index j, the subdiagonal entry is one and the opposite "
                        + "entry is h(j)/h(j-1), where h is the squared norm. Strict Hankel "
                        + "positivity makes this ratio positive. Finally, change-of-basis "
                        + "invariance reduces the characteristic polynomial to that of the "
                        + "companion matrix; the pinned power-basis theorem identifies it "
                        + "with q.")),
                Paragraph(Text(
                    "This declaration stops at the coefficient-driven Jacobi construction. It "
                        + "does not perform Cholesky factorization, construct chain weights, or "
                        + "identify the final chain polynomial."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        new Formula.Subscript(matrix, Seq(row, Comma, column));

    private static Formula TheoremFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = F.Id("E");
        Formula polynomial = F.Id("q");
        Formula degree = Call("natDegree", polynomial);
        Formula indexType = Call("Fin", degree);
        Formula basis = F.Id("b");
        Formula moment = F.Id("m");
        Formula multiplication = Call("coefficientMultiplication", polynomial, basis);
        Formula orthogonal = Call("gramSchmidtBasis", basis);
        Formula matrix = F.Id("J");
        Formula norm = F.Id("h");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula previous = Seq(j, Sp, Minus, Sp, D(1));

        Formula hypotheses = Seq(
            Call("Monic", polynomial), Sp, Land, Sp,
            Call("HankelInnerProduct", basis, moment), Sp, Land, Sp,
            Call("StrictPositiveHankel", basis, moment), Sp, Land, Sp,
            Call("SelfAdjoint", multiplication));

        Formula orthogonality = Seq(
            Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, indexType, Comma, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Call("inner", Apply(orthogonal, i), Apply(orthogonal, j)), Sp, Eq, Sp, D(0));

        Formula monicity = Seq(
            Forall, Sp, i, Sp, InMacro, Sp, indexType, Comma, Sp,
            Call("repr", basis, Apply(orthogonal, i), i), Sp, Eq, Sp, D(1));

        Formula farApart = Seq(
            i, Sp, Plus, Sp, D(1), Sp, Lt, Sp, j, Sp, Lor, Sp,
            j, Sp, Plus, Sp, D(1), Sp, Lt, Sp, i);
        Formula tridiagonal = Seq(
            Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, indexType, Comma, Sp,
            Open, farApart, Close, Sp, Rightarrow, Sp,
            Entry(matrix, i, j), Sp, Eq, Sp, D(0));

        Formula recurrence = Seq(
            Forall, Sp, j, Sp, InMacro, Sp, indexType, Comma, Sp,
            D(0), Sp, Lt, Sp, j, Sp, Rightarrow, Sp,
            Entry(matrix, j, previous), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Entry(matrix, previous, j), Sp, Eq, Sp,
            Frac, Grp(Apply(norm, j)), Grp(Apply(norm, previous)), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Entry(matrix, previous, j));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, space, Colon, Sp, Call("RealInnerProductSpace"), Comma, Sp,
                polynomial, Colon, Sp, Call("Polynomial", reals), Comma),
            Seq(
                basis, Colon, Sp, Call("Basis", indexType, reals, space), Comma, Sp,
                moment, Colon, Sp, Naturals(), Sp, To, Sp, reals, Comma),
            Seq(hypotheses, Sp, Rightarrow),
            Seq(
                matrix, Sp, Eq, Sp,
                Call("toMatrix", orthogonal, orthogonal, multiplication), Comma, Sp,
                norm, Open, i, Close, Sp, Eq, Sp,
                Call("inner", Apply(orthogonal, i), Apply(orthogonal, i)), Comma),
            Seq(Open, orthogonality, Close, Sp, Land),
            Seq(Open, monicity, Close, Sp, Land),
            Seq(Open, tridiagonal, Close, Sp, Land),
            Seq(Open, recurrence, Close, Sp, Land),
            Seq(Call("charpoly", matrix), Sp, Eq, Sp, polynomial, Dot),
        ]));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
