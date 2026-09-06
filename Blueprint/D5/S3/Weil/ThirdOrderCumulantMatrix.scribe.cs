using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class ThirdOrderCumulantMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ThirdOrderCumulantMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third-order cumulants define an explicit positive matrix whose determinant is the reversed cubic.",
        H("Third-Order Cumulant Matrix"),
        Blocks(
            Definition(
                "third-order-cumulants",
                "ThirdOrderCumulants",
                "Typed third-order cumulant data",
                "The model records the second, fourth, and sixth cumulants as real numbers."),
            Definition(
                "cubic-discriminant-condition",
                "CubicDiscriminantCondition",
                "Strict cubic discriminant condition",
                "The typed inequalities require u = -chi4 to be positive and "
                    + "3 chi6^2 < 100 u^3. They imply that both squared off-diagonal "
                    + "coefficients b1 and b2 are strictly positive."),
            Definition(
                "positive-cubic-roots",
                "HasPositiveCubicRoots",
                "Positive root condition",
                "Every real root of the centered cubic q3 is required to be strictly positive. "
                    + "This is an explicit premise for this slice; no residual-open theorem is imported."),
            Definition(
                "third-order-cumulant-matrix",
                "k3Matrix",
                "The explicit three-by-three matrix",
                "Formula (24) is represented as a real symmetric tridiagonal matrix with center mu, "
                    + "displacement r, and off-diagonal entries sqrt(b1) and sqrt(b2)."),
            Describe.Lean(
                DescribeId.Create("third-order-cumulant-charpoly"),
                DeclarationHandle.Create(Prefix + "k3_charpoly_eq_q3"),
                H("The matrix has the centered cubic as characteristic polynomial"),
                StatementSource.FromAuthor(CharpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expanding the three-by-three determinant and using the discriminant inequalities "
                        + "to rewrite both square-root squares identifies the characteristic polynomial "
                        + "coefficient by coefficient with q3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("k3-positive-definite-from-cubic-data"),
                DeclarationHandle.Create(Prefix + "K3_posdef_from_cubic_discriminant"),
                H("The cubic data certify all leading minors and positive definiteness"),
                StatementSource.FromAuthor(PosDefFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The computed characteristic polynomial sends every Hermitian eigenvalue of K3 "
                            + "to a root of q3. The positive-root premise therefore makes every eigenvalue "
                            + "strictly positive, which proves that K3 is positive definite.")),
                    Paragraph(Text(
                        "Positive definiteness is retained by the one-by-one and two-by-two leading "
                            + "submatrices and makes the full determinant positive. Thus the same witness "
                            + "records all three strict Sylvester minors on the typed cumulant object."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-order-determinant-reversal"),
                DeclarationHandle.Create(Prefix + "k3_determinant_reversal"),
                H("The centered cubic reverses to the determinant polynomial"),
                StatementSource.FromAuthor(DeterminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A direct determinant expansion gives det(I + v K3) = p3(v). The same b1 and b2 "
                        + "identities used in the characteristic-polynomial calculation remove the square roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-order-positive-matrix-reversal"),
                DeclarationHandle.Create(
                    Prefix + "third_order_cumulant_positive_matrix_reversal"),
                H("The third-order positive-matrix bridge"),
                StatementSource.FromAuthor(FinalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For typed cumulant data satisfying the strict discriminant and positive-root "
                        + "conditions, formula (24) is positive definite and its determinant polynomial "
                        + "is exactly the coefficient reversal p3. No Fibonacci-weight, six-position-chain, "
                        + "or arbitrary higher-order positivity assertion is included."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        Seq(Grp(left), Sp, Land, Sp, Grp(right));

    private static Formula Positive(Formula expression) =>
        Seq(D(0), Sp, Lt, Sp, expression);

    private static Formula CharpolyFormula()
    {
        Formula cumulants = F.Id("c");
        return Disp(Seq(
            Forall, Sp, cumulants, Comma, Sp,
            Call("CubicDiscriminantCondition", cumulants), Sp, Rightarrow, Sp,
            EqualTo(Call("charpoly", Call("k3Matrix", cumulants)), Call("q3", cumulants)), Dot));
    }

    private static Formula PosDefFormula()
    {
        Formula cumulants = F.Id("c");
        Formula matrix = Call("k3Matrix", cumulants);
        Formula hypotheses = And(
            Call("CubicDiscriminantCondition", cumulants),
            Call("HasPositiveCubicRoots", cumulants));
        Formula minors = And(
            Positive(Call("leadingPrincipalMinorOne", matrix)),
            And(
                Positive(Call("leadingPrincipalMinorTwo", matrix)),
                And(Positive(Call("det", matrix)), Call("PosDef", matrix))));
        return Disp(Seq(
            Forall, Sp, cumulants, Comma, Sp,
            Grp(hypotheses), Sp, Rightarrow, Sp, Grp(minors), Dot));
    }

    private static Formula DeterminantFormula()
    {
        Formula cumulants = F.Id("c");
        Formula variable = F.Id("v");
        Formula matrix = Call("k3Matrix", cumulants);
        Formula shifted = Seq(D(1), Sp, Plus, Sp, variable, Sp, Cdot, Sp, matrix);
        return Disp(Seq(
            Forall, Sp, cumulants, Comma, Sp, Forall, Sp, variable, Comma, Sp,
            Call("CubicDiscriminantCondition", cumulants), Sp, Rightarrow, Sp,
            EqualTo(Call("det", shifted), Call("eval", Call("p3", cumulants), variable)), Dot));
    }

    private static Formula FinalFormula()
    {
        Formula cumulants = F.Id("c");
        Formula variable = F.Id("v");
        Formula matrix = Call("k3Matrix", cumulants);
        Formula hypotheses = And(
            Call("CubicDiscriminantCondition", cumulants),
            Call("HasPositiveCubicRoots", cumulants));
        Formula shifted = Seq(D(1), Sp, Plus, Sp, variable, Sp, Cdot, Sp, matrix);
        Formula conclusion = And(
            Call("PosDef", matrix),
            EqualTo(Call("det", shifted), Call("eval", Call("p3", cumulants), variable)));
        return Disp(Seq(
            Forall, Sp, cumulants, Comma, Sp, Forall, Sp, variable, Comma, Sp,
            Grp(hypotheses), Sp, Rightarrow, Sp, Grp(conclusion), Dot));
    }
}
