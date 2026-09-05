using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class MubDimensionSixTensorDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/QuantumContext/MubDimensionSixTensor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tensor and Gauss-sum certificates produce three mutually unbiased bases in complex dimension six.",
        H("Three Mutually Unbiased Bases in Complex Dimension Six"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-tensor-mub-package"),
                DeclarationHandle.Create(LeanPrefix + "tensor_mub_package"),
                H("Coordinate tensor products preserve orthonormality and overlap-only mutual unbiasedness"),
                StatementSource.FromAuthor(TensorPackageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite coordinate types alpha and beta, expanding the sum over "
                            + "alpha times beta and distributing multiplication factors the "
                            + "coordinate inner product of two tensor vectors into the product "
                            + "of the two coordinate inner products.")),
                    Paragraph(Text(
                        "The factorization turns the Gram identity for two orthonormal bases "
                            + "into the product of two Kronecker deltas. It also multiplies two "
                            + "cross-overlap values, and Fintype.card_prod identifies the result "
                            + "with the reciprocal cardinality of the product carrier.")),
                    Paragraph(Text(
                        "The Lean predicate MutuallyUnbiased is exactly the atom's overlap-only "
                            + "condition. Orthonormality remains a separate second conjunct, so "
                            + "the third conjunct needs no hidden Gram hypotheses.")),
                    Paragraph(Text(
                        "The basis-level tensorBasis is a thin wrapper around Mathlib's "
                            + "Matrix.kronecker. The vector-level tensorVector remains explicit "
                            + "because the factorization theorem is stated for coordinate vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qutrit-three-mubs"),
                DeclarationHandle.Create(LeanPrefix + "qutrit_three_mubs"),
                H("Three explicit qutrit bases are pairwise mutually unbiased"),
                StatementSource.FromAuthor(QutritFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The family consists of the standard basis, the normalized character "
                            + "table of Z/3Z, and the normalized quadratic-phase basis with "
                            + "entries omega^(j k + k^2), where omega=exp(2 pi i/3).")),
                    Paragraph(Text(
                        "The proof evaluates every entry of all three Gram tables and every "
                            + "ordered cross-overlap table. The reductions use omega cubed equals "
                            + "one, omega not equal to one, conjugate omega equals omega squared, "
                            + "and one plus omega plus omega squared equals zero.")),
                    Paragraph(Text(
                        "All computations are exact complex equalities. No floating-point "
                            + "approximation, frozen theorem, or unchecked evaluator supplies the "
                            + "one-third overlap values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dimension-six-three-mubs-certificate"),
                DeclarationHandle.Create(LeanPrefix + "dimension_six_three_mubs_certificate"),
                H("Three tensor-product bases certify M(6) at least three"),
                StatementSource.FromAuthor(DimensionSixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each of the three family indices, dimensionSixBases tensors the "
                            + "corresponding Z, X, or Y qubit basis with the corresponding "
                            + "standard, Fourier, or quadratic-phase qutrit basis.")),
                    Paragraph(Text(
                        "The qubit overlap table has exact value one half and the qutrit table "
                            + "has exact value one third. Tensor factorization therefore gives "
                            + "one sixth for every cross-overlap on Fin 2 times Fin 3, while the "
                            + "same argument preserves each Gram identity.")),
                    Paragraph(Text(
                        "The theorem records both the PairwiseMUB package and the source atom's "
                            + "separate displayed orthonormality and one-sixth clauses. It proves "
                            + "the known lower bound of three bases only and makes no claim about "
                            + "the open existence of a fourth basis in complex dimension six."))),
                DescribeRole.Theorem))));

    private static Formula TensorPackageFormula()
    {
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula bPrime = F.Id("bPrime");
        Formula cPrime = F.Id("cPrime");

        return Disp(Seq(
            Parenthesized(Seq(
                Forall, Sp, alpha, Comma, Sp, beta, Sp, F.Text, Grp(Sp, F.Id("finite")),
                Comma, Sp, Forall, Sp, x, Comma, Sp, u, Colon, Sp, CoordinateSpace(alpha),
                Comma, Sp, y, Comma, Sp, v, Colon, Sp, CoordinateSpace(beta), Comma, RowBreak,
                Inner(TensorVector(x, y), TensorVector(u, v)), Sp, Eq, Sp,
                Inner(x, u), Sp, Times, Sp, Inner(y, v))), Comma, RowBreak,
            Land, Sp,
            Parenthesized(Seq(
                Forall, Sp, alpha, Comma, Sp, beta, Sp, F.Text, Grp(Sp, F.Id("finite")),
                Comma, Sp, Forall, Sp, b, Comma, Sp, bPrime, Comma, Sp,
                Call("CoordinateOrthonormalBasis", b), Sp, Rightarrow, Sp,
                Call("CoordinateOrthonormalBasis", bPrime), Sp, Rightarrow, Sp,
                Call("CoordinateOrthonormalBasis", TensorBasis(b, bPrime)))), Comma, RowBreak,
            Land, Sp,
            Parenthesized(Seq(
                Forall, Sp, alpha, Comma, Sp, beta, Sp, F.Text, Grp(Sp, F.Id("finite")),
                Comma, Sp, Forall, Sp, b, Comma, Sp, c, Comma, Sp,
                bPrime, Comma, Sp, cPrime, Comma, Sp,
                Call("MutuallyUnbiased", b, c), Sp, Rightarrow, Sp,
                Call("MutuallyUnbiased", bPrime, cPrime), Sp, Rightarrow, Sp,
                Call("MutuallyUnbiased", TensorBasis(b, bPrime), TensorBasis(c, cPrime)))),
            Dot));
    }

    private static Formula QutritFormula() =>
        Disp(Seq(Call("PairwiseMUB", F.Id("qutritBases")), Dot));

    private static Formula DimensionSixFormula()
    {
        Formula bases = F.Id("dimensionSixBases");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula leftVector = Call("dimensionSixBases", r, i);
        Formula rightVector = Call("dimensionSixBases", s, j);

        return Disp(Seq(
            Call("PairwiseMUB", bases), Sp, Land, Sp,
            Parenthesized(Seq(
                Parenthesized(Seq(
                    Forall, Sp, r, Colon, Sp, Call("Fin", D(3)), Comma, Sp,
                    Call("CoordinateOrthonormalBasis", Call("dimensionSixBases", r)))),
                Sp, Land, RowBreak,
                Parenthesized(Seq(
                    Forall, Sp, r, Comma, Sp, s, Colon, Sp, Call("Fin", D(3)),
                    Comma, Sp, r, Sp, Neq, Sp, s, Sp, Rightarrow, Sp,
                    Forall, Sp, i, Comma, Sp, j, Colon, Sp,
                    Seq(Call("Fin", D(2)), Sp, Times, Sp, Call("Fin", D(3))), Comma, RowBreak,
                    AbsSquared(Inner(leftVector, rightVector)), Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(6)))))),
            Dot));
    }

    private static Formula CoordinateSpace(Formula index) =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(index));

    private static Formula TensorVector(Formula left, Formula right) =>
        Call("tensorVector", left, right);

    private static Formula TensorBasis(Formula left, Formula right) =>
        Call("tensorBasis", left, right);

    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula AbsSquared(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert, Caret, Grp(D(2)));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
