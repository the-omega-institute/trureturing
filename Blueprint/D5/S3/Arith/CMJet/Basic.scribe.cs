using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/Basic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The invariant derivation on the polynomial-pair algebra gives a three-term fourth "
            + "derivative and controls the support and highest monomial of each odd jet.",
        H("Lemniscatic polynomial pairs and their derivatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("curve"),
                DeclarationHandle.Create(Prefix + "Curve"),
                H("Polynomial pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over any commutative ring A, the carrier is the free A[X]-module on 1 and Y. "
                        + "Multiplication uses the relation Y² = 1 − X⁴."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("y-sq"),
                DeclarationHandle.Create(Prefix + "y_sq"),
                H("The curve relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square of Y is the pure polynomial 1 − X⁴. This is the relation used to identify "
                        + "the restricted derivation in prime characteristic."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("d"),
                DeclarationHandle.Create(Prefix + "D"),
                H("The invariant derivation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On f + Yg the operator has polynomial part (1 − X⁴)g′ − 2X³g and Y-part f′. "
                        + "Differentiating the pair multiplication proves the Leibniz law over A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("iter-two-poly"),
                DeclarationHandle.Create(Prefix + "iter_two_poly"),
                H("The square on pure polynomials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two applications of D send f to the pure polynomial Qf = (1 − X⁴)f″ − 2X³f′."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("q-x-pow"),
                DeclarationHandle.Create(Prefix + "Q_X_pow"),
                H("The two-term monomial rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two terms of Q(X^k) have exponents k−2 and k+2 and coefficients k(k−1) and "
                        + "−k(k+1). The first coefficient vanishes at k equal to zero or one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("iter-four-x-pow"),
                DeclarationHandle.Create(Prefix + "iter_four_X_pow"),
                H("The three-term fourth derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three exponents are k−4, k and k+4. Their coefficients are k(k−1)(k−2)(k−3), "
                        + "−2k²(k²+5) and k(k+1)(k+2)(k+3). When k < 4, the coefficient of the term with "
                        + "truncated subtraction is zero."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("q-iter-monomial-support"),
                DeclarationHandle.Create(Prefix + "Q_iter_monomial_support"),
                H("Support modulo four"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After s applications of Q to X^r, a nonzero coefficient of degree n requires n ≡ 2s+r "
                        + "modulo four."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("ato"),
                DeclarationHandle.Create(Prefix + "atO"),
                H("Evaluation at the base point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluation at X = 0 and Y = 1 adds the constant coefficients of both polynomial "
                        + "components."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-top-jet"),
                DeclarationHandle.Create(Prefix + "odd_top_jet"),
                H("The factorial at the highest monomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At order 2s+1, the value of the derivative of X^(2s+1) at the base point is (2s+1)!. "
                        + "Only the descending term of Q can contribute to the coefficient of X in each step "
                        + "toward the lowest degree."))),
                DescribeRole.Theorem)
        )));
}
