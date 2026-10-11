using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OrthocrossPairingPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-frame pairings can be expressed through Gaussian polynomials. "
            + "Intersecting supports are detected by evaluation at one; disjoint supports "
            + "are detected by the derivative at one.",
        H("Gaussian polynomials for orthocross pairings"),
        Blocks(
            Describe.Lean(DescribeId.Create("orthocross-pairing-polynomial"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial"), H("The pairing polynomial"),
                StatementSource.FromAuthor(Disp(Dimension(Indices(Seq(
                    Sub("P", Seq(Alpha, Beta)), Open, F.Id("X"), Close, Sp, Eq, Sp,
                    Sub("v", Alpha), Caret, Grp(Star), Sp,
                    Sub("H", F.Id("d")), Open, F.Id("X"), Close, Sp, Sub("v", Beta)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The dimension d is natural and alpha,beta are orthocross "
                    + "indices. The Gaussian coefficients of the vectors are 1 and i. The polynomial "
                    + "matrix H has diagonal X^(d-1)-i, upper entry (1-X)X^(d+j-k-1), "
                    + "and lower entry i(1-X)X^(j-k-1). Expanding the one- or two-element "
                    + "supports defines P_alpha,beta. X denotes the polynomial indeterminate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orthocross-pairing-polynomial-nonzero"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial_ne_zero"), H("Nonzero pairing polynomials"),
                StatementSource.FromAuthor(Disp(Dimension(Indices(Seq(
                    Sub("P", Seq(Alpha, Beta)), Sp, Neq, Sp, D(0)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation at one gives (1-i) times the ordinary vector "
                    + "pairing. This is nonzero when the supports intersect. For disjoint supports, "
                    + "the derivative at one is the negative pairing with upper entry 1 and lower "
                    + "entry i. The order of the support indices and the vector phases prevent "
                    + "that value from vanishing. Thus the polynomial is nonzero for every pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthocross-pairing-coefficient-bound"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial_coeff_bound"), H("A uniform coefficient bound"),
                StatementSource.FromAuthor(Disp(Dimension(Hypothesis("hd", DimensionAtLeast(D(2)),
                    Indices(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    GaussianNorm(Seq(OpenBracket, Pow(F.Id("X"), F.Id("n")), CloseBracket,
                        Sub("P", Seq(Alpha, Beta)))), Sp, Leq, Sp, D(1, 6))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each matrix-entry polynomial has coefficients of modulus at most one. "
                    + "A vector pairing contains at most four such terms with Gaussian unit phases. "
                    + "The triangle inequality bounds the modulus by four and its square by sixteen."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthocross-pairing-at-ratio"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial_at_ratio_ne_zero"), H("Nonvanishing at the geometric ratio"),
                StatementSource.FromAuthor(Disp(Dimension(Hypothesis("hd", DimensionAtLeast(D(4)),
                    Indices(Seq(Sub("P", Seq(Alpha, Beta)), Open, Ratio(), Close,
                        Sp, Neq, Sp, D(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d at least four, the Gaussian denominator of q has norm "
                    + "2d squared minus 2d plus one, which exceeds sixteen. Coprimality forces that "
                    + "denominator to divide the leading coefficient of a polynomial vanishing at q. "
                    + "The nonzero polynomial and the coefficient bound exclude this divisibility."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthocross-pairing-evaluation"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial_eval_ratio"), H("The inverse pairing identity"),
                StatementSource.FromAuthor(Disp(Dimension(Hypothesis("hd", DimensionAtLeast(D(2)),
                    Indices(Seq(Sub("P", Seq(Alpha, Beta)), Open, Ratio(), Close, Sp, Eq, Sp,
                        Fraction(Seq(Open, D(1), Minus, Ratio(), Close,
                            Pow(Ratio(), Seq(IntegerDimension(), Minus, D(2)))), Sub("u", F.Id("d"))),
                        Sp, Sub("v", Alpha), Caret, Grp(Star), Sp,
                        Call("candidate", F.Id("d")), Sp, Sub("v", Beta))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplying the inverse matrix by (1-q)q^(d-2)/u removes "
                    + "all negative powers. The diagonal quotient and the conjugate coefficient phase "
                    + "give exactly the entries of H(q). Expanding the original vector supports "
                    + "then identifies P(q) with the scaled inverse-frame pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthocross-pairing-evaluation-nonzero"),
                DeclarationHandle.Create(Prefix + "pairingPolynomial_eval_ne_zero"), H("Nonvanishing in every dimension"),
                StatementSource.FromAuthor(Disp(Dimension(Hypothesis("hd", DimensionAtLeast(D(2)),
                    Indices(Seq(Sub("P", Seq(Alpha, Beta)), Open, Ratio(), Close,
                        Sp, Neq, Sp, D(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The uniform Gaussian coefficient argument applies in dimension "
                    + "at least four. In dimensions two and three, q equals (4-3i)/5 and (12-5i)/13 "
                    + "respectively. Exact evaluation of the finite vector supports gives nonzero values."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orthocross-inverse-pairing-nonzero"),
                DeclarationHandle.Create(Prefix + "inverse_frame_pairing_ne_zero"), H("Nonzero inverse-frame pairings"),
                StatementSource.FromAuthor(Disp(Dimension(Indices(Seq(
                    Sub("v", Alpha), Caret, Grp(Star), Sp,
                    Pow(Seq(F.Omega, Underscore, Grp(F.Id("d"))), Seq(Minus, D(1))), Sp,
                    Sub("v", Beta), Sp, Neq, Sp, D(0)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial evaluation identity and its nonzero value exclude "
                    + "a zero inverse-frame pairing. Dimension zero has no indices. Dimension one "
                    + "contains only the basis vector, whose pairing is the positive diagonal parameter. "
                    + "The conclusion also includes equal indices."))),
                DescribeRole.Theorem)), []));

    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula IntegerDimension() =>
        Seq(Open, F.Id("d"), Colon, Sp, Mathbb, Grp(F.Id("Z")), Close);
    private static Formula Ratio() => Sub("q", F.Id("d"));
    private static Formula DimensionAtLeast(Formula lower) => Seq(lower, Sp, Leq, Sp, F.Id("d"));
    private static Formula Dimension(Formula body) =>
        Seq(Forall, Sp, F.Id("d"), Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula Indices(Formula body) => Seq(
        Forall, Sp, Alpha, Comma, Sp, Beta, Sp, InMacro, Sp, Call("Idx", F.Id("d")), Comma, Sp, body);
    private static Formula Hypothesis(string name, Formula proposition, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, proposition, Close, Sp, Rightarrow, Sp, body);
    private static Formula Call(string name, Formula argument) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, argument, Close);
    private static Formula GaussianNorm(Formula value) => Seq(
        Operatorname, Grp(F.Id("norm")), Underscore,
        Grp(Mathbb, Grp(F.Id("Z")), OpenBracket, F.Id("i"), CloseBracket), Open, value, Close);
}
