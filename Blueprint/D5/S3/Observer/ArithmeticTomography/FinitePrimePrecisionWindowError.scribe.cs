using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class FinitePrimePrecisionWindowErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime and precision truncation has horizontal-plus-vertical error.",
        H("Finite Prime-Precision Window Error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-precision-window-error"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ArithmeticTomography/FinitePrimePrecisionWindowError."
                        + "finite_prime_precision_window_error"),
                H("Finite prime-precision windows have a uniform two-part error"),
                StatementSource.FromAuthor(WindowErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed pair of points, d is its exact local prime distance and "
                            + "dK is the precision-truncated local distance. The public local "
                            + "laws state both the unit diameter and the precision error.")),
                    Paragraph(Text(
                        "The global expression and its finite window are constructed directly "
                            + "from the prime weights. Splitting the convergent prime sum across "
                            + "F leaves the omitted-prime tail, while the local bound contributes "
                            + "the precision tail on F.")),
                    Paragraph(Text(
                        "Mathlib's prime rpow summability theorem supplies convergence exactly "
                            + "for s greater than one, and positivity of the prime-weight sum "
                            + "justifies the common normalization."))),
                DescribeRole.Theorem))));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PrimeNumbers() =>
        Seq(Mathbb, Grp(F.Id("P")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula SumOver(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(index, Sp, InMacro, Sp, domain)), Sp, body);

    private static Formula WindowErrorFormula()
    {
        Formula real = RealNumbers();
        Formula natural = NaturalNumbers();
        Formula primeType = PrimeNumbers();
        Formula s = F.Id("s");
        Formula window = F.Id("F");
        Formula precision = F.Id("K");
        Formula distance = F.Id("d");
        Formula truncated = F.Id("dK");
        Formula prime = F.Id("p");
        Formula dp = Call("d", prime);
        Formula dkp = Call("dK", prime);
        Formula kp = Call("K", prime);
        Formula primeWeight = Power(prime, Seq(Minus, s));
        Formula normalizer = SumOver(prime, primeType, primeWeight);
        Formula global = new Formula.Fraction(
            SumOver(prime, primeType, Seq(primeWeight, Sp, dp)),
            normalizer);
        Formula finiteWindow = new Formula.Fraction(
            SumOver(prime, window, Seq(primeWeight, Sp, dkp)),
            normalizer);
        Formula difference = Seq(global, Sp, Minus, Sp, finiteWindow);
        Formula horizontalTail = SumOver(
            prime,
            Seq(primeType, Sp, Setminus, Sp, window),
            primeWeight);
        Formula precisionTail = SumOver(
            prime,
            window,
            Power(prime, Seq(Minus, Open, s, Sp, Plus, Sp, kp, Close)));
        Formula bound = new Formula.Fraction(
            Seq(horizontalTail, Sp, Plus, Sp, precisionTail),
            normalizer);
        Formula exactLocalLaw = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, primeType, Comma, Sp,
            D(0), Sp, Leq, Sp, dp, Sp, Leq, Sp, D(1));
        Formula truncationLaw = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, window, Comma, Sp,
            D(0), Sp, Leq, Sp, dp, Sp, Minus, Sp, dkp, Sp, Leq, Sp,
            Power(prime, Seq(Minus, kp)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, s, Colon, Sp, real, Comma, Sp,
            window, Colon, Sp, Call("Finset", primeType), Comma,
            RowBreak, Grp(),
            precision, Colon, Sp, Arrow(primeType, natural), Comma,
            RowBreak, Grp(),
            distance, Comma, Sp, truncated, Colon, Sp,
            Arrow(primeType, real), Comma,
            RowBreak, Grp(),
            Open, D(1), Sp, Lt, Sp, s, Close, Sp, Land, Sp,
            Open, exactLocalLaw, Close, Sp, Land, RowBreak, Grp(),
            Open, truncationLaw, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, D(0), Sp, Leq, Sp, difference, Close,
            Sp, Land, RowBreak, Grp(),
            Open, difference, Sp, Leq, Sp, bound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
