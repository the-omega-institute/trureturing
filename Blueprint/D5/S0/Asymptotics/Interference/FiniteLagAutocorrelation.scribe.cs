using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.Interference;

internal sealed class FiniteLagAutocorrelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite real signal has its exact lag autocorrelation as the Fourier coefficients of its squared modulus.",
        H("Finite Lag Autocorrelation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-real-signal-lag-autocorrelation-expansion"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/Interference/FiniteLagAutocorrelation.finite_lag_autocorrelation_expansion"),
                H("Finite signals expand by lag autocorrelation"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real signal indexed by Fin(T+1), p is its Laurent coefficient "
                        + "polynomial, extended by zero away from indices zero through T. The "
                        + "Laurent product A = invert(p) times p is constructed from that signal.")),
                    Paragraph(Text(
                        "The first public conjunct proves that the coefficient A_m is the lag sum "
                        + "of f_n times f_(n+m), with the zero extension supplied by p. The second "
                        + "public conjunct evaluates the same Laurent product on the unit circle "
                        + "and obtains the squared modulus over exactly the possible lags.")),
                    Paragraph(Text(
                        "The proof imports the earlier finite pairwise expansion only as the "
                        + "canonical finite-signal primitive. Laurent convolution, inversion, "
                        + "support bounds, and unit-circle conjugation establish the stronger "
                        + "lag-indexed statement."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula t = F.Id("T");
        Formula f = F.Id("f");
        Formula theta = F.Id("theta");
        Formula p = F.Id("p");
        Formula a = F.Id("A");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula tPlusOne = Seq(t, Sp, Plus, Sp, D(1));
        Formula signalType = Seq(Call("Fin", tPlusOne), Sp, Rightarrow, Sp, reals);
        Formula fn = new Formula.Subscript(f, n);
        Formula xToN = Seq(F.Id("X"), Caret, Grp(n));
        Formula coefficientPolynomial = Seq(
            Sum, Underscore, Grp(D(0), Sp, Leq, Sp, n, Sp, Leq, Sp, t), Sp,
            fn, Sp, xToN);
        Formula laurentRing = Seq(
            complexes, OpenBracket, F.Id("X"), Comma, Sp,
            F.Id("X"), Caret, Grp(Minus, D(1)), CloseBracket);
        Formula pDefinition = Seq(
            p, Sp, Colon, Sp, laurentRing, Sp, Eq, Sp, coefficientPolynomial);
        Formula aDefinition = Seq(
            a, Sp, Eq, Sp, Call("invert", p), Sp, Times, Sp, p);
        Formula am = new Formula.Subscript(a, m);
        Formula shiftedCoefficient = new Formula.Subscript(
            p, Seq(n, Sp, Plus, Sp, m));
        Formula lagSum = Seq(
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, Call("Fin", tPlusOne)), Sp,
            fn, Sp, shiftedCoefficient);
        Formula coefficientClause = Seq(
            Forall, Sp, m, Sp, InMacro, Sp, integers, Comma, Sp,
            am, Sp, Eq, Sp, lagSum);
        Formula phase = Call("exp", Seq(F.Id("i"), Thin, theta));
        Formula signal = Call("finiteSignal", f, phase);
        Formula normSquare = Call("normSq", signal);
        Formula phasePower = Seq(phase, Caret, Grp(m));
        Formula fourierSum = Seq(
            Sum, Underscore, Grp(Minus, t, Sp, Leq, Sp, m, Sp, Leq, Sp, t), Sp,
            am, Sp, phasePower);
        Formula fourierClause = Seq(normSquare, Sp, Eq, Sp, fourierSum);

        return Seq(
            Forall, Sp, t, Sp, InMacro, Sp, naturals, Comma, Sp,
            f, Colon, Sp, signalType, Comma, Sp,
            theta, Sp, InMacro, Sp, reals, Comma, Sp,
            F.Text, Grp(F.Id("let"), Sp), Sp,
            pDefinition, Comma, Sp, aDefinition, Comma, Sp,
            Open, coefficientClause, Close, Sp, Land, RowBreak, Grp(),
            Open, fourierClause, Close, Dot);
    }
}
