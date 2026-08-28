using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class FiniteCountertermMellinContinuationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite local counterterms give a meromorphic Mellin continuation.",
        H("Finite Counterterm Mellin Continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-counterterms-continue-the-mellin-transform"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation."
                        + "finite_counterterm_mellin_continuation"),
                H("Finite counterterms continue the Mellin transform"),
                StatementSource.FromAuthor(ContinuationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let theta be a complex-valued heat trace, let a be a finite family of "
                            + "local coefficients, and let alpha be a strictly decreasing list of "
                            + "real exponents with one additional residual exponent. The displayed "
                            + "regularized trace is constructed by subtracting the finite principal "
                            + "part only on the interval ending at one.")),
                    Paragraph(Text(
                        "The hypotheses state local integrability of that exact piecewise trace, "
                            + "the residual power bound at zero, and exponential decay of theta at "
                            + "infinity. These analytic assumptions are all explicit in the Lean "
                            + "signature; none is hidden in a named source object.")),
                    Paragraph(Text(
                        "The continued function is the literal sum of the two split integrals and "
                            + "the finite rational pole ledger. It is meromorphic on the half-plane "
                            + "to the right of the residual exponent, and on the original "
                            + "convergence half-plane theta has a convergent Mellin transform equal "
                            + "to this continuation.")),
                    Paragraph(Text(
                        "Repository search found no theorem with this general finite-counterterm "
                            + "carrier. The proof applies Mathlib's Mellin convergence and "
                            + "differentiability theorem for simultaneous power and exponential "
                            + "bounds, the exact Mellin transform of a power on (0,1], and the "
                            + "standard closure rules for finite sums of meromorphic functions."))),
                DescribeRole.Theorem))));

    private static Formula ContinuationFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula m = F.Id("m");
        Formula theta = Theta;
        Formula coefficient = F.Id("a");
        Formula exponent = Alpha;
        Formula decay = Delta;
        Formula t = F.Id("t");
        Formula s = F.Id("s");
        Formula j = F.Id("j");
        Formula residual = F.Id("R");
        Formula regularized = Seq(Theta, Underscore, Grp(F.Id("reg")));
        Formula continued = Seq(F.Id("M"), Underscore, Grp(m));
        Formula finM = Call("Fin", m);
        Formula finNext = Call("Fin", Seq(m, Plus, D(1)));
        Formula thetaType = Seq(real, To, complex);
        Formula coefficientType = Seq(finM, To, complex);
        Formula exponentType = Seq(finNext, To, real);
        Formula complexT = Seq(Open, t, Colon, complex, Close);
        Formula exponentJ = Seq(exponent, Open, j, Close);
        Formula alphaLast = Seq(exponent, Open, F.Id("last"), Open, m, Close, Close);
        Formula principalTerm = Seq(
            coefficient, Open, j, Close, Sp,
            complexT, Caret, Grp(Minus, exponentJ));
        Formula principalSum = Seq(
            Sum, Underscore, Grp(j, Colon, finM), Sp, principalTerm);
        Formula residualAtT = Seq(
            theta, Open, t, Close, Sp, Minus, Sp, principalSum);
        Formula regularizedAtT = Seq(
            F.Id("if"), Sp, t, Sp, Le, Sp, D(1), Sp,
            F.Id("then"), Sp, residual, Open, t, Close, Sp,
            F.Id("else"), Sp, theta, Open, t, Close);
        Formula mellinKernel = Seq(
            complexT, Caret, Grp(s, Minus, D(1)));
        Formula leftIntegral = Call(
            "setIntegral",
            Call("Ioc", D(0), D(1)),
            Seq(mellinKernel, Sp, residual, Open, t, Close));
        Formula rightIntegral = Call(
            "setIntegral",
            Call("Ioi", D(1)),
            Seq(mellinKernel, Sp, theta, Open, t, Close));
        Formula poleSum = Seq(
            Sum, Underscore, Grp(j, Colon, finM), Sp,
            Frac,
            Grp(coefficient, Open, j, Close),
            Grp(s, Minus, exponentJ));
        Formula continuedAtS = Seq(
            leftIntegral, Sp, Plus, Sp, rightIntegral, Sp, Plus, Sp, poleSum);
        Formula residualPower = Seq(
            t, Caret, Grp(Minus, alphaLast));
        Formula exponentialDecay = Seq(
            F.Id("exp"), Open, Minus, decay, Sp, t, Close);
        Formula halfPlane = Seq(
            OpenBrace, s, Sp, InMacro, Sp, complex, Colon, Sp,
            alphaLast, Sp, Lt, Sp, Re, Open, s, Close, CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(m, natural), Comma, Sp,
                Typed(theta, thetaType), Comma, Sp,
                Typed(coefficient, coefficientType), Comma),
            Seq(
                Grp(), Typed(exponent, exponentType), Comma, Sp,
                Typed(decay, real), Semi),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(residual, thetaType), Comma, Sp,
                residual, Open, t, Close, Sp, Eq, Sp, residualAtT, Semi),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(regularized, thetaType), Comma, Sp,
                regularized, Open, t, Close, Sp, Eq, Sp, regularizedAtT, Semi),
            Seq(
                Grp(), F.Id("let"), Sp,
                Typed(continued, Seq(complex, To, complex)), Comma, Sp,
                continued, Open, s, Close, Sp, Eq, Sp, continuedAtS, Semi),
            Seq(
                Grp(), Call("StrictAnti", exponent), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, decay, Sp, Land),
            Seq(
                Grp(), Call("LocallyIntegrableOn", regularized, Call("Ioi", D(0))),
                Sp, Land),
            Seq(
                Grp(), Call(
                    "IsBigO",
                    Seq(F.Id("nhdsWithin"), Open, D(0), Comma, Sp, Call("Ioi", D(0)), Close),
                    residual,
                    Seq(t, Mapsto, Sp, residualPower)), Sp, Land),
            Seq(
                Grp(), Call(
                    "IsBigO",
                    F.Id("atTop"),
                    theta,
                    Seq(t, Mapsto, Sp, exponentialDecay)),
                Sp, Rightarrow),
            Seq(
                Grp(), Call("MeromorphicOn", continued, halfPlane), Sp, Land),
            Seq(
                Grp(), Forall, Sp, Typed(s, complex), Comma, Sp,
                exponent, Open, D(0), Close, Sp, Lt, Sp, Re, Open, s, Close,
                Sp, Rightarrow, Sp,
                Call("MellinConvergent", theta, s), Sp, Land, Sp,
                continued, Open, s, Close, Sp, Eq, Sp,
                Call("mellin", theta, s), Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
