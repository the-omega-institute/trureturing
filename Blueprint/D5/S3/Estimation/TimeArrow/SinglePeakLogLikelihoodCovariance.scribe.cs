using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class SinglePeakLogLikelihoodCovarianceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly started paths of the single-peak kernel have explicit one-step moments, "
            + "finite-range log-likelihood covariances, and an exact path-sum variance.",
        H("Single-Peak Log-Likelihood Covariances"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-peak-log-mean-function"),
                DeclarationHandle.Create(Module + "phi"),
                H("Even log-likelihood mean function"),
                StatementSource.FromAuthor(PhiFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function phi is the even weighted logarithmic mean associated with a signed "
                        + "transition bias u."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-log-odd-function"),
                DeclarationHandle.Create(Module + "xi"),
                H("Odd weighted log-likelihood function"),
                StatementSource.FromAuthor(XiFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function xi is the odd part of the same weighted logarithmic expression."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-log-second-moment-function"),
                DeclarationHandle.Create(Module + "psi"),
                H("Even log-likelihood second-moment function"),
                StatementSource.FromAuthor(PsiFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function psi is the even weighted second moment of the logarithmic increment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-start-path-weight"),
                DeclarationHandle.Create(Module + "pathWeight"),
                H("Uniform-start path weight"),
                StatementSource.FromAuthor(PathWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A path of s transitions starts with mass one over the cardinality of X and is weighted "
                        + "by the product of its transition factors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-path-expectation"),
                DeclarationHandle.Create(Module + "pathExpectation"),
                H("Finite-path expectation"),
                StatementSource.FromAuthor(PathExpectationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expectation is the explicit finite sum of a path observable against the uniform-start "
                        + "path weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-log-increment"),
                DeclarationHandle.Create(Module + "logIncrement"),
                H("Single-step log-likelihood increment"),
                StatementSource.FromAuthor(LogIncrementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At time t, the increment is the logarithm of the state-space cardinality times the "
                        + "single-peak transition weight along that edge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-path-covariance"),
                DeclarationHandle.Create(Module + "pathCovariance"),
                H("Finite-path covariance"),
                StatementSource.FromAuthor(PathCovarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The covariance of two path observables is their product expectation minus the product "
                        + "of their expectations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-path-variance"),
                DeclarationHandle.Create(Module + "pathVariance"),
                H("Finite-path variance"),
                StatementSource.FromAuthor(PathVarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The variance of a path observable is its covariance with itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-peak-log-likelihood-sum"),
                DeclarationHandle.Create(Module + "logLikelihoodSum"),
                H("Finite log-likelihood sum"),
                StatementSource.FromAuthor(LogLikelihoodSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite log-likelihood sum adds the increments over all edges of the path."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-single-peak-log-likelihood-covariances"),
                DeclarationHandle.Create(Module + "exact_single_peak_log_likelihood_covariances"),
                H("Exact single-peak log-likelihood covariances"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite sign space of cardinality 2M, with exactly M positive signs and a "
                            + "distinguished positive state z. Assume M is at least two, 0 < r < 1, and "
                            + "q = r/(M - 1). The outgoing conditional mean is phi of the local profile, "
                            + "while the incoming conditional mean is I + J chi(y).")),
                    Paragraph(Text(
                        "Under the explicit uniform-start path weights, the edge at every time n has mean I. "
                            + "The adjacent covariance is I J, every covariance at lag at least two is zero, "
                            + "and the variance of the sum over s edges is s v + 2(s - 1) I J for s at least one.")),
                    Paragraph(Text(
                        "The lag cutoff follows from the two-step transition identity: after two transitions, "
                            + "the endpoint is uniform independently of the starting state. The variance then "
                            + "accumulates one-edge second moments and the single adjacent covariance."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Pow(Formula value, byte power) => new Formula.Power(value, Grp(D(power)));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);
    private static Formula RealType() => Seq(Mathbb, Sp, Grp(F.Id("R")));
    private static Formula NatType() => Seq(Mathbb, Sp, Grp(F.Id("N")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Card(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula At(Formula path, Formula index) => Sub(path, index);
    private static Formula LogOf(Formula value) => Seq(Log, Sp, Open, value, Close);
    private static Formula Let(Formula name, Formula value) =>
        Seq(F.Id("let"), Sp, name, Sp, Eq, Sp, value, Semi, Sp);
    private static Formula SumOver(Formula index, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, body);
    private static Formula ProductOver(Formula index, Formula domain, Formula body) =>
        Seq(Prod, Sp, Underscore, Grp(index, Sp, InMacro, Sp, domain), Sp, body);

    private static Formula PhiFormula()
    {
        Formula u = F.Id("u");
        return Disp(Seq(Forall, Sp, u, Sp, InMacro, Sp, RealType(), Comma, Sp,
            Call("phi", u), Sp, Eq, Sp,
            Fr(Seq(Open, D(1), Plus, u, Close, Sp, LogOf(Seq(D(1), Plus, u)), Plus,
                Open, D(1), Minus, u, Close, Sp, LogOf(Seq(D(1), Minus, u))), D(2))));
    }

    private static Formula XiFormula()
    {
        Formula u = F.Id("u");
        return Disp(Seq(Forall, Sp, u, Sp, InMacro, Sp, RealType(), Comma, Sp,
            Call("xi", u), Sp, Eq, Sp,
            Fr(Seq(Open, D(1), Plus, u, Close, Sp, LogOf(Seq(D(1), Plus, u)), Minus,
                Open, D(1), Minus, u, Close, Sp, LogOf(Seq(D(1), Minus, u))), D(2))));
    }

    private static Formula PsiFormula()
    {
        Formula u = F.Id("u");
        return Disp(Seq(Forall, Sp, u, Sp, InMacro, Sp, RealType(), Comma, Sp,
            Call("psi", u), Sp, Eq, Sp,
            Fr(Seq(Open, D(1), Plus, u, Close, Sp, Pow(LogOf(Seq(D(1), Plus, u)), 2), Plus,
                Open, D(1), Minus, u, Close, Sp, Pow(LogOf(Seq(D(1), Minus, u)), 2)), D(2))));
    }

    private static Formula PathWeightFormula()
    {
        Formula x = F.Id("x"), t = F.Id("t"), s = F.Id("s"), p = F.Id("P"), carrier = F.Id("X");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(p, Arrow(carrier, Arrow(carrier, RealType()))), Comma, Sp,
            s, Sp, InMacro, Sp, NatType(), Comma, Sp, Typed(x, path), Comma, Sp,
            Call("pathWeight", p, s, x), Sp, Eq, Sp, Fr(D(1), Card(carrier)), Sp,
            ProductOver(t, Fin(s), Call("P", At(x, t), At(x, Seq(t, Plus, D(1)))))));
    }

    private static Formula PathExpectationFormula()
    {
        Formula x = F.Id("x"), s = F.Id("s"), p = F.Id("P"), f = F.Id("f"), carrier = F.Id("X");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(p, Arrow(carrier, Arrow(carrier, RealType()))), Comma, Sp,
            s, Sp, InMacro, Sp, NatType(), Comma, Sp, Typed(f, Arrow(Seq(Open, path, Close), RealType())), Comma, Sp,
            Call("pathExpectation", p, s, f), Sp, Eq, Sp,
            SumOver(x, path, Seq(Call("pathWeight", p, s, x), Sp, Call("f", x)))));
    }

    private static Formula LogIncrementFormula()
    {
        Formula x = F.Id("x"), t = F.Id("t"), s = F.Id("s"), carrier = F.Id("X");
        Formula chi = F.Id("chi"), z = F.Id("z"), r = F.Id("r"), q = F.Id("q");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(chi, Arrow(carrier, RealType())), Comma, Sp, Typed(z, carrier), Comma, Sp,
            r, Comma, Sp, q, Sp, InMacro, Sp, RealType(), Comma, Sp, s, Sp, InMacro, Sp, NatType(),
            Comma, Sp, t, Sp, InMacro, Sp, Fin(s), Comma, Sp, Typed(x, path), Comma, Sp,
            Call("logIncrement", chi, z, r, q, t, x), Sp, Eq, Sp,
            LogOf(Seq(Card(carrier), Call("kernel", chi, z, r, q, Card(carrier),
                At(x, t), At(x, Seq(t, Plus, D(1))))))));
    }

    private static Formula PathCovarianceFormula()
    {
        Formula s = F.Id("s"), p = F.Id("P"), f = F.Id("f"), g = F.Id("g"), carrier = F.Id("X");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        Formula observable = Arrow(Seq(Open, path, Close), RealType());
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(p, Arrow(carrier, Arrow(carrier, RealType()))), Comma, Sp,
            s, Sp, InMacro, Sp, NatType(), Comma, Sp, f, Comma, Sp, g, Sp, InMacro, Sp, observable,
            Comma, Sp, Call("pathCovariance", p, s, f, g), Sp, Eq, Sp,
            Call("pathExpectation", p, s, Seq(f, Sp, g)), Minus,
            Call("pathExpectation", p, s, f), Sp, Call("pathExpectation", p, s, g)));
    }

    private static Formula PathVarianceFormula()
    {
        Formula s = F.Id("s"), p = F.Id("P"), f = F.Id("f"), carrier = F.Id("X");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(p, Arrow(carrier, Arrow(carrier, RealType()))), Comma, Sp,
            s, Sp, InMacro, Sp, NatType(), Comma, Sp, Typed(f, Arrow(Seq(Open, path, Close), RealType())), Comma, Sp,
            Call("pathVariance", p, s, f), Sp, Eq, Sp, Call("pathCovariance", p, s, f, f)));
    }

    private static Formula LogLikelihoodSumFormula()
    {
        Formula x = F.Id("x"), t = F.Id("t"), s = F.Id("s"), carrier = F.Id("X");
        Formula chi = F.Id("chi"), z = F.Id("z"), r = F.Id("r"), q = F.Id("q");
        Formula path = Arrow(Fin(Seq(s, Plus, D(1))), carrier);
        return Disp(Seq(Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier),
            Comma, Sp, Typed(chi, Arrow(carrier, RealType())), Comma, Sp, Typed(z, carrier), Comma, Sp,
            r, Comma, Sp, q, Sp, InMacro, Sp, RealType(), Comma, Sp, s, Sp, InMacro, Sp, NatType(),
            Comma, Sp, Typed(x, path), Comma, Sp,
            Call("logLikelihoodSum", chi, z, r, q, s, x), Sp, Eq, Sp,
            SumOver(t, Fin(s), Call("logIncrement", chi, z, r, q, t, x))));
    }

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X"), chi = F.Id("chi"), z = F.Id("z");
        Formula r = F.Id("r"), q = F.Id("q"), m = F.Id("M"), x = F.Id("x"), y = F.Id("y");
        Formula p = F.Id("P"), l = F.Id("L"), k = F.Id("k"), i = F.Id("I"), jconst = F.Id("J");
        Formula v = F.Id("v"), n = F.Id("n"), lag = F.Id("j"), s = F.Id("s"), t = F.Id("t");
        Formula ell = Seq(Ell, Sp);
        Formula positiveSet = Seq(OpenBrace, x, Sp, InMacro, Sp, carrier, Colon, Sp,
            Call("chi", x), Sp, Eq, Sp, D(1), CloseBrace);
        Formula outgoing = SumOver(y, carrier, Seq(Call("P", x, y), Sp, Call("L", x, y)));
        Formula incoming = SumOver(x, carrier, Seq(Call("P", x, y), Sp, Call("L", x, y)));
        Formula ellAt = Sub(ell, t);
        Formula sumEll = SumOver(t, Fin(s), Sub(ell, t));

        return Disp(Seq(
            Begin, Sp, Grp(F.Id("aligned")),
            Amp, Forall, Sp, Typed(carrier, F.Id("Type")), Comma, Sp, Call("Fintype", carrier), Comma, Sp,
            Typed(chi, Arrow(carrier, RealType())), Comma, Sp, Typed(z, carrier), Comma, Sp,
            r, Comma, Sp, q, Sp, InMacro, Sp, RealType(), Comma, Sp, m, Sp, InMacro, Sp, NatType(), Comma,
            RowBreak, Sp,
            Amp, Open, Forall, Sp, x, Sp, InMacro, Sp, carrier, Comma, Sp,
            Call("chi", x), Sp, Eq, Sp, D(1), Sp, Lor, Sp, Call("chi", x), Sp, Eq, Sp, Minus, D(1), Close,
            Sp, Land, Sp, Call("chi", z), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Land, Sp, r, Sp, Lt, Sp, D(1), Comma, RowBreak, Sp,
            Amp, Card(carrier), Sp, Eq, Sp, D(2), Sp, m, Sp, Land, Sp,
            Card(positiveSet), Sp, Eq, Sp, m, Sp, Land, Sp, D(2), Sp, Leq, Sp, m, Sp, Land, Sp,
            q, Sp, Eq, Sp, Fr(r, Seq(m, Minus, D(1))), Sp, Rightarrow, Sp, RowBreak, Sp,
            Amp, Let(p, Call("kernel", chi, z, r, q, Card(carrier))),
            Let(Call("L", x, y), LogOf(Seq(Card(carrier), Call("P", x, y)))), RowBreak, Sp,
            Amp, Let(k, Seq(m, Minus, D(1))),
            Let(i, Fr(Seq(Call("phi", r), Plus, k, Sp, Call("phi", q)), Card(carrier))), RowBreak, Sp,
            Amp, Let(jconst, Fr(Seq(Call("xi", r), Minus, k, Sp, Call("xi", q)), Card(carrier))),
            Let(v, Seq(Fr(Seq(Call("psi", r), Plus, k, Sp, Call("psi", q)), Card(carrier)),
                Minus, Pow(i, 2))), RowBreak, Sp,
            Amp, Let(ellAt, LogOf(Seq(Card(carrier), Call("P", At(x, t), At(x, Seq(t, Plus, D(1))))))),
            Open, Forall, Sp, x, Sp, InMacro, Sp, carrier, Comma, Sp, outgoing, Sp, Eq, Sp,
            Call("phi", Call("profile", chi, z, r, q, x)), Close, Sp, Land, Sp, RowBreak, Sp,
            Amp, Open, Forall, Sp, y, Sp, InMacro, Sp, carrier, Comma, Sp, incoming, Sp, Eq, Sp,
            i, Plus, jconst, Sp, Call("chi", y), Close, Sp, Land, Sp, RowBreak, Sp,
            Amp, Open, Forall, Sp, n, Sp, InMacro, Sp, NatType(), Comma, Sp,
            Call("pathExpectation", p, Seq(n, Plus, D(1)), Sub(ell, n)), Sp, Eq, Sp, i, Close,
            Sp, Land, Sp, RowBreak, Sp,
            Amp, Call("pathCovariance", p, D(2), Sub(ell, D(0)), Sub(ell, D(1))), Sp, Eq, Sp,
            i, Sp, jconst, Sp, Land, Sp, RowBreak, Sp,
            Amp, Open, Forall, Sp, lag, Sp, InMacro, Sp, NatType(), Comma, Sp,
            D(2), Sp, Leq, Sp, lag, Sp, Rightarrow, Sp,
            Call("pathCovariance", p, Seq(lag, Plus, D(1)), Sub(ell, D(0)), Sub(ell, lag)),
            Sp, Eq, Sp, D(0), Close, Sp, Land, Sp, RowBreak, Sp,
            Amp, Forall, Sp, s, Sp, InMacro, Sp, NatType(), Comma, Sp,
            D(1), Sp, Leq, Sp, s, Sp, Rightarrow, Sp,
            Call("pathVariance", p, s, sumEll), Sp, Eq, Sp,
            s, Sp, v, Plus, D(2), Sp, Open, s, Minus, D(1), Close, Sp, i, Sp, jconst,
            End, Sp, Grp(F.Id("aligned"))));
    }
}
