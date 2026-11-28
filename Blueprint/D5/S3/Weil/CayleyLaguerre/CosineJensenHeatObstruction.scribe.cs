using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class CosineJensenHeatObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/CayleyLaguerre/CosineJensenHeatObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive derivative shifts alone do not detect nonreal zeros, even along an exact backward heat flow.",
        H("A Heat-Flow Obstruction to Omitting Jensen Shift Zero"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cosine-heat"),
                DeclarationHandle.Create(Prefix + "cosineHeat"),
                H("The cosine heat family"),
                StatementSource.FromAuthor(HeatFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The time variable is allowed to be complex as an analytic extension. "
                    + "On real time slices, this is a finite Fourier source with a constant "
                    + "mode and two opposite frequencies. It is a model family, not the theta source.")),
                    Paragraph(Text(
                        "Newman and Wu discuss the case proportional to exp(t) cos(z)+2 in "
                        + "Constants of de Bruijn-Newman type in analytic number theory and statistical "
                        + "physics, section 3.2.1, Case 2 (https://arxiv.org/abs/1901.06596). "
                        + "The present statement links this model to the full Taylor Jensen rows; "
                        + "no mathematical priority is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cosine-heat-jet"),
                DeclarationHandle.Create(Prefix + "cosineHeatJet"),
                H("Full Taylor derivatives"),
                StatementSource.FromAuthor(JetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient sequence consists of the actual real derivatives at zero. "
                    + "Every derivative order is retained. For a positive order k its value is "
                    + "exp(t) times the real part of i to the power k; the constant mode disappears. "
                    + "This convention differs from reindexing only the even derivatives."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-shift-heat-counterexample"),
                DeclarationHandle.Create(Prefix + "positive_shift_heat_counterexample"),
                H("All positive shifts coexist with a nonreal source zero"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here Ht and Hzz denote the first time derivative and second spatial "
                        + "derivative of H. The first clause is the exact backward heat equation. "
                        + "The polynomial J is the repository's binomial Jensen transform of gamma. "
                        + "For a fixed nonzero y and chosen real time t, set c=exp(t) cosh(y). "
                        + "This single family has every positive-degree, positive-shift row "
                        + "hyperbolic at every real time, while pi+i*y is a nonreal zero at time t.")),
                    Paragraph(Text(
                        "The complex evaluation of twice a positive-shift row is exp(u) times "
                        + "the sum i^n(1+i*z)^d+(-i)^n(1-i*z)^d. At a zero, the two summands "
                        + "have equal norm. Since d is positive, their affine factors also have "
                        + "equal norm. Their squared norms differ by minus four times Im(z), "
                        + "so every polynomial root is real. The source zero follows instead "
                        + "from cos(pi+i*y)=-cosh(y).")),
                    Paragraph(Text(
                        "The exact row classification includes degree zero: even positive shifts "
                        + "give nonzero constants, whereas odd shifts give the zero polynomial, "
                        + "which fails the stated root-location predicate. The conclusion "
                        + "identifies information lost by omitting shift zero when hyperbolicity "
                        + "alone is used. The full Taylor sequence has alternating even derivatives, "
                        + "so the model does not satisfy a separate nonnegative-coefficient premise. It does not "
                        + "establish a criterion or collision threshold for the actual theta heat flow, "
                        + "nor does it prove the sharp finite-degree secant thresholds for shift zero."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args)
    {
        var result = args[0];
        for (var i = 1; i < args.Length; i++) result = Seq(result, Comma, Sp, args[i]);
        return result;
    }
    private static Formula All(string names, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(names), InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);

    private static Formula HeatFormula()
    {
        var c = F.Id("c"); var t = F.Id("t"); var z = F.Id("z");
        return Disp(All("c", Real, All("t", Complex, All("z", Complex,
            Equal(Call("H", c, t, z), Seq(Call("exp", t), Sp, Call("cos", z), Sp, Plus, Sp, c))))));
    }

    private static Formula JetFormula()
    {
        var c = F.Id("c"); var t = F.Id("t"); var k = F.Id("k"); var x = F.Id("x");
        var function = Seq(x, Sp, Mapsto, Sp, Call("exp", t), Sp, Call("cos", x), Sp, Plus, Sp, c);
        return Disp(All("c", Real, All("t", Real, All("k", Natural,
            Equal(Call("gamma", c, t, k), Call("iteratedDeriv", k, function, D(0)))))));
    }

    private static Formula CounterexampleFormula()
    {
        var t = F.Id("t"); var y = F.Id("y"); var c = F.Id("c");
        var u = F.Id("u"); var z = F.Id("z"); var d = F.Id("d"); var n = F.Id("n");
        var root = Seq(Pi, Sp, Plus, Sp, F.Id("i"), Sp, y);
        var equation = All("u", Complex, All("z", Complex,
            Equal(Call("Ht", c, u, z), Seq(Minus, Call("Hzz", c, u, z)))));
        var tower = All("u", Real, All("d", Natural, All("n", Natural,
            Seq(D(0), Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
                Open, Call("Hyperbolic", Call("J", Call("gamma", c, u), d, n)),
                Sp, Iff, Sp, Open, D(0), Sp, Lt, Sp, d, Sp, Lor, Sp, Call("Even", n), Close, Close))));
        return Disp(All("t", Real, All("y", Real,
            Seq(y, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                Operatorname, Grp(F.Id("let")), Sp, c, Sp, Eq, Sp,
                Call("exp", t), Sp, Call("cosh", y), Semi, Sp,
                Open, equation, Close, Sp, Land, Sp,
                Open, tower, Close, Sp, Land, Sp,
                Equal(Call("H", c, t, root), D(0)), Sp, Land, Sp,
                Call("Im", root), Sp, Neq, Sp, D(0)))));
    }
}
