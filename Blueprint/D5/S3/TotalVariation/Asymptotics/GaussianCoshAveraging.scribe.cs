using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class GaussianCoshAveragingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Gaussian-cosh local expansion remains a relative approximation after Gaussian averaging in both unbounded source-offset regimes.",
        H("Relative Gaussian averaging of the clipped cosh kernel"),
        Blocks(
            Paragraph(Text("Let phi be the existing standard normal density and J the existing Gaussian-cosh integral. "
                + "All integrals below use Lebesgue measure. All fractional powers are real powers.")),
            Definition("coefficient", "coshCoefficient", "The exact local coefficient",
                All("q", R, Eqn(Call("A", I("q")),
                    Fr(Seq(D(4), Sqrt, Grp(D(2)), PhiAt(D(0))), Seq(D(3), Cdot, Sp, I("q")))))),
            Definition("displacement", "affineOffset", "The shifted affine displacement",
                All("b", R, All("t", R, All("v", R,
                    Eqn(Offset(I("b"), I("t"), I("v")),
                        Seq(I("b"), Cdot, Sp, Grp(Open, I("v"), Minus, I("t"), Close), Minus,
                            Fr(Pow(I("b"), D(2)), D(2)))))))),
            Definition("moment", "positiveMoment", "The actual three-halves moment",
                All("b", R, All("t", R,
                    Eqn(Call("K", I("b"), I("t")), Integral("v", R,
                        Seq(PhiAt(I("v")), Cdot, Sp, PositivePower(Offset(I("b"), I("t"), I("v"))))))))),
            Definition("average", "averagedCosh", "The actual averaged kernel",
                All("q", R, All("b", R, All("t", R,
                    Eqn(Call("N", I("q"), I("b"), I("t")), Integral("v", R,
                        Seq(PhiAt(I("v")), Cdot, Sp,
                            Call("J", I("q"), Offset(I("b"), I("t"), I("v")))))))))),
            Definition("nonlocal-envelope", "nonlocalEnvelope", "The nonlocal exponential envelope",
                All("b", R, All("t", R, All("e", R,
                    Eqn(Call("T", I("b"), I("t"), I("e")),
                        Integral("v", Seq(OpenBrace, I("v"), InMacro, Sp, R, Mid, Sp,
                            I("e"), Lt, Sp, Offset(I("b"), I("t"), I("v")), CloseBrace),
                            Seq(PhiAt(I("v")), Cdot, Sp,
                                Call("exp", Offset(I("b"), I("t"), I("v")))))))))),
            Definition("source-offset", "sourceOffset", "The source normalized offset",
                All("q", R, All("b", R, Eqn(Call("tau", I("q"), I("b")),
                    Fr(Seq(Call("log", D(4)), Minus, Fr(Pow(I("q"), D(2)), D(2))), I("b")))))),
            Paragraph(Text("The integrability clauses use the following three actual functions, with every argument displayed:")),
            Paragraph(Math(Disp(InnerFormula()))),
            Paragraph(Math(Disp(OuterFormula()))),
            Paragraph(Math(Disp(MomentFormula()))),
            Describe.Lean(
                DescribeId.Create("source-relative-limit"),
                DeclarationHandle.Create(Prefix + "gaussian_cosh_source_relative"),
                H("The relative limit in both unbounded regimes"),
                StatementSource.FromAuthor(Disp(SourceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here Q=sqrt(2 log(4)), q(n) and b(n) are positive at every natural index, "
                        + "and t(n)=tau(q(n),b(n)). The formula includes integrability of each inner kernel, "
                        + "the outer kernel and the moment integrand at every index, together with strict "
                        + "positivity of K, A and their product. No asymptotic integral or tail estimate is a hypothesis.")),
                    Paragraph(Text("The nonlocal envelope satisfies T(b(n),t(n),e)/K(b(n),t(n)) tending to zero "
                        + "for every fixed positive e. On the positive side, the change of variables v=t+z/t "
                        + "extracts the common factor phi(t)(b/t)^(3/2)/t. The remaining moment integral tends "
                        + "to the strictly positive integral of z^(3/2) exp(-z) over positive z. The shift is "
                        + "exactly b t/2. The normalized tail is dominated by the cutoff to the power -3/2 times z^(3/2) exp(-z/2) "
                        + "and vanishes pointwise. Thus the exponentially small density factor cancels before taking the ratio.")),
                    Paragraph(Text("On the negative side write t=-L. Division by (bL)^(3/2) leaves the positive "
                        + "part of 1+v/L-b/(2L), raised to the three-halves power. Its Gaussian integral tends "
                        + "to one. The normalized nonlocal envelope is dominated by a constant times "
                        + "phi(v)(1+v^2) exp(1+abs(v)), an integrable function. It also vanishes pointwise.")),
                    Paragraph(Text("Split the error at displacement e. The local remainder is at most C e K. "
                        + "On the nonlocal set, J(d) is at most exp(d) and d^(3/2) is at most 4 exp(d), "
                        + "so the integrated error is at most C e K+(1+4A)T. Divide by the positive A K, "
                        + "use the proved relative tail limit, and let e decrease to zero. The source relation "
                        + "b t=log(4)-q^2/2 supplies b t tending to zero.")),
                    Paragraph(Text("This establishes the analytic averaging formula of equation 14.16. "
                        + "No Bayes identity, moment comparison, full crossover theorem or additional offset regime is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel"))]));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(declaration switch
            {
                "coshCoefficient" => "This coefficient uses the value at zero of the standard normal density.",
                "affineOffset" => "The quadratic shift is part of the displacement at every parameter value.",
                "positiveMoment" => "The positive part is taken before the fractional power and Gaussian integration.",
                "averagedCosh" => "The inner kernel is the actual Gaussian-cosh integral, evaluated at the shifted displacement.",
                "nonlocalEnvelope" => "The integration set is the strict superlevel set of the actual displacement.",
                "sourceOffset" => "The normalized offset uses the same positive parameters as the source sequence.",
                _ => throw new System.ArgumentOutOfRangeException(nameof(declaration))
            }))), DescribeRole.Definition);
    private static Formula I(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(I("R")));
    private static Formula Nat => Seq(Mathbb, Grp(I("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula PhiAt(Formula x) => Seq(Varphi, Open, x, Close);
    private static Formula Clip(Formula x) => Seq(Max, Grp(OpenBrace, x, Comma, D(0), CloseBrace));
    private static Formula PositivePower(Formula x) => Pow(Clip(x), Fr(D(3), D(2)));
    private static Formula Offset(Formula b, Formula t, Formula v) => Call("d", b, t, v);
    private static Formula Integral(string variable, Formula domain, Formula body) =>
        Seq(Int, Underscore, Grp(domain), Sp, body, Sp, I("d" + variable));
    private static Formula Limit(Formula sequence, Formula value) =>
        Seq(Lim, Underscore, Grp(I("n"), To, Sp, Infty), Sp, sequence, Eq, value);
    private static Formula And(params Formula[] parts)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (terms.Count > 0) { terms.Add(Land); terms.Add(Sp); }
            terms.Add(part);
        }
        return Seq([.. terms]);
    }
    private static Formula Positive(Formula x) => Seq(D(0), Lt, Sp, x);
    private static Formula InnerFormula()
    {
        Formula q = I("q"), e = I("e"), u = I("u");
        Formula body = Eqn(Call("inner", q, e, u), Seq(PhiAt(u), Cdot, Sp,
            Clip(Seq(Call("exp", e), Minus, Call("cosh", Seq(q, Cdot, Sp, u))))));
        return All("q", R, All("e", R, All("u", R, body)));
    }
    private static Formula OuterFormula()
    {
        Formula q = I("q"), b = I("b"), t = I("t"), v = I("v");
        Formula body = Eqn(Call("outer", q, b, t, v),
            Seq(PhiAt(v), Cdot, Sp, Call("J", q, Offset(b, t, v))));
        return All("q", R, All("b", R, All("t", R, All("v", R, body))));
    }
    private static Formula MomentFormula()
    {
        Formula b = I("b"), t = I("t"), v = I("v");
        Formula body = Eqn(Call("moment", b, t, v), Seq(PhiAt(v), Cdot, Sp, PositivePower(Offset(b, t, v))));
        return All("b", R, All("t", R, All("v", R, body)));
    }
    private static Formula SourceFormula()
    {
        Formula q = I("q"), b = I("b"), n = I("n"), v = I("v");
        Formula qn = Call("q", n), bn = Call("b", n), tn = Call("tau", qn, bn);
        Formula a = Call("A", qn), k = Call("K", bn, tn);
        Formula qc = Seq(Sqrt, Grp(D(2), Cdot, Sp, Call("log", D(4))));
        Formula hypotheses = And(Grp(Open, All("n", Nat, Positive(qn)), Close),
            Grp(Open, All("n", Nat, Positive(bn)), Close), Limit(qn, qc), Limit(bn, D(0)),
            Grp(Open, Limit(tn, Infty), Lor, Sp, Limit(tn, Seq(Minus, Infty)), Close));
        Formula inner = Grp(Open, All("v", R, Call("Integrable", Call("inner", qn, Offset(bn, tn, v)))), Close);
        Formula leafBody = And(inner, Call("Integrable", Call("outer", qn, bn, tn)),
            Call("Integrable", Call("moment", bn, tn)), Positive(k), Positive(a), Positive(Seq(a, Cdot, Sp, k)));
        Formula leaves = Grp(Open, All("n", Nat, Grp(Open, leafBody, Close)), Close);
        Formula conclusion = And(leaves, Limit(Fr(Call("N", qn, bn, tn), Seq(a, Cdot, Sp, k)), D(1)));
        Formula sequenceType = Seq(Open, Nat, To, Sp, R, Close);
        return All("q", sequenceType, All("b", sequenceType,
            Seq(Grp(Open, hypotheses, Close), Rightarrow, Sp, Grp(Open, conclusion, Close))));
    }
}
