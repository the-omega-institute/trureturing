using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityCompositionKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/ParityCompositionKernel.";
    private static readonly Formula Dv = F.Id("d"), Mv = F.Id("M"), Hv = F.Id("h");
    private static readonly Formula Xv = F.Id("x"), Cv = F.Id("m"), Jv = F.Id("j");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The composition parity mass and a biased Bernoulli mass have the same prescribed terminal parity.",
        H("Parity Composition Kernels"),
        Blocks(
            Node("actual", "Composition parity mass", "R", ActualFormula(),
                "The parameters d and M are natural numbers, xi : Fin d -> Bool, and h is the sum of the Boolean digits. "
                + "The guard requires h <= M and h mod 2 = M mod 2. The mass is zero when either test fails; "
                + "the binomial coefficient in the nonzero branch is evaluated only for the resulting natural parameters. "
                + "Its numerator counts the weak compositions after subtracting the parity vector and dividing each part by two.",
                DescribeRole.Definition),
            Node("reference", "Conditioned Bernoulli mass", "Q", ReferenceFormula(),
                "Here nu = M/(2M+d), eta = d/(2M+d), and p_e = (1+(-1)^M eta^d)/2. "
                + "The mass is zero when h mod 2 differs from M mod 2. For positive d and M, "
                + "this formula describes independent Bernoulli(nu) bits conditioned on the terminal parity. "
                + "The conditioned bits are not asserted to be independent.", DescribeRole.Definition),
            Node("profile", "Logarithmic profile", "logProfile", ProfileFormula(),
                "The continuous profile is the sum of the logarithms of all d-1 composition factors, "
                + "minus x log(tau), where tau = M/(M+d). The center m = dM/(2M+d) is the mean "
                + "of the unconditioned Bernoulli total, rather than the conditional mean.", DescribeRole.Definition),
            Node("endpoint", "Centered endpoint error", "profile_endpoint", EndpointFormula(),
                "For d >= 2 and M >= 3d, the derivative at m is s = -sum_{j=1}^{d-1} 1/(M-m+2j) - log(tau). "
                + "The integral of 1/(M-m+2y) from zero to d is exactly -log(tau). "
                + "The function is positive and decreasing. Comparing its complete reciprocal sum with the two shifted integrals "
                + "leaves an error between zero and the integral from zero to one, which is at most 1/(M-d).",
                DescribeRole.Theorem),
            Node("estimate", "Full interval profile bound", "profile_estimate", EstimateFormula(),
                "Put Delta = x-m, T = M-d and L = M-d/2. Since m <= d/2, each centered factor a_j = M-m+2j "
                + "satisfies a_j >= L and a_j-|Delta| >= T. The logarithm-series remainder bounds "
                + "|log(1-Delta/a_j)+Delta/a_j| by Delta^2/(L T). Summing all d-1 remainders and using the centered endpoint "
                + "error gives the absolute profile bound. The logarithm tangent inequality gives the signed upper bound, "
                + "and d/(M-d) <= 1/2 gives the final cap. Both bounds cover the whole interval, including both sides of m.",
                DescribeRole.Theorem),
            Node("normalization", "Composition mass normalization", "actual_normalization", NormalizationFormula(),
                "For every positive dimension d and every natural total M, the composition parity masses sum to one. "
                + "The sum runs over all Boolean vectors xi : Fin d -> Bool. The weak compositions of M partition "
                + "according to their complete parity vector. A legal vector with h occupied coordinates has "
                + "exactly choose((M-h)/2+d-1,d-1) preimages, through the bijection r_i = 2t_i + xi_i. "
                + "An illegal vector has no preimages. Summing these fiber counts and dividing by "
                + "the total choose(M+d-1,d-1) proves normalization.", DescribeRole.Theorem),
            Node("moments", "Conditional centered moments", "reference_moments", MomentsFormula(),
                "The independent Bernoulli vector has generating function (1-nu+nu z)^d. "
                + "Its value at z=-1 gives the parity event probability; differentiating twice at z=1 gives "
                + "the centered second moment d nu (1-nu). For M >= 3d, eta <= 1/7 and p_e >= 1/3. "
                + "Restricting the nonnegative squared deviation to the parity event and dividing by p_e "
                + "bounds its conditional expectation by 3d/4. Weighted Cauchy-Schwarz then gives "
                + "the absolute deviation bound sqrt(3d)/2. Both moments are centered at m=d nu.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create("parity-composition-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Parity() => Equal(Call("mod", Hv, D(2)), Call("mod", Mv, D(2)));
    private static Formula ActualFormula() => Equal(Call("R", Dv, Mv, F.Xi),
        Call("ite", And(Parity(), Relation(Hv, Leq, Mv)),
            Ratio(Call("choose", Subtract(Add(Ratio(Subtract(Mv, Hv), D(2)), Dv), D(1)), Subtract(Dv, D(1))),
                Call("choose", Subtract(Add(Mv, Dv), D(1)), Subtract(Dv, D(1)))), D(0)));

    private static Formula ReferenceFormula() => Equal(Call("Q", Dv, Mv, F.Xi),
        Call("ite", Parity(), Ratio(Multiply(Power(F.Nu, Hv),
            Power(Paren(Subtract(D(1), F.Nu)), Subtract(Dv, Hv))), Index(F.Id("p"), F.Id("e"))), D(0)));

    private static Formula ProfileFormula() => Equal(Call("logProfile", Dv, Mv, Xv),
        Subtract(Seq(Index(Sum, Seq(Jv, Eq, D(1))), Caret, Grp(Subtract(Dv, D(1))), Sp,
            Call("log", Add(Subtract(Mv, Xv), Multiply(D(2), Jv)))),
            Multiply(Xv, Call("log", Ratio(Mv, Add(Mv, Dv))))));

    private static Formula EndpointFormula() => Quantified(
        And(Call("HasDerivAt", Call("logProfile", Dv, Mv), F.Id("s"), Cv),
            And(Relation(D(0), Leq, F.Id("s")), Relation(F.Id("s"), Leq, Ratio(D(1), Subtract(Mv, Dv))))));

    private static Formula EstimateFormula()
    {
        Formula gap = Subtract(Call("logProfile", Dv, Mv, Xv), Call("logProfile", Dv, Mv, Cv));
        Formula delta = Subtract(Xv, Cv);
        Formula bound = Add(Ratio(Abs(delta), Subtract(Mv, Dv)),
            Ratio(Multiply(Subtract(Dv, D(1)), Power(Paren(delta), D(2))),
                Multiply(Paren(Subtract(Mv, Ratio(Dv, D(2)))), Paren(Subtract(Mv, Dv)))));
        return Quantified(Seq(Forall, Sp, Xv, Sp, InMacro, Sp, OpenBracket, D(0), Comma, Dv,
            CloseBracket, Comma, Sp, And(Relation(Abs(gap), Leq, bound), Relation(gap, Leq, Ratio(D(1), D(2))))));
    }

    private static Formula MomentsFormula()
    {
        Formula q = Call("Q", Dv, Mv, F.Xi);
        Formula delta = Subtract(Hv, Cv);
        Formula mass = Equal(Seq(Index(Sum, F.Xi), Sp, q), D(1));
        Formula eventBound = Relation(Ratio(D(1), D(3)), Leq, Index(F.Id("p"), F.Id("e")));
        Formula second = Relation(Seq(Index(Sum, F.Xi), Sp, Multiply(q, Power(Paren(delta), D(2)))),
            Leq, Ratio(Multiply(D(3), Dv), D(4)));
        Formula first = Relation(Seq(Index(Sum, F.Xi), Sp, Multiply(q, Abs(delta))),
            Leq, Ratio(Call("sqrt", Multiply(D(3), Dv)), D(2)));
        return Quantified(And(mass, And(eventBound, And(second, first))));
    }

    private static Formula Quantified(Formula body) => Seq(Forall, Sp, Dv, Comma, Mv, Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp, Paren(And(Relation(D(2), Leq, Dv),
            Relation(Multiply(D(3), Dv), Leq, Mv))), Sp, Rightarrow, Sp, body);
    private static Formula NormalizationFormula() => Seq(Forall, Sp, Dv, Comma, Mv, Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp, Relation(D(1), Leq, Dv), Sp, Rightarrow, Sp,
        Equal(Seq(Index(Sum, F.Xi), Sp, Call("R", Dv, Mv, F.Xi)), D(1)));
    private static Formula Relation(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Paren(a), Sp, Land, Sp, Paren(b));
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Power(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Index(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula Abs(Formula a) => Seq(Bar, a, Bar);
}
