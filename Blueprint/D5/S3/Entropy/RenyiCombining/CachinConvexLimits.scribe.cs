using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexLimitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinConvexLimits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite even jets bound the slope and give strictly negative curvature after square-root reparametrization.",
        H("Finite-Jet Signs at the Square-Root Endpoint"),
        Blocks(
            Paragraph(Text("Let Q be smooth near zero and write Q1, Q2, Q3 and Q4 for its first four "
                + "derivatives. Evenness supplies Q1(0)=Q3(0)=0. If Q2(0)<2k and Q4(0)<0, "
                + "the reparametrized function C(z)=Q(sqrt(z)) has first derivative below k and negative second "
                + "derivatives for all sufficiently small positive z. The formal sign theorem "
                + "takes only the explicitly used derivative chain and endpoint values; it does "
                + "not assume evenness or differentiability of C at zero.")),
            Node("sqrtSlope", "Slope expression", ForFunctions(new[] { "Q1" }, AllReal("z",
                Equal(Call("sqrtSlope", N("Q1"), N("z")), SlopeBody()))), DescribeRole.Definition,
                "The expression is Q1(sqrt(z))/(2 sqrt(z)). It is a total real function; "
                + "its derivative interpretation is asserted only for z>0."),
            Node("sqrtCurvature", "Curvature expression", ForFunctions(new[] { "Q1", "Q2" }, AllReal("z",
                Equal(Call("sqrtCurvature", N("Q1"), N("Q2"), N("z")), CurvatureBody()))),
                DescribeRole.Definition,
                "The numerator is sqrt(z) Q2(sqrt(z))-Q1(sqrt(z)); the denominator is 4 sqrt(z)^3."),
            Node("sqrt_comp_hasDerivAt", "First derivative under square-root reparametrization",
                ForFunctions(new[] { "Q", "Q1" }, AllReal("z",
                    Imp(Lt(D(0), N("z")), Imp(
                        Call("HasDerivAt", N("Q"), Call("Q1", Root()), Root()),
                        Call("HasDerivAt", Call("comp", N("Q"), N("sqrt")),
                            Call("sqrtSlope", N("Q1"), N("z")), N("z")))))),
                DescribeRole.Theorem,
                "For z>0 the square-root derivative and chain rule give the stated slope expression."),
            Node("sqrtSlope_hasDerivAt", "Second derivative under square-root reparametrization",
                ForFunctions(new[] { "Q1", "Q2" }, AllReal("z",
                    Imp(Lt(D(0), N("z")), Imp(
                        Call("HasDerivAt", N("Q1"), Call("Q2", Root()), Root()),
                        Call("HasDerivAt", Call("sqrtSlope", N("Q1")),
                            Call("sqrtCurvature", N("Q1"), N("Q2"), N("z")), N("z")))))),
                DescribeRole.Theorem,
                "The quotient and chain rules give the curvature expression from the first derivative chain."),
            Node("exists_sqrt_jet_negative", "Negative endpoint signs from four finite jets",
                ForFunctions(new[] { "Q1", "Q2", "Q3", "Q4" }, AllReal("a", AllReal("k", Imp(Assumptions(),
                    Seq(Exists, Sp, N("delta"), Colon, Sp, RealType(), Comma, Sp,
                        Conj(Lt(D(0), N("delta")), AllReal("z", Imp(
                            Member(N("z"), Call("Ioo", D(0), N("delta"))),
                            Conj(Lt(Call("sqrtSlope", N("Q1"), N("z")), N("k")),
                                Lt(Call("sqrtCurvature", N("Q1"), N("Q2"), N("z")), D(0))))))))))),
                DescribeRole.Theorem,
                "Continuity makes Q4 negative on a small interval. Since Q3(0)=0, the mean value "
                + "theorem first gives Q3(t)<0. Thus Q2(t)<=Q2(0)<2k and Q1(t)<2kt. "
                + "The derivative of t Q2(t)-Q1(t) is t Q3(t)<0, and this numerator vanishes at zero. "
                + "It is therefore negative for t>0. Substituting t=sqrt(z) and using the positive "
                + "denominators proves both signs without a Taylor remainder or l'Hopital argument."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-limits-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula N(string name) => F.Id(name);
    private static Formula RealType() => Seq(Mathbb, Grp(N("R")));
    private static Formula AllReal(string name, Formula body) =>
        Seq(Forall, Sp, Grp(Seq(N(name), Colon, Sp, RealType())), Comma, Sp, body);
    private static Formula ForFunctions(string[] names, Formula body) {
        for (int i = names.Length - 1; i >= 0; --i)
            body = Seq(Forall, Sp, Grp(Seq(N(names[i]), Colon, Sp, RealType(), Sp, To, Sp, RealType())), Comma, Sp, body);
        return body;
    }
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Grp(premise), FormulaLogicOperator.Implies, conclusion);
    private static Formula Conj(Formula left, Formula right) =>
        new Formula.Logic(Grp(left), FormulaLogicOperator.And, Grp(right));
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Root() => Call("sqrt", N("z"));
    private static Formula SlopeBody() => new Formula.Fraction(Call("Q1", Root()), Multiply(D(2), Root()));
    private static Formula CurvatureBody() => new Formula.Fraction(
        Subtract(Multiply(Root(), Call("Q2", Root())), Call("Q1", Root())),
        Multiply(D(4), new Formula.Power(Root(), D(3))));
    private static Formula DerivativeChain(string first, string second) => AllReal("t", Imp(
        Member(N("t"), Call("Icc", D(0), N("a"))),
        Call("HasDerivAt", N(first), Call(second, N("t")), N("t"))));
    private static Formula Assumptions() {
        Formula result = Conj(Lt(D(0), N("a")), DerivativeChain("Q1", "Q2"));
        result = Conj(result, DerivativeChain("Q2", "Q3"));
        result = Conj(result, DerivativeChain("Q3", "Q4"));
        result = Conj(result, Equal(Call("Q1", D(0)), D(0)));
        result = Conj(result, Equal(Call("Q3", D(0)), D(0)));
        result = Conj(result, Lt(Call("Q2", D(0)), Multiply(D(2), N("k"))));
        result = Conj(result, Call("ContinuousAt", N("Q4"), D(0)));
        return Conj(result, Lt(Call("Q4", D(0)), D(0)));
    }
}
