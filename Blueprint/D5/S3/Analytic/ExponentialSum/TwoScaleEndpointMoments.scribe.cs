using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExponentialSum;

internal sealed class TwoScaleEndpointMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform moment concentration for signed two-scale exponential families, including coefficient cancellation.",
        H("Two-scale endpoint moments"), Blocks(
            Describe.Lean(DescribeId.Create("two-scale-exponential-moment"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.exponential_moment"),
                H("Every polynomial moment of a decreasing exponential"),
                StatementSource.FromAuthor(Disp(All("r", R, Imp(
                    new Formula.Relation(new Formula.Number(0), FormulaRelationOperator.LessThan, V("r")),
                    All("k", N, new Formula.Logic(
                        C("MeasureTheory.IntegrableOn", MomentFunction, C("Set.Ioi", new Formula.Number(0))),
                        FormulaLogicOperator.And,
                        new Formula.Relation(
                            C("MeasureTheory.integral", C("Measure.restrict", C("volume"), C("Set.Ioi", new Formula.Number(0))), MomentFunction),
                            FormulaRelationOperator.Equal,
                            new Formula.Fraction(C("Nat.factorial", V("k")),
                                new Formula.Power(Parenthesized(V("r")), new Formula.Binary(V("k"), FormulaBinaryOperator.Add, new Formula.Number(1))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real rate r and natural order k, the polynomially weighted exponential is integrable on the positive ray and its integral equals k! divided by r to the power k+1. The Gamma integral gives both assertions. The exact formula supplies the moments of each exponential term in the two-scale family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-scale-endpoint-moment-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.two_scale_endpoint_moment_bound"),
                H("Uniform moments relative to the same source mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real a, b, endpoint s, and p greater than zero, define F(x)=a exp(-p(x-s))+b exp(-2p(x-s)). For every natural k, the theorem proves integrability of (x-s)^k F(x)^2 on x>s, the coercive mass bound D at least (a^2+b^2)/(54p), and the uniform moment bound M_k at most 54 k! p^(-k) D. Here D and M_k are the actual Lebesgue integrals of this same F on x>s. Both coefficients may depend on p and may have opposite signs.")),
                    Paragraph(Text("With t=p(x-s), the fixed shape is g(t)=a exp(-t)+b exp(-2t). Mathlib's real Gamma integral gives its exact k-th moment as k! times (a^2/2^(k+1)+2ab/3^(k+1)+b^2/4^(k+1)). Its mass is a^2/2+2ab/3+b^2/4. The identity 54D_shape-(a^2+b^2)=((26a+18b)^2+b^2)/26 controls cancellation. The positive moment upper bound is at most k!(a^2+b^2); translation invariance and positive dilation then give the stated estimate.")),
                    Paragraph(Text("Nonzero coefficients therefore give positive mass. At a fixed positive endpoint, these bounds supply concentration of polynomially weighted mass as p tends to infinity. Applying the estimate to an actual Suzuki mean-zero source requires a separate proof of the source's trace condition and relevant domains; those conditions are not assumptions of this moment theorem."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula MomentFunction => Seq(V("t"), Colon, Sp, R, Mapsto, Sp,
        new Formula.Binary(new Formula.Power(Parenthesized(V("t")), V("k")), FormulaBinaryOperator.Multiply,
            C("Real.exp", new Formula.Negate(new Formula.Binary(V("r"), FormulaBinaryOperator.Multiply, V("t"))))));
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
}
