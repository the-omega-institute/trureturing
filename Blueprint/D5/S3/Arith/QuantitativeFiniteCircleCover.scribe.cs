using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class QuantitativeFiniteCircleCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/QuantitativeFiniteCircleCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite block of a circle rotation meets every open interval of the specified length "
            + "when the explicit small-denominator obstructions are absent.",
        H("Quantitative finite circle cover"),
        Blocks(
            Paragraph(Text(
                "This document records the finite-window theorem and its exact hypotheses. "
                + "The source keeps the bounded integer block and explicit finite obstruction family. "
                + "All occurrences of natural or integer variables inside real expressions "
                + "use the canonical real casts. The ceiling is the integer ceiling Int.ceil, "
                + "so H = ceil(4/w) is an integer. No irrationality hypothesis is imposed.")),
            Describe.Lean(
                DescribeId.Create("quantitative-finite-circle-cover"),
                DeclarationHandle.Create(Prefix + "quantitative_finite_circle_cover"),
                H("The fully quantified finite window theorem"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use Real.exists_rat_abs_sub_le_and_den_le with n=N. It supplies "
                        + "a reduced rational r=p/q, 1<=q<=N, and "
                        + "|theta-r|<=1/((N+1)q). Multiplication by q gives "
                        + "|q theta-p|<=1/(N+1)<=1/N. The stated obstruction hypothesis "
                        + "therefore excludes q<=H, so q>H>=4/w. No upper bound on w is used.")),
                    Paragraph(Text(
                        "For x=t+w/2-N theta, put j=round(qx). Rat.reduced and "
                        + "Int.isCoprime_iff_nat_coprime give integers u,v with up+vq=1. "
                        + "Take k=(uj mod q).toNat, d=(uj)/q using Euclidean integer division, "
                        + "and ell=-(vj+pd). Then 0<=k<q and kp-ell q=j. Hence "
                        + "|kp/q-ell-x|<=1/(2q). The proof constructs both k and ell; "
                        + "it does not replace the finite window by qualitative density.")),
                    Paragraph(Text(
                        "Since k<q, perturbing the rational grid costs at most "
                        + "k|theta-r|<=1/(N+1)<=1/N. The total error is at most "
                        + "1/(2q)+1/N < w/8+w/4=3w/8<w/2. Setting b=N+k yields "
                        + "N<=b< N+q<=2N and t<b theta-ell<t+w, including rational theta.")),
                    Paragraph(Text(
                        "Research attribution: the completed Pro input "
                        + "non-dyadic-actual-price-power-followup.answer.txt, finite-circle "
                        + "lemma (28), gives this reduced-denominator grid argument. "
                        + "Its intended actual application is theta=alpha_3/alpha_2, "
                        + "N_e=floor(kappa*zeta*Tbar_e^(nu-sigma)*Lbar_e^2), "
                        + "w_e=zeta*taubar_(sigma,e)/64, and H_e=ceil(4/w_e). "
                        + "The covering lemma applies only after its budget and finite "
                        + "nonresonance premises have been established for those actual parameters. "
                        + "The original all-B/all-record/RH power-scale goal remains open."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Ceil(Formula value) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("ceil"))), [value]);

    private static Formula Statement()
    {
        Formula theta = F.Id("theta"), t = F.Id("t"), w = F.Id("w"), n = F.Id("N");
        Formula h = F.Id("h"), a = F.Id("a"), b = F.Id("b"), ell = F.Id("ell");
        Formula nonresonance = All("h", Integers(), All("a", Integers(),
            Imp(Le(D(1), h), Imp(Le(h, Ceil(Div(D(4), w))),
                Lt(Div(D(1), n), new Formula.Absolute(Sub(Mul(h, theta), a)))))));
        Formula liftedPoint = Sub(Mul(b, theta), ell);
        Formula witnesses = Ex("b", Naturals(), And(Le(n, b),
            And(Le(b, Mul(D(2), n)), Ex("ell", Integers(),
                And(Lt(t, liftedPoint), Lt(liftedPoint, Add(t, w)))))));
        return All("theta", Reals(), All("t", Reals(), All("w", Reals(), All("N", Naturals(),
            Imp(Lt(D(0), w),
                Imp(Le(Div(D(4), w), n), Imp(nonresonance, witnesses)))))));
    }
}
