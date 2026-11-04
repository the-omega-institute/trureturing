using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Interpolation;

internal sealed class PositiveJJExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Fibonacci reciprocal data cannot interpolate across the original JJ clocks.",
        H("Positive JJ reciprocal interpolation exclusion"),
        Blocks(
            Paragraph(Text(
                "Let m and a be nonnegative integers, with m at least five and a at most K=2m-2. "
                + "Let r be a positive real number and let u be the actual sequence with u(0)=1, "
                + "u(1)=-r and u(k+2)=u(k+1)+u(k). The prefix evaluates a polynomial at clocks "
                + "0 through a, while the suffix evaluates it at clocks a+2 through K+2. "
                + "The exponent a therefore supplies two equations, at the distinct clocks a and a+2.")),
            Describe.Lean(
                DescribeId.Create("positive-jj-reciprocal-exclusion"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Interpolation/PositiveJJExclusion.positive_jj_exclusion"),
                H("Full original-clock interpolation obstruction"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The degree bound includes constants and every lower actual degree. "
                        + "Since the prefix contains clock zero, any candidate has R(0)=1 and is nonzero. "
                        + "For nonzero real polynomials, natDegree is the ordinary degree. "
                        + "Natural m and a represent exactly the integer ranges in the statement. "
                        + "Every sampled denominator through K is required to be nonzero; no further "
                        + "parameter, parity, root or determinant premise is imposed.")),
                    Paragraph(Text(
                        "The Fibonacci solution-space decomposition gives u(k)=A phi^k+B psi^k, "
                        + "where phi is the positive golden ratio, psi its negative conjugate, and B>0. "
                        + "Let s be the left index of the first same-sign pair before K, or set s=K "
                        + "if there is no such pair. Before s, adjacent values have opposite signs. "
                        + "A same-sign pair gives A u(s)>0 through "
                        + "u(s+1)-psi u(s)=A phi^s(phi-psi); the recurrence then gives A u(k)>0 "
                        + "for every k at least s. Thus A is nonzero whenever this tail is used.")),
                    Paragraph(Text(
                        "Put H(t)=exp(log(phi)t)R(t) and Q=R'+log(phi)R. "
                        + "Then H'(t)=exp(log(phi)t)Q(t). The coefficient of Q at the actual degree "
                        + "of R is log(phi) times the nonzero leading coefficient of R. "
                        + "Consequently Q is nonzero and its degree is at most that of R, including "
                        + "the constant case. On a block shifted by h=0 or h=2, the interpolation "
                        + "equations give (A u(k))(H(k+h)-phi^h/A)=-phi^h B psi^k. "
                        + "Its consecutive residuals have opposite signs on the same-sign tail. "
                        + "Before the transition, the values of H themselves have opposite signs.")),
                    Paragraph(Text(
                        "If s is at most a, use the open intervals (0,s), (s,a) and (a+2,K+2), "
                        + "with edge counts s, a-s and K-a. If a is less than s, use (0,a), "
                        + "(a+2,s+2) and (s+2,K+2), with counts a, s-a and K-s. "
                        + "These intervals are disjoint in either case, and the counts sum to K. "
                        + "An alternating block with n edges gives n distinct level crossings by the "
                        + "intermediate value theorem; Rolle interleaving gives n at most one plus "
                        + "the number of roots of Q in that interval. This inequality also holds "
                        + "for an empty block. Summing gives K at most deg(Q)+3, and hence "
                        + "2m-2 at most m+2, contradicting m at least five.")),
                    Paragraph(Text(
                        "The two shifted levels are differentiated separately; no crossing across "
                        + "the omitted-clock gap is counted. Both transition parities and the case "
                        + "with no same-sign pair are included. The exponential is an auxiliary "
                        + "function in the proof and adds no acquisition or observation.")),
                    Paragraph(Text(
                        "Excluding interpolation excludes any criterion that requires these same "
                        + "equations together with a separate determinant condition. It determines "
                        + "no determinant value, sign or singularity. The fixed-word gain-ray "
                        + "application additionally uses the critical mixed-word classification: "
                        + "its acquisition word and countable matrix palette are preassigned, "
                        + "and different words or palettes may have different failure worlds. "
                        + "No adaptive, common-world, complete-target, calibration or physical "
                        + "resource conclusion is supplied by the auxiliary weight."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var r = F.Id("r");
        var u = F.Id("u");
        var p = F.Id("R");
        var k = F.Id("k");
        var K = Subtract(Multiply(D(2), m), D(2));
        Formula U(Formula t) => new Formula.Apply(u, [t]);
        Formula R(Formula t) => Call("eval", p, t);
        var recurrence = All("k", Naturals(),
            Equal(U(Add(k, D(2))), Add(U(Add(k, D(1))), U(k))));
        var assumptions = And(Le(D(5), m), And(Le(a, K), And(Lt(D(0), r),
            And(Equal(U(D(0)), D(1)), And(Equal(U(D(1)), new Formula.Negate(r)), recurrence)))));
        var candidate = And(Le(Call("natDegree", p), Subtract(m, D(1))),
            And(All("k", Naturals(), Imp(Le(k, K), NotEqual(U(k), D(0)))),
                And(All("k", Naturals(), Imp(Le(k, a), Equal(Multiply(U(k), R(k)), D(1)))),
                    All("k", Naturals(), Imp(Le(a, k), Imp(Le(k, K),
                        Equal(Multiply(U(k), R(Add(k, D(2)))), D(1))))))));
        return All("m", Naturals(), All("a", Naturals(), All("r", Reals(),
            All("u", new Formula.TypeArrow(Naturals(), Reals()),
                Imp(assumptions, new Formula.Not(new Formula.Bind(
                    FormulaQuantifier.Exists, FormulaIdentifier.Create("R"),
                    Call("Polynomial", Reals()), candidate)))))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
