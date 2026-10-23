using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ArithmeticMixedCornerResponseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ArithmeticMixedCornerResponse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual coprime integer corners equal a strictly positive curvature integral with explicit area bounds.",
        H("The Actual Arithmetic Mixed Response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("absolute-margin"), DeclarationHandle.Create(Prefix + "G"),
                H("The absolute logarithmic Robin margin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("G(n)=log(sigma_1(n)/n)-gamma-log(log(log(n))), "
                    + "where gamma is Euler's constant and all logarithms are real natural logarithms. "
                    + "For n>=3 every logarithm argument used here is positive. In particular "
                    + "G(n)<0 is the strict Robin sign on this domain."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-mixed-response"),
                DeclarationHandle.Create(Prefix + "arithmetic_mixed_response"),
                H("Exact transport and quantitative curvature"),
                StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the displayed statement x=log(n), a=log(r), b=log(s), "
                        + "J(n,r,s)=G(n*r*s)+G(n)-G(n*r)-G(n*s), and "
                        + "k(t)=(log(t)+1)/(t^2*log(t)^2). The function k is exactly "
                        + "D5/S3/Arith/Robin/ActualRobinClockCovariance.activationDensity. "
                        + "The theorem also proves x>1, a>0 and b>0. Coprimality is required "
                        + "only between r and s; either or both may share prime factors with n. "
                        + "Thus r=p^i and s=q^j are included for distinct primes p,q and "
                        + "arbitrary positive exponents i,j, including p|n and q|n.")),
                    Paragraph(Text("The arithmetic proof computes gcd(n*r,n*s)=n and "
                        + "lcm(n*r,n*s)=n*r*s. It directly applies Mathlib's "
                        + "ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply to sigma_1. "
                        + "After normalization by the integer arguments, the four log(sigma_1/n) "
                        + "terms cancel; gamma cancels as well. The remaining log-log rectangle "
                        + "is integrated twice using the existing "
                        + "D5/S3/Arith/Robin/ActualRobinClockCovariance.density_integral and "
                        + "Mathlib integral_inv_div_log. Monotonicity of k follows from "
                        + "D5/S3/Arith/Robin/MellinWeightedVariation.scaleWeight_antitone. "
                        + "The endpoint kernel comparisons are integrated over both intervals, "
                        + "giving the area bounds and strict positivity without a response-bound premise.")),
                    Paragraph(Text("The finite response is described in the thermodynamic-action "
                        + "theory, section 16.1, and seams theory, sections 8 through 10. "
                        + "The existing D5/S3/Arith/Robin/LogLogHigherDerivative.signed_iteratedDeriv_logLog_pos supplies "
                        + "higher analytic signs but does not assert this arithmetic transport.")),
                    Paragraph(Text("For n>=3 and the literal five-state menu (n,p*n,q*n,r*n,p*r*n), "
                        + "take d=(G(n),G(p*n),G(q*n),G(r*n),G(p*r*n)), beta>0, and "
                        + "P_s=exp(beta*d_s)/sum_t exp(beta*d_t), with s,t in Fin 5. "
                        + "The definition D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.hiddenChi "
                        + "gives hiddenChi(P)=beta*(G(p*r*n)+G(n)-G(p*n)-G(r*n))=beta*J(n,p,r)>0 "
                        + "for distinct primes p,r and any chosen prime q; the q slot does not enter this contrast. "
                        + "Commutativity identifies the displayed integer addresses with the theorem's corners. "
                        + "D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.mixed_coordinates_global_chart "
                        + "places this law in its global visible-occupancy and hidden-coordinate chart.")),
                    Paragraph(Text("Keep the absolute log partition A0=log(sum_s exp(beta*d_s)). "
                        + "For normalized weights P_s, d_s=(log(P_s)+A0)/beta. "
                        + "The mixed contrast cancels A0, but an absolute Robin sign still needs it. "
                        + "This positive finite response supplies no absolute Robin anchor, "
                        + "menu-external integer control, cofinal tail estimate or strict global margin. "
                        + "The multipliers include prime powers; positivity of their mixed response "
                        + "does not establish their absolute signs. Strict Robin for every n>5040 "
                        + "and RH remain unproved."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), s = F.Id("s");
        Formula x = Call("log", n), a = Call("log", r), b = Call("log", s);
        Formula j = Call("J", n, r, s);
        Formula u = F.Id("u"), v = F.Id("v");
        Formula integral = Seq(Int, Underscore, Grp(D(0)), Caret, Grp(a), Sp,
            Int, Underscore, Grp(D(0)), Caret, Grp(b), Sp,
            Call("k", Add(Add(x, u), v)), Sp, F.Id("d"), v, Sp, F.Id("d"), u);
        Formula premise = And(Le(D(3), n), Le(D(2), r), Le(D(2), s),
            Eq(Call("gcd", r, s), D(1)));
        Formula result = And(Lt(D(1), x), Lt(D(0), a), Lt(D(0), b), Eq(j, integral),
            Lt(D(0), j), Le(Mul(Mul(a, b), Call("k", Add(Add(x, a), b))), j),
            Le(j, Mul(Mul(a, b), Call("k", x))));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), nat),
             new Formula.BoundVariable(FormulaIdentifier.Create("r"), nat),
             new Formula.BoundVariable(FormulaIdentifier.Create("s"), nat)],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, result));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
}
