using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Lagarias;

internal sealed class ThresholdPerturbationDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Arith/Robin/Lagarias/ThresholdPerturbation.";
    private static readonly LibraryNoteRef AsymptoticSource =
        LibraryNoteRef.Create("D5/L/Analytic/lucapomerancesole2025robin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Lagarias threshold has an exact leading perturbation and preserves the sharp Robin margin.",
        H("Harmonic and Robin thresholds"),
        Blocks(
            Paragraph(Text("Let H(n) be the ordinary harmonic number, gamma the Euler-Mascheroni constant, "
                + "and E=exp(gamma). All sequences have natural arguments and real values. "
                + "Write K=2*sqrt(2)-2-firstLiMass, with the normalization in "
                + "RHSharpOriginalRecordMargin.K: firstLiMass is twice the conventional first Li coefficient.")),
            Describe.Lean(DescribeId.Create("lagarias-harmonic-threshold"),
                DeclarationHandle.Create(Root + "threshold"), H("The harmonic threshold"),
                StatementSource.FromAuthor(Disp(All("n", Nat, Eqn(C("L", Id("n")),
                    Add(C("H", Id("n")), Multiply(C("exp", C("H", Id("n"))),
                        C("log", C("H", Id("n"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L(n)=H(n)+exp(H(n))*log(H(n)). The definition uses the total real logarithm."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lagarias-robin-threshold-gap"),
                DeclarationHandle.Create(Root + "gap"), H("The difference per integer"),
                StatementSource.FromAuthor(Disp(All("n", Nat, Eqn(C("delta", Id("n")),
                    Sub(Q(C("L", Id("n")), Id("n")),
                        Multiply(Id("E"), C("log", C("log", Id("n"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("delta(n)=L(n)/n-E*log(log(n)); all divisions are total real divisions, including at n=0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lagarias-normalized-margin"),
                DeclarationHandle.Create(Root + "margin"), H("The normalized divisor-sum margin"),
                StatementSource.FromAuthor(Disp(All("n", Nat, Eqn(C("M", Id("n")),
                    Multiply(Sub(Q(C("L", Id("n")), Id("n")),
                        Q(C("sigma", Id("n")), Id("n"))), C("sqrt", C("log", Id("n")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("sigma(n)=ArithmeticFunction.sigma 1 n. Thus M(n)=(L(n)-sigma(n))*sqrt(log(n))/n "
                    + "for n>0. The Robin sequence T is RHSharpAllIntegerMargin.T."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lagarias-threshold-leading-coefficient"),
                DeclarationHandle.Create(Root + "threshold_asymptotic"), H("The exact perturbation coefficient"),
                StatementSource.FromAuthor(Disp(Seq(Lim, Underscore, Grp(Id("n"), To, Infty), Sp,
                    Multiply(C("log", Id("n")), C("delta", Id("n"))), Sp, Eq, Sp,
                    Multiply(Id("E"), Id("gamma"))))),
                AssessedProvenance.FromLiterature(AsymptoticSource),
                Blocks(Paragraph(Text("This limit is unconditional. For n>=3, put x=log(n), a=H(n)-x and b=exp(H(n))/n-E. "
                    + "The two Euler sequences imply E*n<exp(H(n))<E*(n+1), so 0<b<E/n. For x>1, "
                    + "H(n)<=x+1 and 0<=log(H(n))<=x+1. The bounds 1-u^(-1)<=log(u)<=u-1, "
                    + "applied to u=H(n)/x, give "
                    + "E*a/(1+a/x)<=x*delta(n)<=E*a+(1+E)*(x^2+x)/n. "
                    + "Both endpoints tend to E*gamma because a tends to gamma and every fixed power of log(n) is o(n)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sharp-lagarias-margin"),
                DeclarationHandle.Create(Root + "sharp_lagarias_margin"), H("The sharp endpoint and original records"),
                StatementSource.FromAuthor(SharpClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume RH. Every sufficiently large integer has M(n)>E*K-epsilon, "
                    + "for each epsilon>0. For every epsilon>0 and every natural N, there exist m>=N, "
                    + "m>=2, and a real lambda>0 such that every positive predecessor k<m has strictly "
                    + "smaller original goldenResourceObjective(lambda,k), and abs(M(m)-E*K)<epsilon. "
                    + "The real liminf of M on natural atTop is E*K.")),
                    Paragraph(Text("For n>1, the difference is M(n)-T(n)=(log(n)*delta(n))/sqrt(log(n)); "
                    + "the perturbation theorem makes this difference tend to zero. "
                    + "Apply the existing all_integer_sharp_margin theorem with epsilon/2, choosing the "
                    + "perturbation cutoff before its arbitrarily late record witness. The same witness works "
                    + "by the triangle inequality. An eventual lower bound and arbitrarily late upper witnesses "
                    + "provide the boundedness and coboundedness required for the real liminf.")),
                    Paragraph(Text("The threshold comparison is classical: Jeffrey C. Lagarias, "
                    + "An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177, "
                    + "Lemmas 3.1-3.2. The leading coefficient also appears in Luca, Pomerance and Sole, "
                    + "Correction to: On Robin's inequality, Integers 25 (2025), A8 Corrigendum, Section 3. "
                    + "The harmonic asymptotic transfers the existing sharp Robin endpoint to the Lagarias margin. "
                    + "This result asserts no independent proof of RH and no finite cutoff at 5040."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula C(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a, b);
    private static Formula Q(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula SharpClaim()
    {
        var eps = Id("epsilon"); var n = Id("n"); var N = Id("N");
        var m = Id("m"); var k = Id("k"); var lam = Id("lambda");
        var endpoint = Multiply(Id("E"), Id("K"));
        var lower = All("epsilon", Real, Imp(Lt(D(0), eps), Ex("N", Nat,
            All("n", Nat, Imp(Le(N, n), Lt(Sub(endpoint, eps), C("M", n)))))));
        var record = All("k", Nat, Imp(And(Lt(D(0), k), Lt(k, m)),
            Lt(C("goldenResourceObjective", lam, k), C("goldenResourceObjective", lam, m))));
        var attainment = All("epsilon", Real, Imp(Lt(D(0), eps), All("N", Nat,
            Ex("m", Nat, Ex("lambda", Real, And(Le(N, m), And(Lt(D(0), lam),
                And(Le(D(2), m), And(record, Lt(C("abs", Sub(C("M", m), endpoint)), eps))))))))));
        return Disp(Imp(Id("RiemannHypothesis"), And(lower, And(attainment,
            Eqn(Seq(Operatorname, Grp(Id("liminf")), Underscore,
                Grp(n, InMacro, Sp, Nat, Comma, Sp, n, To, Sp, Infty), Sp, C("M", n)), endpoint)))));
    }
}
