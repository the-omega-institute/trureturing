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
        "The Lagarias threshold has an exact leading perturbation of the Robin threshold.",
        H("Harmonic and Robin thresholds"),
        Blocks(
            Paragraph(Text("Let H(n) be the ordinary harmonic number, gamma the Euler-Mascheroni constant, "
                + "and E=exp(gamma). All sequences have natural arguments and real values.")),
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
                    Subtract(Q(C("L", Id("n")), Id("n")),
                        Multiply(Id("E"), C("log", C("log", Id("n"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("delta(n)=L(n)/n-E*log(log(n)); all divisions are total real divisions, including at n=0."))),
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
                    + "Both endpoints tend to E*gamma because a tends to gamma and every fixed power of log(n) is o(n).")),
                    Paragraph(Text("The cited corrigendum, Section 3, page 4, states the same leading coefficient for "
                    + "exp(H(n))*log(H(n)); the additional harmonic term is negligible at this scale. "
                    + "For n>1, sqrt(log(n))*delta(n)=(log(n)*delta(n))/sqrt(log(n)). "
                    + "The numerator has a finite limit and the denominator tends to infinity, so the perturbation "
                    + "vanishes at the sharp Robin margin scale. This result asserts no independent proof of RH "
                    + "and no finite cutoff at 5040."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula C(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Q(Formula a, Formula b) => new Formula.Fraction(a, b);
}
