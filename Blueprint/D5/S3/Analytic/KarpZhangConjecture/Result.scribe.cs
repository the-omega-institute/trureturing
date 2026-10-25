using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangConjecture;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both coefficient assertions of Karp and Zhang's Conjecture 5.2.",
        H("Coefficientwise log-concavity of both series"), Blocks(
            Describe.Lean(DescribeId.Create("karp-zhang-conjecture-five-two-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangConjecture/Result.claim"),
                H("Conjecture 5.2"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Karp and Zhang, Conjecture 5.2, page 12: Suppose that {yₖ}ₖ₌₀∞ is a log-concave sequence. Then the functions μ→ỹ(μ;x) and μ→ŷ(μ;x) are coefficient-wise log-concave on μ>0.")),
                    Paragraph(Text("The real sequence y satisfies KarpZhangReciprocal.Result.IsLogConcave: its terms are nonnegative, it is nontrivial, its adjacent log-concavity inequalities hold, and its support is an interval of integers with the precise zero condition of Definition 1.1. For every positive real mu, nonnegative real alpha and beta, and natural m, claim asserts both 0 at most KarpZhangReciprocal.Result.delta(y,mu,alpha,beta,m) and 0 at most KarpZhangGamma.Series.gammaDelta(y,mu,alpha,beta,m).")),
                    Paragraph(Text("The reciprocal series has coefficient y(k)(2mu) rising factorial k divided by (mu) rising factorial k times k factorial. The gamma series has coefficient y(k)Real.Gamma(mu+k) divided by Real.Gamma(2mu+k) times k factorial. In both cases the Turanian is the product at mu+alpha and mu+beta minus the product at mu and mu+alpha+beta. Finite Cauchy coefficients express the assertion without convergence or growth hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-conjecture-five-two-result"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangConjecture/Result.result"),
                H("Both halves hold for every coefficient"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The theorem proves claim by combining KarpZhangReciprocal.Result.reciprocal_half and KarpZhangGamma.Series.gamma_half with the same sequence, base parameter, shifts and coefficient degree.")),
                    Paragraph(Text("For the reciprocal series, reversible birth-and-death rates bound the score variance of an interval convolution by its expected curvature. Concavity along lines of constant parameter sum and symmetry give the symmetric-tail inequalities. Abel summation combines these tails with the increasing balanced products of a log-concave sequence.")),
                    Paragraph(Text("For the gamma series, exponential smoothing preserves balanced coefficient minors. The paired reciprocal-gamma kernel has nonnegative total and at most one change from negative to positive, so increasing nonnegative smoothed weights give nonnegative coefficients of the two-variable transform. A positive diagonal substitution and the gamma duplication identity transfer these inequalities to the literal gamma-series coefficients. Both shifts may be any nonnegative real numbers, including zero."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-zhang-2023-conjecture-5-2"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimFormula()
    {
        Formula natural = F.Id("Nat");
        Formula real = F.Id("Real");
        Formula y = F.Id("y");
        Formula mu = F.Id("mu");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula m = F.Id("m");
        Formula admissible = new Formula.Apply(
            Qualified("KarpZhangReciprocal", "Result", "IsLogConcave"), [y]);
        Formula reciprocal = new Formula.Apply(
            Qualified("KarpZhangReciprocal", "Result", "delta"), [y, mu, alpha, beta, m]);
        Formula gamma = new Formula.Apply(
            Qualified("KarpZhangGamma", "Series", "gammaDelta"), [y, mu, alpha, beta, m]);
        Formula conclusion = new Formula.Logic(
            new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, reciprocal),
            FormulaLogicOperator.And,
            new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, gamma));
        Formula assertion = All("y", new Formula.TypeArrow(natural, real),
            Implies(admissible,
                All("mu", real, All("alpha", real, All("beta", real,
                    Implies(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, mu),
                        Implies(new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, alpha),
                            Implies(new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, beta),
                                All("m", natural, conclusion)))))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Qualified(string group, string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(group)), Dot, Operatorname, Grp(F.Id(owner)),
            Dot, Operatorname, Grp(F.Id(name)));
}
