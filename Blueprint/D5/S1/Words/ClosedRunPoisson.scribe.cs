using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ClosedRunPoissonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/arratia1990poisson");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound the probability that one closed fair Boolean word avoids k consecutive ones.",
        H("Poisson Error for Closed Fair Words"),
        Blocks(
            Paragraph(Text(
                "The probability law is uniform on all functions from Fin n to Bool, "
                + "equivalently n independent fair bits. It is not conditioned on legality. "
                + "Let G(n,k)=dbonacci(k,n+2), p=G(n,k)/2^n, and "
                + "mu=(n-k+2)/2^(k+1). A forbidden block occupies k contiguous "
                + "coordinates entirely within the word. There are N=n-k+1 possible "
                + "starts. Position zero requires k ones; every later start also requires "
                + "a preceding zero. Thus W counts run beginnings, with probabilities "
                + "2^(-k) at zero and 2^(-k-1) elsewhere, and mean mu.")),
            Describe.Lean(
                DescribeId.Create("closed-word-poisson-bounds"),
                DeclarationHandle.Create(
                    "D5/S1/Words/ClosedRunPoisson.closed_word_poisson_bounds"),
                H("Uniform absolute error and two supplementary probability bounds"),
                StatementSource.FromAuthor(BoundsFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every n at least k at least two, the count ratio is exactly "
                        + "the probability W=0. The three bounds include n=k and k=2. "
                        + "The Poisson claim is an absolute error bound; it asserts no "
                        + "relative error or guaranteed error direction.")),
                    Paragraph(Text(
                        "Each start depends on its k-bit block and optional predecessor. "
                        + "Its support is disjoint from the union of supports of all "
                        + "starts at distance greater than k, giving independence from "
                        + "the entire outside indicator tuple. Distinct nearby starts "
                        + "are mutually exclusive. The first marginal has double weight; "
                        + "counting it separately bounds every neighborhood mass by "
                        + "(k+1)2^(-k).")),
                    Paragraph(Text(
                        "For F(z)=E[z^W], cancellation gives "
                        + "F'(z)=sum_i p_i E[z^V_i], where V_i counts outside starts. "
                        + "On [0,1], the defect F'-mu F lies between zero and the "
                        + "weighted neighborhood charge. Exponential integrating "
                        + "factors bound F(0) relative to exp(-mu), with coefficient "
                        + "(1-exp(-mu))/mu. A second derivative identity bounds "
                        + "E[W(W-1)] by mu^2, so Var(W) is at most mu. The pointwise "
                        + "indicator bound and Chebyshev's inequality give the two "
                        + "supplementary bounds under the same fair-word law. This is a "
                        + "closed-word adaptation of the classical long-run method."))),
                DescribeRole.Theorem))));

    private static Formula BoundsFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var p = Fraction(Call("dbonacci", k, Add(n, D(2))), Sup(D(2), n));
        var mu = Fraction(Add(Subtract(n, k), D(2)), Sup(D(2), Add(k, D(1))));
        var error = AtMost(Seq(Vert, Subtract(p, Call("exp", Seq(Minus, mu))), Vert),
            Multiply(Multiply(Call("min", D(1), mu), Add(k, D(1))),
                Fraction(D(1), Sup(D(2), k))));
        var union = AtMost(Subtract(D(1), p), mu);
        var reciprocal = Implies(Less(D(0), mu), AtMost(p, Fraction(D(1), mu)));
        return Disp(All("n", All("k", Implies(
            And(AtMost(D(2), k), AtMost(k, n)), And(error, And(union, reciprocal))))));
    }

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            Seq(Mathbb, Grp(F.Id("N"))), body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Sup(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
