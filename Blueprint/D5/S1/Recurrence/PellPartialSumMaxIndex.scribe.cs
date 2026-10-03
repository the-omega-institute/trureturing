using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PellPartialSumMaxIndexDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/byrapuram2024pellpartialsums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pell partial sums have greatest dividing indices in four residue classes.",
        H("Greatest Pell indices dividing initial partial sums"),
        Blocks(
            Paragraph(Text("The Pell sequence has P(0)=0, P(1)=1 and "
                + "P(n+2)=2P(n+1)+P(n). Its companion has Q(0)=Q(1)=1 and "
                + "Q(n+2)=2Q(n+1)+Q(n). Write S(n)=P(1)+...+P(n). "
                + "The formal sum ranges from zero through n; P(0)=0 makes "
                + "this the same sum. Let G(n,m) mean that m is the greatest "
                + "positive index j for which P(j) divides S(n). Thus G(n,m) "
                + "includes m>=1 and P(m)|S(n), and asserts j<=m for every "
                + "j>=1 satisfying P(j)|S(n).")),
            Describe.Lean(
                DescribeId.Create("pell-partial-sum-max-index-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/PellPartialSumMaxIndex.result"),
                H("Four greatest-index classes"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The addition formulas yield "
                    + "P(2r)=2P(r)Q(r) and Q(2r)=Q(r)^2+2P(r)^2. "
                    + "Together with Q(r)^2-2P(r)^2=(-1)^r, they give "
                    + "S(4k+1)=Q(2k+1)^2 and S(4k+2)=Q(2k+1)Q(2k+2), "
                    + "and, for k>=1, S(4k-1)=2P(2k)^2 and "
                    + "S(4k)=2P(2k)P(2k+1). "
                    + "Strong divisibility gives gcd(P(a),P(b))=P(gcd(a,b)). "
                    + "For odd m, P(m) is coprime to every Q(j); consequently "
                    + "the first two odd sums admit only the index one. "
                    + "For the other sums, a dividing P(m) also divides "
                    + "2 gcd(P(m),P(r)) gcd(P(m),P(s)). Proper divisor "
                    + "indices and strict growth place this positive product "
                    + "below P(m) whenever m exceeds the claimed maximum. "
                    + "In the equal-index case, Q(d)>P(d) for d>=2 handles "
                    + "the possible equality 2d=m. In the consecutive case, "
                    + "gcd(m,r) and gcd(m,r+1) are coprime, so their sum is "
                    + "strictly below m. Both latter classes exclude k=0."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("byrapuram-pell-partial-sum-max-index"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k");
        Formula fourK = Multiply(D(4), k), twoK = Multiply(D(2), k);
        return Disp(And(
            All("k", Call("G", Add(fourK, D(1)), D(1))),
            All("k", Call("G", Add(fourK, D(2)), D(1))),
            All("k", Implies(Le(D(1), k), Call("G", Subtract(fourK, D(1)), twoK))),
            All("k", Implies(Le(D(1), k), Call("G", fourK, Add(twoK, D(1)))))));
    }

    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parens(a), FormulaLogicOperator.Implies, Parens(b));
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parens(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(Parens(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }
}
