using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class OeisA130095RatioLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/OeisA130095RatioLimit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/adamson2007a130095");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete successive-term ratio limit in OEIS A130095.",
        H("The OEIS A130095 ratio conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a130095-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The odd-Fibonacci divisor transform"),
                StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"),
                    Eq(Call("a", F.Id("n")), SumOver(
                        Call("Nat.divisors", F.Id("n")), "d",
                        Call("Nat.fib", Sub(Mul(D(2), F.Id("d")), D(1)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Peter Bala's formula in OEIS A130095 is a(n) = sum {d | n} "
                    + "Fibonacci(2*d - 1). Nat.fib has F(0)=0 and F(1)=1. For positive "
                    + "n, Nat.divisors contains every positive divisor, including n. "
                    + "The extension a(0)=0 is an empty sum and does not enter the eventual ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a130095-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The complete eventual ratio tends to the squared golden ratio"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The source comment states: “Conjecture: a(n)/a(n-1) tends to phi^2.” "
                        + "Here phi is (1+sqrt(5))/2. Every positive real epsilon has a natural "
                        + "threshold N at least two, and the estimate holds for every natural "
                        + "n at least N. Both sequence values are cast to Real before division. "
                        + "Subtraction in the sequence argument n-1 is natural subtraction. "
                        + "There is no subsequence restriction or additional arithmetic hypothesis.")),
                    Paragraph(Text(
                        "Split a(n) as F(2n-1)+R(n), where R sums the proper divisors. "
                        + "A positive proper divisor d satisfies 2d<=n. The telescoping "
                        + "Fibonacci sum bounds R(n) by F(n). The doubling identity gives "
                        + "F(n)^2<=F(2n-1), so R(n)/F(2n-1)<=1/F(n), which tends to zero. "
                        + "Two instances of Mathlib's adjacent Fibonacci ratio theorem give "
                        + "F(2n-1)/F(2n-3) tending to phi^2. Multiplying by the quotient of "
                        + "the two relative correction factors proves the displayed full limit. "
                        + "The proof establishes a(n)>0 for every n>=1 and discharges every "
                        + "denominator obligation used in the transfer.")),
                    Paragraph(Text(
                        "This delivery uses the external named open-problem-resolution route "
                        + "preregistered in issue 29484. The proof steps are classified bind-only "
                        + "under the repository rule; no separate new general theorem or priority "
                        + "claim is asserted. Independent review and canonical freeze remain separate "
                        + "requirements. The source note records the bounded literature qualification."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a130095-ratio-limit"), ResolutionKind.Proved))
        )));

    private static Formula ResultFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula threshold = F.Id("N");
        Formula n = F.Id("n");
        Formula phi = new Formula.Fraction(Add(D(1), Seq(Sqrt, Grp(D(5)))), D(2));
        Formula ratio = new Formula.Fraction(Cast(Call("a", n)), Cast(Call("a", Sub(n, D(1)))));
        return All("epsilon", F.Id("Real"), Implies(Lt(D(0), epsilon),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("N"), F.Id("Nat"),
                And(Le(D(2), threshold), All("n", F.Id("Nat"), Implies(Le(threshold, n),
                    Lt(new Formula.Absolute(Sub(ratio, new Formula.Power(phi, D(2)))), epsilon)))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        name.Contains('.') ? new Formula.Apply(Q(name.Split('.')[0], name.Split('.')[1]), [.. args])
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula SumOver(Formula set, string name, Formula body) =>
        new Formula.Apply(Q("Finset", "sum"), [set,
            Seq(Open, F.Id("fun"), Sp, F.Id(name), Sp, Mapsto, Sp, body, Close)]);
    private static Formula Cast(Formula x) => Seq(Open, x, Colon, F.Id("Real"), Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
