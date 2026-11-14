using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class BrentEvenMomentPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/BrentEvenMomentPolynomial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/brent2016evenmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even double binomial moments admit ordinary integer coefficient polynomials.",
        H("Integer coefficients of the even double binomial moment"),
        Blocks(
            Paragraph(Text("Brent, Ohtsuka, Osborn and Prodinger, Some Binomial Sums Involving Absolute Values, "
                + "Journal of Integer Sequences 19, Article 16.3.7, section 3.3, page 10 immediately after Theorem 9, "
                + "ask whether the coefficients of 2^(r-4n) W_(2r)(n) are integers. "
                + "The equivalent cleared identity below takes place in Rat. Both indices range over all natural numbers, "
                + "including zero, and every zeroth power is one. Polynomial Int is the ordinary polynomial ring "
                + "with integer monomial coefficients. The polynomial is chosen before n is quantified.")),
            Node("binomial", "The binomial convention", BinomialFormula(),
                "The upper index N is natural and the lower index k is integral. "
                + "Nat.choose is zero when its lower index exceeds N. The displayed value is cast to Rat.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("W", "The original double sum", WFormula(),
                "Both integer intervals include their endpoints. The squared indices and the binomial values "
                + "are interpreted in Rat. In particular the only summand when n=0 uses i=j=0, "
                + "and its weight is one when beta=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The coefficient assertion", Disp(Iff(F.Id("claim"), ClaimBody())),
                "The normalization has been cleared by multiplication by 2^(4*n). "
                + "Evaluation uses the coefficient homomorphism Int.castRingHom Rat and the rational image of n. "
                + "This is an assertion about ordinary integer coefficients, not only integral values at natural arguments.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The integral polynomial exists", Disp(ClaimBody()),
                "For N=2*n, pair two sign sequences. Their exact binomial multiplicities give the original sum. "
                + "The coordinates U=(epsilon+eta)/2 and V=(epsilon-eta)/2 take the four values "
                + "(1,0), (-1,0), (0,1), (0,-1), with equal weight. Their coordinate sums multiply to I^2-J^2. "
                + "Expand the 2*r factors of each color and group their step labels by the equality partition. "
                + "A mixed block or an odd block contributes zero. Each nonempty pure even block contributes 1/2. "
                + "A partition with m blocks has m<=2*r and (2*n).descFactorial(m) injective label assignments. "
                + "Let K_0=1. In K_(m+1), multiply K_m by X-m/2 when m is even, "
                + "and by 2*X-m when m is odd; the first quotient m/2 is a natural number. "
                + "Then 2^ceil(m/2)*K_m(X)=(2*X)_m. The integer polynomial "
                + "H_(r,m)=2^(r-floor(m/2))*K_m therefore satisfies "
                + "2^m*H_(r,m)(n)=2^r*(2*n).descFactorial(m). "
                + "Sum H_(r,m) over the pure even two-color partitions. All coefficients are integers, "
                + "and the finite expansion gives the displayed identity for every n. Empty products and "
                + "empty assignments include r=0 and n=0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brent-ohtsuka-osborn-prodinger-even-moment-integrality"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("brent-even-moment-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula BinomialFormula()
    {
        var n = F.Id("N"); var k = F.Id("k");
        var choose = App(Qualified("Nat", "choose"), n, App(Qualified("Int", "toNat"), k));
        var value = Call("ite", new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, k), choose, D(0));
        return Disp(All("N", Nat(), All("k", Ints(), Equal(Call("binomial", n, k), value))));
    }

    private static Formula WFormula()
    {
        var n = F.Id("n"); var beta = F.Id("beta"); var i = F.Id("i"); var j = F.Id("j");
        var interval = Call("Icc", new Formula.Negate(n), n);
        var weight = Pow(new Formula.Absolute(Sub(Pow(i, D(2)), Pow(j, D(2)))), beta);
        var term = Mul(Mul(Call("binomial", Mul(D(2), n), Add(n, i)),
            Call("binomial", Mul(D(2), n), Add(n, j))), weight);
        return Disp(All("beta", Nat(), All("n", Nat(), Equal(Call("W", beta, n),
            SumOver("i", interval, SumOver("j", interval, term))))));
    }

    private static Formula ClaimBody()
    {
        var r = F.Id("r"); var n = F.Id("n"); var p = F.Id("P");
        var evaluation = App(new Formula.Subscript(Qualified("Polynomial", "eval"), D(2)),
            App(Qualified("Int", "castRingHom"), Rats()), n, p);
        return All("r", Nat(), new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("P"),
            Call("Polynomial", Ints()), All("n", Nat(), Equal(Mul(Pow(D(2), Mul(D(4), n)), evaluation),
                Mul(Pow(D(2), r), Call("W", Mul(D(2), r), n))))));
    }

    private static Formula SumOver(string name, Formula range, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), Sp, InMacro, Sp, range)), Sp, body);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Ints() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Rats() => new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
}
