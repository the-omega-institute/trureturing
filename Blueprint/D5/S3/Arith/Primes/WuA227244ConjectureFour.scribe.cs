using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class WuA227244ConjectureFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/WuA227244ConjectureFour.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/wu2026a227244c4");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fifty-nine is the least prime divisor throughout the specified progression outside one residue class.",
        H("Wu's fourth conjecture for A227244"),
        Blocks(
            Paragraph(Text("All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.")),
            Node("G", "The nested exponential integer", Disp(All("m", Equal(Call("G", F.Id("m")), IntegerBody(F.Id("m"))))),
                "OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The least-prime assertion", Disp(Equal(F.Id("claim"), Parenthesized(Event()))),
                "OEIS A227244, FORMULA, Chai Wah Wu: Conjecture 4: a(168*n+43) = 59 if n>=0 and n mod 55 <> 26. Least prime divisor means primality of 59, divisibility by 59, and a lower bound on every natural prime divisor of that same signed integer. The assertion includes n=0 and has no upper bound. It makes no assertion at residue 26 and does not assert that the exclusion is necessary.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reduced", "Finite residues of the nested powers", Disp(ReducedFormula()),
                "This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 168*n+43 transfers this expression to every natural n.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The fourth conjecture holds", Disp(Event()),
                "Powers along an arithmetic progression repeat once a period equation holds. After the initial tail, the inner modular powers repeat as well. These two facts reduce divisibility by 59 and nondivisibility by each smaller prime to finite residue calculations. For the prime 47 the period in n is 55 and the calculation uses the stated exclusion of residue 26. Divisibility by 59 and exclusion of every smaller prime give the least-prime assertion for the entire unbounded family.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wu-a227244-conjecture-four"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a227244c4-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula All(string x, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), Nat, body);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mod(Formula x, Formula y) => Call("mod", x, y);
    private static Formula Cast(Formula x, Formula ty) => Parenthesized(Seq(x, Colon, Sp, ty));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Prime(Formula x) => Call("Prime", x);
    private static Formula Divides(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula IntegerBody(Formula m) => Subtract(Multiply(
        Parenthesized(Add(Pow(Cast(D(2), Ints), Pow(D(2), m)), D(1))),
        Pow(Cast(D(2), Ints), Pow(D(2), Pow(D(2), m)))), D(1));
    private static Formula Event()
    {
        var n = F.Id("n"); var q = F.Id("q");
        var g = IntegerBody(Add(Multiply(D(1,6,8), n), D(4,3)));
        var exclusion = Seq(Mod(n, D(5,5)), Sp, Neq, Sp, D(2,6));
        var lower = new Formula.Relation(D(5,9), FormulaRelationOperator.LessThanOrEqual, q);
        return All("n", Implies(exclusion, And(Prime(D(5,9)), And(
            Divides(Cast(D(5,9), Ints), g),
            All("q", Implies(Prime(q), Implies(Divides(Cast(q, Ints), g), lower)))))));
    }
    private static Formula ReducedFormula()
    {
        var q=F.Id("q"); var d=F.Id("d"); var p=F.Id("p"); var l=F.Id("L"); var r=F.Id("r");
        var zmod=Call("ZMod", q);
        var e=Pow(D(2), Add(Multiply(D(1,6,8), r), D(4,3)));
        var rhs=Subtract(Multiply(Parenthesized(Add(Pow(Cast(D(2), zmod), Mod(e,d)),D(1))),
            Pow(Cast(D(2), zmod),Mod(Pow(D(2),Add(p,Mod(e,p))),d))),D(1));
        return All("q", All("d", All("p", All("L", All("r", Equal(Call("reduced",q,d,p,l,r),rhs))))));
    }
}
