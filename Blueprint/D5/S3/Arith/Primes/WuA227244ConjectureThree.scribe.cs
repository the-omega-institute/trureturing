using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class WuA227244ConjectureThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/WuA227244ConjectureThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/wu2026a227244c3");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under two independent progression noncoverage hypotheses, 149 is the least prime divisor for every natural index.",
        H("A conditional progression interpretation of Wu's third conjecture for A227244"),
        Blocks(
            Paragraph(Text("All indices and exponents are natural numbers. The outer arithmetic, including the final subtraction, is in the integers. The symbol G denotes the signed integer itself, without a natural subtraction or absolute value.")),
            Paragraph(Text("The symbol G is the public original-owner definition D5.S3.Arith.Primes.WuA227244ConjectureFour.G, used directly throughout the Lean proof. OEIS A227244, NAME: Smallest prime factor of (2^(2^n) + 1)*2^(2^(2^n)) - 1. The exponent of the second outer power is two raised to two raised to m.")),
            Paragraph(Math(Disp(All("m", Equal(Call("G", F.Id("m")), IntegerBody(F.Id("m"))))))),
            Node("reduced", "Finite residues of the nested powers", Disp(ReducedFormula()),
                "This residue expression is in ZMod q. Its five natural parameters are q, d, p, L and r; L records the period used to choose r. The first exponent is reduced modulo d. For the second exponent, a tail of length p precedes reduction modulo p, and the resulting outer exponent is reduced modulo d. Periodicity of powers along 72*n+32 transfers this expression to every natural n.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The exact conditional least-prime assertion", Disp(Event()),
                "The source says: Conjecture 3: a(72*n+32) = 149 for n >= 0 and a(72*n+32) is not covered by Conjectures 1 and 2. We use the disclosed progression-index CONDITIONAL interpretation: for each natural n, absence of a natural k with 72*n+32=20*k+16 and, independently, absence of a natural k with 72*n+32=220*k+8 imply the least-prime conclusion. This quantified formula is our interpretation, not an author-written formula or established author intent. Both k binders range independently over all natural numbers, including zero; n also includes zero and is unbounded. The first hypothesis gives n mod 5 different from 2 and excludes the prime 101; the second gives n mod 55 different from 18 and excludes 47. Periodic modular transfer proves divisibility by 149 and excludes all 34 smaller primes. No extra exclusion, finite prefix or eventual onset is assumed. The proof composes existing periodicity, casts and finite calculations; it claims no new general method", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wu-a227244-conjecture-three"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a227244c3-" + name.ToLowerInvariant()),
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
    private static Formula Noncoverage(Formula index, Formula step, Formula offset) =>
        Seq(Neg, Sp, Parenthesized(new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("k"), Nat,
            Equal(index, Add(Multiply(step, F.Id("k")), offset)))));
    private static Formula Event()
    {
        var n = F.Id("n"); var q = F.Id("q");
        var index = Add(Multiply(D(7,2), n), D(3,2));
        var g = IntegerBody(index);
        var lower = new Formula.Relation(D(1,4,9), FormulaRelationOperator.LessThanOrEqual, q);
        return All("n", Implies(Noncoverage(index, D(2,0), D(1,6)),
            Implies(Noncoverage(index, D(2,2,0), D(8)),
                And(Prime(D(1,4,9)), And(Divides(Cast(D(1,4,9), Ints), g),
                    All("q", Implies(Prime(q), Implies(Divides(Cast(q, Ints), g), lower))))))));
    }
    private static Formula ReducedFormula()
    {
        var q=F.Id("q"); var d=F.Id("d"); var p=F.Id("p"); var l=F.Id("L"); var r=F.Id("r");
        var zmod=Call("ZMod", q);
        var e=Pow(D(2), Add(Multiply(D(7,2), r), D(3,2)));
        var rhs=Subtract(Multiply(Parenthesized(Add(Pow(Cast(D(2), zmod), Mod(e,d)),D(1))),
            Pow(Cast(D(2), zmod),Mod(Pow(D(2),Add(p,Mod(e,p))),d))),D(1));
        return All("q", All("d", All("p", All("L", All("r", Equal(Call("reduced",q,d,p,l,r),rhs))))));
    }
}
