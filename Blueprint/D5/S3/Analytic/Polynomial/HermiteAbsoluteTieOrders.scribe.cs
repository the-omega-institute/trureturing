using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteAbsoluteTieOrdersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/sheppard2025a381737");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact increasing enumeration of physicists Hermite orders with exactly two largest absolute coefficients.",
        H("Orders with two maximal absolute Hermite coefficients"),
        Blocks(
            Paragraph(Text("The order k and every exponent are natural numbers, including zero. The polynomial is exactly "
                + "HermiteSignedMode.physicistsHermite over the rationals. Maximality compares absolute values over the entire coefficient "
                + "row from zero through k, including the zero coefficients of the other parity. The index n of the enumeration starts at one. "
                + "Its formula uses integer arithmetic, so the alternating summand is an ordinary signed integer.")),
            Node("IsAbsMax", "Maximality in the complete original row", MaxFormula(),
                "An exponent j is at most k and its absolute coefficient bounds the absolute coefficient at every exponent i at most k.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("HasExactlyTwo", "Exactly two distinct maxima", TwoFormula(),
                "There are exponents u less than v such that the maximizing exponents are precisely u and v. "
                + "The equivalence for every natural j excludes both additional maxima and exponents outside the row.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("a", "The one-based source formula", AFormula(),
                "This is Conjecture 1 of OEIS A381737 revision 28. The natural index is cast to the integers before the additions and products. "
                + "The exponent n+1 remains natural. The theorem uses only positive indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete increasing exhaustive enumeration", Equal(F.Id("claim"), Par(ClaimBody())),
                "Every positive-index value is positive; the values strictly increase with the index; and for every natural order k, "
                + "exactly two maxima occur if and only if k equals the formula at one unique positive index. "
                + "The displayed unique-index condition expands existence and uniqueness explicitly.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Exact classification and enumeration", ClaimBody(),
                "Let w(k,r) be the original absolute signedCoeff at exponent k-2r, with 2r at most k. "
                + "HermiteAbsoluteMode supplies positivity, the adjacent identity, maximality at mode(k), and strict decrease after that mode. "
                + "Before the final adjacent pair, the threshold is strict: if r+1 is less than mode(k), then "
                + "4(r+1) is less than second(k-2(r+1)), where second(j)=(j+1)(j+2). The adjacent identity therefore gives "
                + "w(k,r) less than w(k,r+1). A maximizing index must be mode(k) or mode(k)-1. "
                + "Those two indices tie exactly when second(k-2r)=4r at r=mode(k), with r at least one. "
                + "Conversely, any such equality forces r to be mode(k) and gives precisely those two maxima. "
                + "The coefficient_cases and polynomial_coeff statements transfer the comparison to every exponent in the original polynomial row; "
                + "zero parity coefficients cannot maximize because the mode weight is positive.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a381737-hermite-absolute-ties"), ResolutionKind.Proved)),
            Paragraph(Text("Put j=k-2r. The tie equation is (j+1)(j+2)=4r. Its reduction modulo four forces j to be 4t+2 or 4t+3. "
                + "In the first case k=8t squared+18t+8=a(2t+1); in the second, k=8t squared+22t+13=a(2t+2). "
                + "Conversely, these formulas provide r=(4t+3)(t+1) and r=(4t+5)(t+1), respectively, satisfying the tie equation and 2r at most k. "
                + "Every positive index is uniquely odd or even in these forms. The alternating power is either one or minus one; "
                + "substitution shows that a(n+1)-a(n) is 2n+3 or 6n+9, both positive. Thus the enumeration is strictly increasing, "
                + "and a(1)=8 makes every positive-index value positive. Strict increase gives the unique positive index for each qualifying order. "
                + "No finite cutoff, rescaling of the coefficient row, or restriction to a subsequence is used.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hermite-absolute-tie-orders-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LessEqual(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Equiv(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, F.Id(n), Colon, t, Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, F.Id(n), Colon, t, Comma, Sp, b);
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Ints()));
    private static Formula A(Formula n) => Call("a", n);
    private static Formula AbsCoeff(Formula k, Formula j) => Call("abs", Call("coeff", Call("physicistsHermite", k), j));
    private static Formula MaxFormula()
    {
        var k=F.Id("k"); var j=F.Id("j"); var i=F.Id("i");
        return All("k", Nat(), All("j", Nat(), Equal(Call("IsAbsMax", k, j), Par(And(LessEqual(j,k),
            All("i",Nat(),Arrow(LessEqual(i,k),LessEqual(AbsCoeff(k,i),AbsCoeff(k,j)))))))));
    }
    private static Formula TwoFormula()
    {
        var k=F.Id("k"); var u=F.Id("u"); var v=F.Id("v"); var j=F.Id("j");
        return All("k",Nat(),Equal(Call("HasExactlyTwo",k),Par(Some("u",Nat(),Some("v",Nat(),And(Less(u,v),
            All("j",Nat(),Equiv(Call("IsAbsMax",k,j),Or(Equal(j,u),Equal(j,v))))))))));
    }
    private static Formula AFormula()
    {
        var n=F.Id("n"); var z=Cast(n);
        return All("n",Nat(),Equal(A(n),Add(Mul(Mul(D(2),z),Par(Add(z,D(2)))),
            Mul(Par(Add(z,D(1))),new Formula.Power(Par(Seq(Minus,D(1))),Add(n,D(1)))))));
    }
    private static Formula Index(Formula k, Formula n) => And(LessEqual(D(1),n),Equal(Cast(k),A(n)));
    private static Formula ClaimBody()
    {
        var n=F.Id("n"); var m=F.Id("m"); var k=F.Id("k");
        var positive=All("n",Nat(),Arrow(LessEqual(D(1),n),Less(D(0),A(n))));
        var increasing=All("n",Nat(),All("m",Nat(),Arrow(LessEqual(D(1),n),Arrow(Less(n,m),Less(A(n),A(m))))));
        var unique=Some("n",Nat(),And(Index(k,n),All("m",Nat(),Arrow(Index(k,m),Equal(m,n)))));
        return And(positive,And(increasing,All("k",Nat(),Equiv(Call("HasExactlyTwo",k),unique))));
    }
}
