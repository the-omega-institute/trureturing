using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteSignedModeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteSignedMode.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/sheppard2025a381423");
    private static readonly LibraryNoteRef Dlmf = LibraryNoteRef.Create("D5/L/Analytic/dlmf2010hermitecoefficients");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest exponent with maximum signed physicists Hermite coefficient changes by one or minus three.",
        H("Signed coefficient modes of physicists Hermite polynomials"),
        Blocks(
            Paragraph(Text("All indices are natural numbers, including zero. Polynomial coefficients are represented exactly in the rationals. "
                + "The comparison uses signed coefficients. Subtraction in the conclusion occurs in the integers after both exponents are cast. "
                + "The function coeff(H,j) extracts the coefficient of X to the power j. Natural subtraction truncates at zero; "
                + "all mode indices below satisfy four times the index at most n.")),
            Node("signedCoeff", "Exact signed coefficient", CoefficientFormula(),
                "For j at most n with n-j even, this is (-1) to the power (n-j)/2 times n! times 2 to the power j, "
                + "divided by ((n-j)/2)! j!. Otherwise it is zero. div and mod are natural division and remainder. "
                + "Factorials and powers in the quotient are cast to the rationals. This is the coefficient formula from DLMF 18.5.13, reindexed by exponent.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("physicistsHermite", "The physicists polynomial", PolynomialFormula(),
                "The sum runs over every k from zero through floor(n/2). monomial(j,c) denotes c times X to the power j. "
                + "This is exactly DLMF 18.5.13 with n! distributed into the sum and (2X) to the power n-2k expanded. "
                + "It defines the physicists normalization directly; it does not rescale a probabilists argmax. "
                + "The coefficient extraction proof shows that every coefficient in the source range equals signedCoeff(n,j).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Dlmf)),
            Node("polynomial_coeff", "Exact coefficient extraction", ExtractionFormula(),
                "For every natural n and j with j at most n, the coefficient of X to the power j in the original physicists polynomial "
                + "equals signedCoeff(n,j). This includes zero coefficients outside the parity support. "
                + "The absolute-mode selector consumes this same extraction theorem; its statement and proof also serve the signed selector.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Dlmf)),
            Node("a", "A certified smallest maximizing exponent", AFormula(),
                "mode(n) is the largest r satisfying 4r at most n and 16(2r)(2r-1) at most "
                + "(n-4r+1)(n-4r+2)(n-4r+3)(n-4r+4). The finite set contains zero. "
                + "The theorem certifies that n-4mode(n) is exactly the smallest exponent maximizing the signed coefficient, "
                + "so this constructive selector agrees with the source's upward scan and first maximum. No uniqueness hypothesis is used.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("IsSmallestMax", "Signed maximum with the first-index tie rule", SmallestFormula(),
                "The predicate requires membership in zero through n, maximality against every coefficient in that range, "
                + "and that every tied maximizer has exponent at least j. The last condition handles all possible ties.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The independent OEIS difference assertion", Equal(F.Id("claim"), Par(ClaimBody())),
                "OEIS A381423 revision 8 states: \"Differences are either 1 or -3\" as the first independent clause of its conjecture. "
                + "The selector certificate is included explicitly, followed by the difference assertion for every natural n. "
                + "Fine difference patterns, linearly or quadratically spaced positions, square-root growth and the separate uniqueness assertion remain outside this claim.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal signed-mode transition", ClaimBody(),
                "Write the positive coefficient at exponent n-4r as n! times w(n,r), where "
                + "w(n,r)=2 to the power n-4r divided by (2r)! (n-4r)!. All coefficients outside this positive residue class are nonpositive. "
                + "Successive positive weights obey w(n,r+1) times 16(2r+2)(2r+1) = w(n,r) times "
                + "(n-4r)(n-4r-1)(n-4r-2)(n-4r-3). Thus the threshold predicate says precisely that the weight has not decreased from the previous index. "
                + "Its true indices form an initial segment. Induction proves maximality at the largest true index and strict decrease past it; "
                + "choosing that largest index gives the smallest exponent among ties. Increasing n preserves every true threshold; "
                + "a true threshold at index r+1 for n+1 implies a true threshold at index r for n. Consequently mode(n+1) is mode(n) or mode(n)+1. "
                + "The corresponding exponent difference is 1 or -3, with both exponents cast before subtraction. "
                + "All factorial denominators are positive, and the proof covers the boundary indices without a cutoff. "
                + "This is a repository derivation of the separate source assertion, with no global priority claim. "
                + "The source-family audit observes the entire natural sequence, reconstructs this claim, rejects the constant-zero family, "
                + "and proves actual dependence between indices zero and one. Its continuation is unknown.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a381423-hermite-differences"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hermite-signed-mode-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LessEqual(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, F.Id(n), Colon, t, Comma, Sp, b);
    private static Formula A(Formula n) => Call("a", n);
    private static Formula Coeff(Formula n, Formula j) => Call("coeff", Call("physicistsHermite", n), j);
    private static Formula CoefficientFormula()
    {
        var n = F.Id("n"); var j = F.Id("j");
        var k = Call("div", Par(Sub(n,j)), D(2));
        var value = new Formula.Fraction(Mul(Mul(new Formula.Power(Par(Seq(Minus,D(1))),k), Call("factorial",n)),
            new Formula.Power(D(2),j)), Mul(Call("factorial",k), Call("factorial",j)));
        return All("n",Nat(),All("j",Nat(),Equal(Call("signedCoeff",n,j),
            Call("ite",And(LessEqual(j,n),Equal(Call("mod",Par(Sub(n,j)),D(2)),D(0))),value,D(0)))));
    }
    private static Formula PolynomialFormula()
    {
        var n=F.Id("n"); var k=F.Id("k"); var j=Par(Sub(n,Mul(D(2),k)));
        var value=new Formula.Fraction(Mul(Mul(new Formula.Power(Par(Seq(Minus,D(1))),k),Call("factorial",n)),
            new Formula.Power(D(2),j)),Mul(Call("factorial",k),Call("factorial",j)));
        var sum=Seq(Sum,Underscore,Grp(Seq(k,InMacro,Call("range",Add(Call("div",n,D(2)),D(1))))),Call("monomial",j,value));
        return All("n",Nat(),Equal(Call("physicistsHermite",n),sum));
    }
    private static Formula AFormula() => All("n",Nat(),Equal(A(F.Id("n")),
        Sub(F.Id("n"),Mul(D(4),Call("mode",F.Id("n"))))));
    private static Formula ExtractionFormula()
    {
        var n=F.Id("n"); var j=F.Id("j");
        return All("n",Nat(),All("j",Nat(),Arrow(LessEqual(j,n),
            Equal(Coeff(n,j),Call("signedCoeff",n,j)))));
    }
    private static Formula SmallestBody(Formula n, Formula j)
    {
        var k=F.Id("k");
        return And(LessEqual(j,n),And(All("k",Nat(),Arrow(LessEqual(k,n),LessEqual(Coeff(n,k),Coeff(n,j)))),
            All("k",Nat(),Arrow(LessEqual(k,n),Arrow(Equal(Coeff(n,k),Coeff(n,j)),LessEqual(j,k))))));
    }
    private static Formula SmallestFormula() => All("n",Nat(),All("j",Nat(),
        Equal(Call("IsSmallestMax",F.Id("n"),F.Id("j")),Par(SmallestBody(F.Id("n"),F.Id("j"))))));
    private static Formula ClaimBody()
    {
        var n=F.Id("n");
        Formula Cast(Formula x) => Par(Seq(x,Colon,Ints()));
        var diff=Sub(Cast(A(Add(n,D(1)))),Cast(A(n)));
        return And(All("n",Nat(),Call("IsSmallestMax",n,A(n))),
            All("n",Nat(),Or(Equal(diff,D(1)),Equal(diff,Seq(Minus,D(3))))));
    }
}
