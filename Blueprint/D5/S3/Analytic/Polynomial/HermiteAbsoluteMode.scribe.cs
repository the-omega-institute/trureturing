using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteAbsoluteModeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteAbsoluteMode.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/sheppard2025a381524");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smallest exponent of a largest absolute physicists Hermite coefficient changes by one or minus one.",
        H("Absolute coefficient modes of physicists Hermite polynomials"),
        Blocks(
            Paragraph(Text("All orders and exponents are natural numbers, including zero. The polynomial physicistsHermite and its exact "
                + "signedCoeff supplier are the original HermiteSignedMode declarations. Coefficients are rational, and absolute value is taken "
                + "before comparing them. No rescaling or restriction to positive coefficients is made. Both exponents are cast to the integers "
                + "before the subtraction in the transition statement.")),
            Paragraph(Text("The comparison functions are second(j)=(j+1)(j+2), "
                + "rises(n,r) meaning 2r at most n and 4r at most second(n-2r), and mode(n), the largest rising index. "
                + "mode_rises asserts the threshold at mode(n), le_mode bounds every rising index by mode(n), and second_mono "
                + "states monotonicity of second. The weight is the absolute original signedCoeff at n-2r. "
                + "weight_pos asserts positivity on 2r at most n, and adjacent gives its successive cross-product identity. "
                + "weight_le_mode bounds every supported weight by the mode weight; weight_lt_mode makes this bound strict "
                + "beyond the mode. coefficient_cases says that each original absolute signed coefficient is zero or is a supported weight.")),
            Node("b", "The smallest absolute-coefficient mode", BFormula(),
                "Let rises(n,r) mean 2r at most n and 4r at most (n-2r+1)(n-2r+2). "
                + "mode(n) is the largest r in range(n+1) satisfying rises(n,r); zero always belongs. "
                + "The selector is n-2mode(n). Equality in the threshold is included, so a tied maximum chooses the larger r "
                + "and therefore the smaller exponent. The selector theorem verifies this construction against the original polynomial.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("IsSmallestAbsMax", "Full absolute maximum with the first-index tie rule", SmallestFormula(),
                "The predicate requires j at most n, maximal absolute coefficient against every exponent from zero through n, "
                + "and j at most every other exponent with equal absolute coefficient. Thus parity zeros and all ties remain in scope.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The complete OEIS adjacent-difference assertion", Equal(F.Id("claim"), Par(ClaimBody())),
                "OEIS A381524 revision 18 defines the smallest exponent of a maximal coefficient ignoring signs and conjectures: "
                + "Differences are either +1 or -1. This claim includes the exact selector certificate for all natural orders, "
                + "followed by that entire adjacent-difference assertion. It assumes neither uniqueness nor an asymptotic cutoff.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal absolute-mode transition", ClaimBody(),
                "Write w(n,r) for the absolute value of the original signedCoeff at exponent n-2r. The original polynomial_coeff theorem "
                + "connects these values to the polynomial. On 2r at most n they are positive; all other parity coefficients are zero. "
                + "For 2(r+1) at most n, successive weights satisfy "
                + "w(n,r+1) times 4(r+1) = w(n,r) times (n-2r-1)(n-2r). "
                + "Consequently rises(n,r+1) is exactly the nondecrease test. The true thresholds form an initial segment. "
                + "Induction proves maximality at its last index and strict decrease beyond it, which supplies the smallest-exponent tie rule. "
                + "Every true threshold persists when n increases by one; a true threshold at (n+1,r+1) implies a true threshold at (n,r). "
                + "Hence mode(n+1) is mode(n) or mode(n)+1, and the exponent changes by +1 or -1. The argument includes order zero. "
                + "It applies to the complete natural selector sequence, preserving parity zeros, all ties, and the stated first-index convention. "
                + "The result is derived from the displayed coefficient identities and makes no uniqueness or asymptotic assumption.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a381524-hermite-absolute-differences"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hermite-absolute-mode-" + name.ToLowerInvariant()),
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
    private static Formula B(Formula n) => Call("b", n);
    private static Formula Coeff(Formula n, Formula j) => Call("coeff", Call("physicistsHermite", n), j);
    private static Formula AbsCoeff(Formula n, Formula j) => Call("abs", Coeff(n,j));
    private static Formula BFormula() => All("n",Nat(),Equal(B(F.Id("n")),
        Sub(F.Id("n"),Mul(D(2),Call("mode",F.Id("n"))))));
    private static Formula SmallestBody(Formula n, Formula j)
    {
        var k=F.Id("k");
        return And(LessEqual(j,n),And(All("k",Nat(),Arrow(LessEqual(k,n),LessEqual(AbsCoeff(n,k),AbsCoeff(n,j)))),
            All("k",Nat(),Arrow(LessEqual(k,n),Arrow(Equal(AbsCoeff(n,k),AbsCoeff(n,j)),LessEqual(j,k))))));
    }
    private static Formula SmallestFormula() => All("n",Nat(),All("j",Nat(),
        Equal(Call("IsSmallestAbsMax",F.Id("n"),F.Id("j")),Par(SmallestBody(F.Id("n"),F.Id("j"))))));
    private static Formula ClaimBody()
    {
        var n=F.Id("n");
        Formula Cast(Formula x) => Par(Seq(x,Colon,Ints()));
        var diff=Sub(Cast(B(Add(n,D(1)))),Cast(B(n)));
        return And(All("n",Nat(),Call("IsSmallestAbsMax",n,B(n))),
            All("n",Nat(),Or(Equal(diff,D(1)),Equal(diff,Seq(Minus,D(1))))));
    }
}
