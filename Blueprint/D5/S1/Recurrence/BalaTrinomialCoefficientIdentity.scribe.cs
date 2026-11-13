using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BalaTrinomialCoefficientIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/bala2022a351858");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational formal coefficient and an inclusive finite sum of ordinary binomial coefficients.",
        H("Bala's finite-binomial coefficient identity"),
        Blocks(
            Node("source", "The independent formal quotient", SourceFormula(),
                [
                    "For every natural n, source(n) is the product of (1+X+X^2) to exponent 3n and the formal multiplicative inverse of (1+X) to exponent 2n in Q[[X]]. The denominator has constant coefficient one, so it is a unit. This defines the quotient independently of the finite sum. These are formal series at zero; no analytic convergence assumption is used.",
                    "The NAME field of OEIS A351858 reads: \"a(n) = [x^n] (1 + x + x^2)^(3*n)/(1 + x)^(2*n).\""
                ], DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The coefficient identity at every natural index", ResultFormula(),
                [
                    "All indices are natural, including zero and one. The displayed choose denotes Nat.choose, the ordinary natural binomial coefficient; subtraction n-k is natural subtraction. The displayed div denotes Nat.div, so div(n,2) is floor(n/2). The displayed range denotes Finset.range; range(floor(n/2)+1) includes both endpoints 0 and floor(n/2). The notation natCastQ casts the entire natural sum to Q. The left side extracts the degree-n coefficient of source(n) at zero. There is no primality, positivity, eventual-index, congruence, or truncated-series premise.",
                    "Peter Bala's FORMULA entry reads: \"Conjecture: a(n) = Sum_{k = 0..floor(n/2)} C(3*n,k)*C(n-k,k).\"",
                    "For positive n, formal substitution X=T/(1-T), followed by multiplication by (1-T)^(n-1), preserves the degree-n coefficient. The proof checks this using finite coefficient substitution and the coefficients of powers of the geometric series. Under this weighted substitution the source becomes (1+T^2/(1-T))^(3n)/(1-T).",
                    "The binomial expansion has terms binom(3n,k) T^(2k)/(1-T)^(k+1). The degree-n coefficient of each term is binom(3n,k) binom(n-k,k) when 2k is at most n, and zero otherwise. Thus only the inclusive range through floor(n/2) contributes. The proof treats n=0 separately, where both sides equal one; n=1 is included in the positive case. The final cast identifies the rational sum with the cast of the natural sum.",
                    "The separate supercongruence on the same sequence is outside this identity."
                ], DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a351858-bala-coefficient-identity"),
                    ResolutionKind.Proved)))));
    private static DocumentBlock Node(string name, string title, Formula formula, string[] prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("bala-a351858-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks([.. prose.Select(text => Paragraph(Text(text)))]), role, resolution);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula AllN(Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), N(), body);
    private static Formula SourceFormula()
    {
        Formula n = F.Id("n"), x = F.Id("X");
        var tri = Add(Add(D(1), x), Pow(x, D(2)));
        return Disp(AllN(Equal(App("source", n), Multiply(Pow(tri, Multiply(D(3), n)),
            App("inverse", Pow(Add(D(1), x), Multiply(D(2), n)))))));
    }
    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var range = App("range", Add(App("div", n, D(2)), D(1)));
        var summand = Multiply(App("choose", Multiply(D(3), n), k), App("choose", Subtract(n, k), k));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(AllN(Equal(App("coeff", n, App("source", n)), App("natCastQ", sum))));
    }
}
