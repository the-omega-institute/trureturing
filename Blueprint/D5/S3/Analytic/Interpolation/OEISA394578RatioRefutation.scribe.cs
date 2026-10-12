using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class OEISA394578RatioRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/OEISA394578RatioRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/kimberling2026a394578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform enclosure for the native moving-point interpolant excludes the asserted consecutive-ratio limit of one quarter.",
        H("The moving-point interpolation ratio cannot tend to one quarter"),
        Blocks(
            Node("p", "The native rational interpolant", PolynomialFormula(),
                "The source says: p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1. The finite set range(n+1) contains indices 0 through n. The node map i -> i+1 is injective over Q and the value map is zero at index zero and one at every other index. Mathlib's Lagrange.interpolate gives exactly the unique polynomial of degree at most n with those values. The source node k corresponds to i+1, while n is unchanged.",
                DescribeRole.Definition, true),
            Node("a", "The source normalization", SequenceFormula(),
                "The source defines a(n) = 2^(2*n-1) p(n,n+1/2); its displayed program uses (1/2) 4^n p(n,n+1/2). The normalization is the rational expression 4^n/2 for every natural n, including zero. At n=0 the sole interpolation value is zero, so p_0 is the zero polynomial and a(0)=0. eval denotes polynomial evaluation over Q; the half in the moving argument is rational.",
                DescribeRole.Definition, true),
            Node("claim", "The printed ratio-limit assertion", ClaimFormula(),
                "The source assertion is: Conjecture: a(n+1)/a(n) -> 1/4. Rat.cast embeds the rational sequence values into R before real division. The ratio function uses the original unshifted indices. Tendsto uses natural atTop and the real neighborhood filter at 1/4. Lean division is total, but a(n) is positive for every n>=1 in the argument below, so all tail denominators are nonzero. A value at n=0 does not affect this limit.",
                DescribeRole.Definition, true),
            Node("result", "The ratio-limit assertion is false", Disp(new Formula.Not(F.Id("claim"))),
                "The sum of the Lagrange bases is one. Removing the basis for node 1 therefore gives p_n. Its error at n+1/2 is the product, for 0<=j<n, of (n-j-3/2)/(-(j+1)). Reversing the numerator factors yields absolute values |j-1/2|. For n>=1 the first factor is 1/2, and each remaining factor is at most its corresponding positive denominator factor. The absolute error is at most 1/2, so p_n(n+1/2) lies in [1/2,3/2]. Positive normalization yields positive a(n) on this tail and the adjacent enclosures give a(n+1)/a(n)>=4/3. A sequence with this eventual lower bound cannot converge to 1/4. This conclusion concerns exactly the printed ratio assertion; it asserts no correct limit, recurrence, integrality or D-finiteness property.",
                DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a394578-interpolation-ratio-limit"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, bool literature,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a394578-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula App(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return new Formula.Apply(Seq(Operatorname, Grp([.. parts])), [.. args]);
    }
    private static Formula Type(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Open, F.Id("fun"), Sp, F.Id(name), Colon, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula RealValue(Formula n) => App("Rat.cast", Type("R"), App("a", n));

    private static Formula PolynomialFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        Formula nodes = Lambda("i", Type("N"), Add(App("Nat.cast", Type("Q"), i), D(1)));
        Formula values = Lambda("i", Type("N"), App("ite", Equal(i, D(0)), D(0), D(1)));
        return Disp(All("n", Type("N"), Equal(App("p", n),
            App("Lagrange.interpolate", App("range", Add(n, D(1))), nodes, values))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", Type("N"), Equal(App("a", n),
            new Formula.Binary(new Formula.Fraction(new Formula.Power(D(4), n), D(2)),
                FormulaBinaryOperator.Multiply,
                App("eval", App("p", n), Add(App("Nat.cast", Type("Q"), n), Half()))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula ratio = Lambda("n", Type("N"),
            new Formula.Fraction(RealValue(Add(n, D(1))), RealValue(n)));
        Formula limit = App("nhds", new Formula.Fraction(D(1), D(4)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            App("Tendsto", ratio, F.Id("atTop"), limit)));
    }
}
