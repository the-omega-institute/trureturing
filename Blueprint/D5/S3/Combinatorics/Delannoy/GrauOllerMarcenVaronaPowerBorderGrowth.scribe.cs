using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Delannoy;

internal sealed class GrauOllerMarcenVaronaPowerBorderGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaPowerBorderGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/grauollermarcenvarona2022delannoy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power-border Delannoy diagonal ratio differs from exp(1) times the half-shift by a quantity tending to zero.",
        H("The power-border Delannoy conjecture"),
        Blocks(
            Node("claimPower", "The additive-error power-border limit",
                new Formula.Logic(F.Id("claimPower"), FormulaLogicOperator.Iff, ClaimBody()),
                "Section 6, arXiv page 18: \"The same phenomenon happens if f_{n,0} = f_{0,n} = n^n, with our conjecture now being f_{n+1,n+1}/f_{n,n} ≈ e · (n + 1/2) [20, OEIS A346385].\" "
                    + "The preceding sentence defines a_n ≈ b_n to mean a_n − b_n → 0 when n → ∞. "
                    + "The border is the natural function k ↦ k^k, including 0^0 = 1. Diagonal entries are cast to the reals before division; the half is a real number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The power-border limit holds", ClaimBody(),
                "The scaled border ratio n b(n−1)/b(n) lies between zero and one. "
                    + "The logarithm remainder estimate and differentiability of exp give its first-order limit at exp(−1). "
                    + "Products of consecutive border ratios preserve the first-order expansion under a summable majorant. "
                    + "Dominated convergence in the exact border convolution transfers that expansion to the normalized diagonal. "
                    + "Reciprocal-ratio algebra gives the half-shift, and first-order ratio transfer gives the asserted additive limit. "
                    + "No explicit rate or second-order expansion is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("gv2501b-bordergrowth"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("gv-power-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var border = Seq(Named("fun"), Sp, Parenthesized(Seq(k, Colon, Naturals())), Sp, Mapsto, Sp, new Formula.Power(k, k));
        var f = Qualified("GrauOllerMarcenVaronaFactorialBorderGrowth", "f");
        var ratio = new Formula.Fraction(
            Cast(Apply(f, Parenthesized(border), Add(n, D(1)), Add(n, D(1)))),
            Cast(Apply(f, Parenthesized(border), n, n)));
        var expression = Subtract(ratio, Multiply(Apply(Qualified("Real", "exp"), D(1)),
            Parenthesized(Add(Cast(n), new Formula.Fraction(D(1), D(2))))));
        var function = Seq(Named("fun"), Sp, Parenthesized(Seq(n, Colon, Naturals())), Sp, Mapsto, Sp, expression);
        return Apply(Qualified("Filter", "Tendsto"), Parenthesized(function),
            Qualified("Filter", "atTop"), Parenthesized(Seq(Mathcal, Grp(F.Id("N")), Parenthesized(D(0)))));
    }
}
