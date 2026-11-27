using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletFiniteZeroFreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arithmetic tests for Dirichlet zero exclusion",
        H("An actual L-function criterion with horizontal margin"),
        Blocks(
            Paragraph(Text("Let χ be a primitive nonprincipal complex Dirichlet character "
                + "of positive modulus q. Fix real C and T, a positive real ε, and a "
                + "natural arithmetic cutoff X. The moments are the negative real parts "
                + "of the normalized von Mangoldt sums on the line Re s = 2.")),
            Definition("moment-start", "momentStart", "The starting exponent",
                Equal(At("momentStart", F.Id("B"), F.Id("C"), F.Id("r")),
                    At("add", F.D(2), At("ceilingNat", At("max",
                        At("ratio", At("realLog", At("mul", F.D(1,6), F.Id("B"))),
                            At("realLog", At("ratio", F.D(4), F.D(3)))),
                        At("ratio", At("realLog", At("mul", F.D(6),
                            At("add", F.Id("C"), F.D(2)))), At("realLog",
                            At("ratio", At("ratio", F.D(3), F.D(2)), F.Id("r")))))))),
                "Write M = momentStart(B,C,r). The first threshold controls the far "
                    + "spectrum; the second controls amplification. M is always at least two. "
                    + "The real logarithm is total, and all ceilings are natural ceilings."),
            Definition("moment-order", "momentOrder", "The last tested order",
                Equal(At("momentOrder", F.Id("B"), F.Id("C"), F.Id("r")),
                    At("sub", At("mul", At("momentStart", F.Id("B"), F.Id("C"),
                        F.Id("r")), At("power", F.D(6), At("ceilingNat",
                            At("mul", F.D(4), F.Id("B"))))), F.D(1))),
                "Write K = M 6^ceil(4B) - 1, using natural subtraction."),
            Definition("grid-size", "gridSize", "The number of grid intervals",
                Equal(At("gridSize", F.Id("T"), F.Id("eps")),
                    At("max", F.D(1), At("ceilingNat", At("ratio",
                        At("mul", F.D(2), F.Id("T")), F.Id("eps"))))),
                "J = max(1,ceil(2T/ε)); the height grid has J+1 points."),
            Definition("grid-point", "gridPoint", "The grid height",
                Equal(At("gridPoint", F.Id("T"), F.Id("eps"), F.Id("j")),
                    At("add", At("neg", F.Id("T")), At("ratio",
                        At("mul", At("mul", F.D(2), F.Id("T")), F.Id("j")),
                        At("gridSize", F.Id("T"), F.Id("eps"))))),
                "t(j) = -T+2Tj/J. The tests use 0 ≤ j ≤ J, including both endpoints."),
            Paragraph(Text("For any square-summable complex spectrum z with square mass "
                + "at most B and 0 < r < 3/2, it suffices to bound the power moments "
                + "Re(sum z(i)^(k+1)) by (C+1)(2/3)^k only when M-1 ≤ k ≤ K "
                + "and M divides k+1. Every spectral norm is then strictly less than 1/r. "
                + "The indices with norm greater than 1/2 form a finite set of size at "
                + "most ceil(4B). Simultaneous circle approximation aligns their phases "
                + "at n = Mu with 1 ≤ u ≤ 6^ceil(4B). The complementary norm is at "
                + "most B(1/2)^(n-2). Put D = (C+1)(3/2) and A = ((3/2)/r)^n > 1. A norm "
                + "at least 1/r forces A/2 ≤ D+1/4 ≤ A/4+1/4, a contradiction.")),
            Paragraph(Text("The grid argument needs Re ρ ≤ 1 only for a member already "
                + "satisfying Re ρ ≥ 1/2+ε and |Im ρ| ≤ T. All other members need "
                + "only the square budgets and sparse moments at the grid centers. "
                + "The starting radius and square summability remain essential: at "
                + "r = 3/2 the amplification logarithm vanishes, while a divergent "
                + "series has a totalized tsum that need not express its mass.")),
            Definition("zero-budget", "zeroBudget", "The inverse-square budget",
                Equal(At("zeroBudget", F.Id("q"), F.Id("T")),
                    At("add", At("realLog", At("mul", F.Id("q"),
                        At("add", F.Id("T"), F.D(3)))), F.D(4))),
                "Write B = log(q(T+3))+4. For nonnegative T this bounds the sum of "
                    + "squared inverse distances over all zeros, with multiplicity."),
            Definition("zero-order", "zeroOrder", "The finite order limit",
                Equal(At("zeroOrder", F.Id("q"), F.Id("C"), F.Id("T"), F.Id("eps")),
                    At("momentOrder", At("zeroBudget", F.Id("q"), F.Id("T")),
                        F.Id("C"), At("sub", At("ratio", F.D(3), F.D(2)),
                            At("ratio", F.Id("eps"), F.D(2))))),
                "Put r = 3/2 - ε/2, M = 2 + ceil(max(log(16B)/log(4/3), "
                    + "log(6(C+2))/log((3/2)/r))), and K = M 6^ceil(4B) - 1. "
                    + "Each ceiling is the natural ceiling. This is the same momentOrder "
                    + "used by the finite spectral exclusion theorem."),
            Describe.Lean(DescribeId.Create("finite-moment-zero-free"),
                DeclarationHandle.Create(
                    "D5/S3/CharacterSums/DirichletFiniteZeroFree.finite_moment_zero_free"),
                H("The finite arithmetic criterion"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let J = max(1,ceil(2T/ε)) and "
                        + "t(j) = -T + 2Tj/J for 0 ≤ j ≤ J. Suppose "
                        + "X ≥ exp(4(K+1)) and, for all those j and M-1 ≤ k ≤ K "
                        + "with M dividing k+1, "
                        + "finiteMoment(χ,k,X,t(j)) ≤ (C+1/3)(2/3)^k. Then L(s,χ) ≠ 0 "
                        + "whenever Re s ≥ 1/2+ε and |Im s| ≤ T, including the "
                        + "rectangle boundary. If T ≥ 0, it also excludes every "
                        + "closed disk |s-(2+i t(j))| ≤ 3/2-ε/2, for 0 ≤ j ≤ J. "
                        + "The theorem allows any real C and T. "
                        + "A negative T gives an empty rectangle. If ε > 1/2 the "
                        + "usual nonvanishing to the right of one already suffices.")),
                    Paragraph(Text("Repeat each actual zero according to its positive "
                        + "analytic order. Absolute convergence transports the weighted "
                        + "power sums and the inverse-square budget to this repeated "
                        + "family. The finite arithmetic tail has magnitude at most "
                        + "(2/3)^(k+1), so a tested coefficient C+1/3 gives C+1 for "
                        + "the full moments. "
                        + "The grid remains inside the height interval, and the finite "
                        + "spectral theorem gives inverse distances strictly below 1/r, "
                        + "which excludes each closed grid disk of radius r when 0 < r < 3/2. "
                        + "At ε = 3 the disk is its nonzero center of real part two; "
                        + "at ε > 3 its radius is negative and the disk is empty. "
                        + "The rectangle is excluded by the same detector and grid geometry. "
                        + "Entire nonzero L-functions have positive finite order at every "
                        + "zero, so this excludes actual zeros, not just an auxiliary list.")),
                    Paragraph(Text("For a prime p, every nonprincipal character modulo p "
                        + "is primitive: its conductor divides p, and conductor one would "
                        + "make it principal. Set T = 4√p, "
                        + "B = log(p(4√p+3))+4, J = max(1,ceil(8√p/ε)), "
                        + "K = momentOrder(B,C,3/2-ε/2), and "
                        + "X ≥ exp(4(K+1)). The stated finite inequalities then exclude "
                        + "all zeros with Re s ≥ 1/2+ε and |Im s| ≤ 4√p. "
                        + "This applies in particular to nonprincipal characters whose "
                        + "order divides rad(p-1); no character-order assumption is needed.")),
                    Paragraph(Text("The exact finite-height premise used for problem 985 "
                        + "asks for Re s > 1/2 at this height. One fixed positive ε leaves "
                        + "a strip untreated. To obtain that premise by this criterion, "
                        + "the finite tests must be supplied for every positive ε, or for "
                        + "a sequence tending to zero. C and X may vary with ε. "
                        + "The criterion proves no unconditional arithmetic moment "
                        + "inequalities and does not establish that remaining supply."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title,
        Formula formula, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/CharacterSums/DirichletFiniteZeroFree." + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Claim()
    {
        var q = F.Id("q");
        var c = F.Id("chi");
        var C = F.Id("C");
        var T = F.Id("T");
        var e = F.Id("eps");
        var x = F.Id("X");
        var k = At("zeroOrder", q, C, T, e);
        var cutoff = At("le", At("exp", At("mul", F.D(4), At("add", k, F.D(1)))), x);
        var m = At("momentStart", At("zeroBudget", q, T), C,
            At("sub", At("ratio", F.D(3), F.D(2)), At("ratio", e, F.D(2))));
        var j = F.Id("j");
        var n = F.Id("k");
        var orders = At("and", At("le", At("sub", m, F.D(1)), n),
            At("and", At("le", n, k), At("divides", m, At("add", n, F.D(1)))));
        var bound = At("mul", At("add", C, At("ratio", F.D(1), F.D(3))),
            At("power", At("ratio", F.D(2), F.D(3)), n));
        var tests = All("j", At("Naturals"), At("implies",
            At("le", j, At("gridSize", T, e)), All("k", At("Naturals"),
                At("implies", orders, At("le",
                    At("finiteMoment", c, n, x, At("gridPoint", T, e, j)), bound)))));
        var rectangle = At("closedRectangleZeroFree", c,
            At("add", At("ratio", F.D(1), F.D(2)), e), T);
        var disks = At("implies", At("le", F.D(0), T), All("j", At("Naturals"), At("implies",
                At("le", j, At("gridSize", T, e)), At("closedDiskZeroFree", c,
                    At("add", F.D(2), At("mul", At("gridPoint", T, e, j), At("imaginaryUnit"))),
                    At("sub", At("ratio", F.D(3), F.D(2)),
                        At("ratio", e, F.D(2)))))));
        return F.Disp(All("q", At("PositiveNaturals"),
            All("chi", At("ComplexDirichletCharacters", q),
            All("C", At("Reals"), All("T", At("Reals"),
            All("eps", At("PositiveReals"), All("X", At("Naturals"),
                At("implies", At("and", At("primitiveNonprincipal", c),
                    At("and", cutoff, tests)), At("and", rectangle, disks)))))))));
    }

    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
