using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class HighCosineThresholdDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/HighCosineThreshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-level probability law minimizes squared mass for high joint cosine thresholds.",
        H("The high-threshold minimum for two cosine moments"),
        Blocks(
            Paragraph(Text(
                "For a finite index type I, write c for its real readout and use 2c² − 1 as the second readout. "
                + "The value one occurs at a unique index. With levels ℓ and u, write g(x) = x − (2x² − 1), "
                + "p = −g(ℓ)/(g(u) − g(ℓ)), b = pu + (1−p)ℓ and r = (1−a)/(1−b). "
                + "The law gives mass 1−r to that index, rp to the level u, and r(1−p) to "
                + "the level ℓ. Each level’s mass is divided equally among its indices.")),
            Paragraph(Text(
                "The notation H(c,z,u,ℓ) means c(i)=1 exactly at i=z, u+ℓ<0, "
                + "and g(ℓ)<0<g(u). Write J(c,z,u,ℓ) for the same conditions with u+ℓ≤0. "
                + "R(c,u,ℓ) means both levels are attained and each value "
                + "is either one or belongs to [ℓ,u]. The predicate Certified(a) requires "
                + "nonnegative weights of mass one, both moments equal to a, the exact squared mass, "
                + "and the squared-distance lower bound for every feasible competitor. "
                + "A feasible competitor has nonnegative weights of mass one and both moments at least a. "
                + "E is the sum of squared weights. "
                + "StrictlyFeasible(w,a) means w is nonnegative of mass one with both moments strictly above a.")),
            Describe.Lean(
                DescribeId.Create("finite-readout-threshold-certificate"),
                DeclarationHandle.Create(Owner + ".high_threshold_certificate"),
                H("A finite interpolation certificate"),
                StatementSource.FromAuthor(FiniteStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sign assumptions imply ℓ < u < 1 by g(x)=(1−x)(2x+1). "
                    + "Interpolate the three weights by a quadratic P with moment coefficients β "
                    + "and γ in the basis 1, x, 2x² − 1. For each of β, γ and the values −P(x) at "
                    + "intermediate levels, take the slope 1 − f(1)/f(0) as a function of r. "
                    + "Let B be the maximum of those slopes and one. The cutoff lies strictly between b and one. At thresholds a in "
                    + "[1 − (1−b)/B, 1] the two moments equal a. The squared mass is "
                    + "(1−r)² + r²(p²/nᵤ + (1−p)²/nₗ), where nᵤ and nₗ are level counts. "
                    + "The excess squared mass of any feasible law bounds its squared distance "
                    + "from the candidate, which gives uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-descent-below-cutoff"),
                DeclarationHandle.Create(Owner + ".exists_smaller_energy_below_threshold"),
                H("A feasible descent below the cutoff"),
                StatementSource.FromAuthor(DescentStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If u+ℓ=0, the first multiplier has zero intercept and its slope is assigned one, "
                    + "already included in the maximum. Its negative value at positive r still "
                    + "permits a feasible perturbation within the support. "
                    + "When b < a is below the cutoff, all three supporting levels have positive "
                    + "weight. If a moment coefficient is negative, a perturbation within the "
                    + "support increases that moment and preserves the other. If an intermediate "
                    + "value of P is positive, a perturbation adds weight there and uses the "
                    + "three support levels to preserve both moments. A sufficiently small "
                    + "positive step decreases the squared mass in either case. At a = b, the weight at z is zero. "
                    + "A small mixture toward the point mass at z raises both moments and lowers squared mass. "
                    + "For any strict energy decrease, a further small mixture with this point mass preserves "
                    + "the energy inequality and makes both moment constraints strict."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-half-cycle-representative"),
                DeclarationHandle.Create(Owner + ".cyclic_fold"),
                H("A representative in the positive half of the cycle"),
                StatementSource.FromAuthor(FoldStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the residue k, write K(k) for its natural representative and "
                    + "c(q,n)=cos(2πn/q) for a natural index n. When K(k) is nonzero, "
                    + "choose K(k) if it is at most ⌊q/2⌋ and q−K(k) otherwise. "
                    + "Cosine is invariant under reflection of the angle about π."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-high-threshold-certificate"),
                DeclarationHandle.Create(Owner + ".cyclic_high_threshold_certificate"),
                H("The sharp high-threshold interval on a cycle"),
                StatementSource.FromAuthor(CyclicStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For q at least four use c(k) = cos(2πk/q) on its canonical residue "
                    + "representatives. The first off-center maximum occurs at k = 1, and a "
                    + "minimum occurs at the integer part of q/2. Reflecting angles into "
                    + "[0, π] proves the required level order and strict signs. The cutoff lies "
                    + "strictly between b and one. The law minimizes squared mass from the "
                    + "cutoff through one, and a feasible law has smaller squared mass "
                    + "with both moments strictly above the threshold at every a from b up to the cutoff, excluding the cutoff."))),
                DescribeRole.Theorem))));

    private static Formula Cutoff => new Formula.Subscript(F.Id("a"), F.Id("crit"));

    private static Formula CertifiedInterval() =>
        Seq(Forall, Sp, F.Id("a"), Sp, InMacro, Sp, OpenBracket, Cutoff, Comma, D(1),
            CloseBracket, Comma, Sp, Operatorname, Grp(F.Id("Certified")), Open, F.Id("a"), Close);

    private static Formula Descent() =>
        Seq(Forall, Sp, F.Id("a"), Sp, InMacro, Sp, OpenBracket, F.Id("b"), Comma, Cutoff, Close,
            Comma, Sp, Exists, Sp, F.Id("w"), Comma, Sp, Operatorname, Grp(F.Id("StrictlyFeasible")),
            Open, F.Id("w"), Comma, F.Id("a"), Close, Sp, Land, Sp, F.Id("E"), Open, F.Id("w"),
            Close, Lt, F.Id("E"), Open, new Formula.Subscript(F.Id("v"), F.Id("a")), Close);

    private static Formula T(string name, params Formula[] args) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Context(bool descent)
    {
        var i = F.Id("I");
        var c = F.Id("c");
        var z = F.Id("z");
        var u = F.Id("u");
        var ell = F.Id("l");
        var readout = Seq(Forall, Sp, c, Colon, i, Sp, To, Sp, Reals, Comma);
        var levels = Seq(Forall, Sp, u, Comma, ell, Sp, InMacro, Sp, Reals, Comma);
        if (!descent)
            return Seq(readout, Sp, Forall, Sp, z, Sp, InMacro, Sp, i, Comma, Sp, levels, Sp,
                T("H", c, z, u, ell), Sp, Land, Sp, T("R", c, u, ell));
        var j = F.Id("j");
        var k = F.Id("k");
        return Seq(readout, Sp, Forall, Sp, z, Comma, j, Comma, k, Sp, InMacro, Sp, i, Comma, Sp, levels, Sp,
            T("J", c, z, u, ell), Sp, Land, Sp, T("c", j), Eq, u, Sp, Land, Sp, T("c", k), Eq, ell);
    }

    private static Formula FiniteStatement() => Disp(new Formula.Aligned([
        Seq(Amp, Context(false), Sp, Longrightarrow, Sp),
        Seq(Amp, F.Id("b"), Lt, Cutoff, Lt, D(1), Sp, Land, Sp, Open, CertifiedInterval(), Close)
    ]));

    private static Formula DescentStatement() => Disp(new Formula.Aligned([
        Seq(Amp, Context(true), Sp, Longrightarrow, Sp),
        Seq(Amp, Descent())
    ]));

    private static Formula FoldStatement()
    {
        var q = F.Id("q");
        var k = F.Id("k");
        var n = F.Id("n");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var representative = T("K", k);
        var half = Seq(Lfloor, new Formula.Fraction(q, D(2)), Rfloor);
        var boundsAndIdentity = Seq(D(1), Sp, Le, Sp, n, Sp, Le, Sp, half, Sp, Land, Sp,
            T("c", q, representative), Eq, T("c", q, n));
        var alternatives = Seq(Open, n, Eq, representative, Sp, Lor, Sp,
            n, Eq, Subtract(q, representative), Close);
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Sp, InMacro, Sp, naturals, Comma, Sp,
                Forall, Sp, k, Sp, InMacro, Sp, T("Fin", q), Comma, Sp,
                representative, Sp, Neq, Sp, D(0), Sp, Longrightarrow, Sp),
            Seq(Amp, Exists, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
                boundsAndIdentity, Sp, Land, Sp, alternatives)
        ]));
    }

    private static Formula CyclicStatement()
    {
        var q = F.Id("q");
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                q, Ge, D(4), Sp, Longrightarrow, Sp, OpenBracket, F.Id("b"), Lt, Cutoff, Lt, D(1), Comma),
            Seq(Amp, CertifiedInterval(), Comma),
            Seq(Amp, Descent(), CloseBracket)
        ]));
    }
}
