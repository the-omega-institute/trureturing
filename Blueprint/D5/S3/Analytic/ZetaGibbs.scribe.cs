using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ZetaGibbsDocument : IScribeDocumentDefinition
{
    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta distribution is the Gibbs measure for logarithmic integer energy.",
        H("The Zeta Distribution as an Integer Gibbs Measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-energy-has-zeta-boltzmann-weight"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.weight"),
                H("Logarithmic energy has zeta Boltzmann weight"),
                StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.Id("weight"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural-number state n and real inverse temperature s, the weight " +
                    "is the extended-nonnegative-real image of n to the power minus s. This is " +
                    "the Boltzmann factor exp(-s log n) on positive integers. At positive s the " +
                    "zero slot has weight zero, while the state n = 1 always has weight one."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("the-partition-function-is-the-total-zeta-weight"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.partitionFunction"),
                H("The partition function is the total zeta weight"),
                StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.Id("partitionFunction"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The partition function Z(s) is the ENNReal sum of all logarithmic " +
                    "Boltzmann weights over natural numbers. The zero slot contributes no mass " +
                    "in the regime s > 1, so this indexing agrees with the positive-integer " +
                    "Dirichlet series."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("the-partition-function-is-finite-above-one"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.partition_function_ne_top"),
                H("The partition function is finite above one"),
                StatementSource.FromAuthor(In(Seq(
                    D(1), Lt, F.Id("s"), Sp, Rightarrow, Sp,
                    F.Id("Z"), Open, F.Id("s"), Close, Neq, Sp, Infty))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For s > 1, the real p-series n^(-s) is summable. Mapping its nonnegative " +
                    "terms into ENNReal therefore gives a partition function different from " +
                    "infinity. The proof reuses Real.summable_nat_rpow and the standard ENNReal " +
                    "finite-tsum bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-partition-function-is-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.partition_function_pos"),
                H("The partition function is positive"),
                StatementSource.FromAuthor(In(Seq(D(0), Lt, F.Id("Z"), Open, F.Id("s"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The n = 1 summand is exactly one, so the full partition function is " +
                    "strictly positive for every real s. In particular, normalization above " +
                    "inverse temperature one has both a nonzero and a finite denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalization-produces-the-zeta-pmf"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.zetaDist"),
                H("Normalization produces the zeta PMF"),
                StatementSource.FromAuthor(FormulaDsl.Disp(FormulaDsl.Id("zetaDist"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For s > 1, PMF.normalize applies to the zeta weight because its total is " +
                    "positive and finite. The result is a genuine probability mass function on " +
                    "natural numbers, with the zero state retaining zero mass."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("the-zeta-pmf-has-the-gibbs-value-formula"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.zeta_dist_apply"),
                H("The zeta PMF has the Gibbs value formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(1), Lt, F.Id("s"), Sp, Rightarrow, Sp,
                    F.Id("P"), Underscore, Grp(F.Id("s")), Open, F.Id("n"), Close, Eq,
                    Frac,
                    Grp(F.Id("w"), Underscore, Grp(F.Id("s")), Open, F.Id("n"), Close),
                    Grp(Sum, Underscore,
                        Grp(F.Id("m"), InMacro, Sp, Mathbb, Grp(F.Id("N"))),
                        F.Id("w"), Underscore, Grp(F.Id("s")), Open, F.Id("m"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pointwise evaluation of PMF.normalize gives the Boltzmann weight times the " +
                    "inverse total weight, equivalently n^(-s) divided by Z(s). This is the exact " +
                    "Gibbs formula rather than only a support or proportionality statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-real-partition-function-is-riemann-zeta"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaGibbs.partition_function_toReal_eq_riemannZeta"),
                H("The real partition function is Riemann zeta"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(1), Lt, F.Id("s"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("toReal")), Open,
                    F.Id("Z"), Open, F.Id("s"), Close, Close, Eq,
                    Zeta, Open, F.Id("s"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After taking the finite ENNReal total back to the reals and embedding it in " +
                    "the complex numbers, the partition function equals mathlib's riemannZeta at " +
                    "the real argument s. The proof uses mathlib's Dirichlet-series identity in " +
                    "the half-plane s > 1 and explicitly reconciles real rpow with complex cpow."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-temperature-one-forces-divergence"),
                DeclarationHandle.Create("D5/S3/Analytic/ZetaGibbs.weight_one_tsum_eq_top"),
                H("Inverse temperature one forces divergence"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Z"), Open, D(1), Close, Eq, Infty))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At s = 1 the weight series is the harmonic series and its ENNReal total is " +
                    "infinity. Thus the strict hypothesis 1 < s bears the normalizability of the " +
                    "ensemble: PMF.normalize cannot receive the required finite-total proof at " +
                    "the critical inverse temperature."))),
                DescribeRole.Theorem))));
}
