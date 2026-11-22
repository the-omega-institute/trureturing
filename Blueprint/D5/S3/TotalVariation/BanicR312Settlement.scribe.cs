using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BanicR312SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/BanicR312Settlement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/TotalVariation/banicelezovic2026cyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At four draws, a fourth bin increases cyclic multinomial dispersion.",
        H("A bin-count reversal for cyclic multinomial dispersion"),
        Blocks(
            Definition("CountVector", "count-vector", "Bounded count vectors",
                Equal(Carrier(), F.Seq(Fin(Id("n")), F.Sp, F.To, F.Sp, Fin(Add(Id("N"), Num(1))))),
                AssessedProvenance.FromRepo(),
                "For natural n and N, a vector supplies one count between zero and N for each bin. "
                + "The carrier includes all such vectors. Write kᵢ for the natural value of the count in bin i."),
            Definition("countVectorMeasurableSpace", "count-vector-measurable-space", "Measurable sets of count vectors",
                Equal(Sub(F.Seq(F.Mathcal, F.Grp(Id("A"))), Id("n"), Id("N")),
                    Apply(F.Seq(F.Mathcal, F.Grp(Id("P"))), Carrier())),
                AssessedProvenance.FromRepo(),
                "For every natural n and N the named instance is the top measurable space on the carrier. "
                + "Its measurable sets are all subsets of that carrier."),
            Definition("multinomialMass", "multinomial-mass", "Uniform multinomial point mass",
                Equal(Mass(Id("k")), MassCases()),
                AssessedProvenance.FromLiterature(Source),
                "For natural n and N and each vector k in the carrier, the mass is in the extended nonnegative "
                + "reals. Interpret the factorials and reciprocal in that type. The zero case enforces the "
                + "total N, and the factor (1/n) to the power N specializes equation (2.2) to uniform bins."),
            Definition("multinomialLaw", "multinomial-law", "Measure of the count vector",
                Equal(Law(), F.Seq(Sub(F.Sum, F.Seq(Id("k"), F.Sp, F.InMacro, F.Sp, Carrier())), F.Sp,
                    Mass(Id("k")), F.Thin, Sub(F.DeltaLower, Id("k")))),
                AssessedProvenance.FromRepo(Source),
                "For natural n and N the measure is the finite sum over the whole count carrier. Each coefficient "
                + "scales the Dirac measure at its own vector. This realizes the uniform count law on the domain "
                + "of Remark 3.12."),
            Definition("cyclicVariation", "cyclic-variation", "Cyclic variation of a count vector",
                Equal(Variation(Id("k")), F.Seq(Sub(F.Sum, BinIndex()), F.Sp, F.Left, F.Bar,
                    Sub(Id("k"), Apply(F.Seq(F.Operatorname, F.Grp(F.Id("finRotate"))), Id("n"), Id("i"))),
                    F.Sp, F.Minus, F.Sp, Sub(Id("k"), Id("i")), F.Right, F.Bar)),
                AssessedProvenance.FromLiterature(Source),
                "For natural n and N and each vector k in the carrier, take differences of the natural counts "
                + "after casting them to the reals. The permutation finRotate advances around the bins and "
                + "sends the last bin to the first, giving the closing edge in equation (2.17)."),
            Definition("dispersionSquared", "cyclic-dispersion-squared", "Variance per draw",
                Equal(VariancePerDraw(), new Formula.Fraction(
                    Apply(Sub(F.Seq(F.Operatorname, F.Grp(F.Id("Var"))), Law()), Sub(Id("D"), Id("n"), Id("N"))),
                    Id("N"))),
                AssessedProvenance.FromLiterature(Source),
                "For natural n and N, take the real variance of the cyclic variation under the count-vector "
                + "measure and divide by the real cast of N. The definition uses Lean's total real division. "
                + "Corollary 3.5 uses this normalization for positive N."),
            Definition("dispersion", "cyclic-dispersion", "Cyclic dispersion",
                Equal(Dispersion(Id("n"), Id("N")), F.Seq(F.Sqrt, F.Grp(VariancePerDraw()))),
                AssessedProvenance.FromLiterature(Source),
                "For natural n and N, apply the nonnegative real square root to the variance per draw. "
                + "Remark 3.12 compares this quantity on the stated positive-sample domain."),
            Describe.Lean(
                DescribeId.Create("cyclic-multinomial-dispersion-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Proposed monotonicities"),
                StatementSource.FromAuthor(F.Disp(Monotonicities())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Nikola Banić and Neven Elezović ask whether the exact dispersion decreases as the bin count "
                    + "grows and increases as the draw count grows. Each adjacent comparison ranges independently "
                    + "over natural n at least three and N at least one. See Remark 3.12, arXiv:2611.14735v1, PDF p. 15. "
                    + "https://arxiv.org/pdf/2611.14735v1#page=15"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-multinomial-dispersion-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the joint monotonicity claim"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(
                    F.Seq(F.Left, F.Open, Monotonicities(), F.Right, F.Close)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For each bin count, sum the integer multinomial weight times D to powers "
                        + "zero, one and two over the bounded count vectors. At (3,4) these sums are (81,312,1488) "
                        + "and at (4,4) they are (256,1120,5888). "
                        + "The zeroth sums give total probability one after division by n to the power N. "
                        + "The first and second sums give the corresponding moments under the same measure.")),
                    Paragraph(Text(
                        "Subtracting the squared first moment from the second moment and dividing by N gives "
                        + "normalized variances 644/729 and 247/256, respectively. Taking the square root "
                        + "preserves the strict increase from three to four bins at four draws. This contradicts "
                        + "the bin-count clause of the conjunction.")),
                    Paragraph(Text(
                        "The original exact calculation also gives variance per draw 3835/4096 at four bins "
                        + "and five draws. In the separate compiled BothReversals proof this gives a strict "
                        + "decrease from four to five draws, refuting the draw-count clause directly. Remark 3.13 "
                        + "asks separately about modes across all bin counts for a fixed draw count. The "
                        + "historical calculation examines that profile at four draws.")),
                    Paragraph(Text(
                        "Claude Code session 07b67e50-10a4-41b3-9622-660f37c654a5 coordinated the historical research. "
                        + "Codex CLI research flight 8964c4b7bb607dfbb7e139d9 screened sources, prepared the exact "
                        + "experiment and mathematical derivation, and compiled the definitions. GPT Pro search "
                        + "seat gptpro-search-s1318 contributed literature search. Loning authored the commits for "
                        + "the exact experiment. https://github.com/the-omega-institute/trureturing/issues/31389")),
                    Paragraph(Text(
                        "Codex CLI flight 6b02a23c137ce8bf24560049 wrote the original Lean proof with both strict "
                        + "comparisons, recorded at Git checkpoint 23991cf8468c1. Codex CLI Stage A flight "
                        + "6b02a69d3e9dff94a3d5d1b7 integrated the direct bin-count proof and its initial exposition "
                        + "and compiled the separate BothReversals proof. MacStudio2 is the Git author on the "
                        + "original proof checkpoint and the integration commit c9b9d86c09b7. Codex CLI flight "
                        + "6b02ad5d9985be77a04c7d34 authored this expanded "
                        + "Scribe exposition. https://github.com/the-omega-institute/trureturing/issues/31389#issuecomment-7076300413"))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string id, string title, Formula formula,
        AssessedProvenance provenance, string commentary) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), provenance,
            Blocks(Paragraph(Text(commentary))), DescribeRole.Definition);

    private static Formula Fin(Formula size) => Apply(F.Seq(F.Mathrm, F.Grp(F.Id("Fin"))), size);

    private static Formula Carrier() => Sub(Id("C"), Id("n"), Id("N"));

    private static Formula BinIndex() => F.Seq(Id("i"), F.Sp, F.InMacro, F.Sp, Fin(Id("n")));

    private static Formula Mass(Formula k) => Apply(Sub(Id("m"), Id("n"), Id("N")), k);

    private static Formula MassCases()
    {
        var countTotal = F.Seq(Sub(F.Sum, BinIndex()), F.Sp, Sub(Id("k"), Id("i")));
        var factorialProduct = F.Seq(Sub(F.Prod, BinIndex()), F.Sp, Sub(Id("k"), Id("i")), F.Bang);
        var coefficient = new Formula.Fraction(F.Seq(Id("N"), F.Bang), factorialProduct);
        var uniformFactor = new Formula.Power(
            F.Seq(F.Left, F.Open, new Formula.Fraction(Num(1), Id("n")), F.Right, F.Close), Id("N"));
        return F.Seq(F.Begin, F.Grp(F.Id("cases")),
            coefficient, F.Thin, uniformFactor, F.Comma, F.Amp, Equal(countTotal, Id("N")), F.RowBreak,
            Num(0), F.Comma, F.Amp, NotEqual(countTotal, Id("N")),
            F.End, F.Grp(F.Id("cases")));
    }

    private static Formula Law() => Sub(F.Mu, Id("n"), Id("N"));

    private static Formula Variation(Formula k) => Apply(Sub(Id("D"), Id("n"), Id("N")), k);

    private static Formula VariancePerDraw() => Apply(Id("v"), Id("n"), Id("N"));

    private static Formula Sub(Formula symbol, Formula index) => new Formula.Subscript(symbol, index);

    private static Formula Sub(Formula symbol, Formula first, Formula second) =>
        Sub(symbol, F.Seq(first, F.Comma, second));

    private static Formula Apply(Formula symbol, Formula argument) => F.Seq(symbol, F.Open, argument, F.Close);

    private static Formula Apply(Formula symbol, Formula first, Formula second) =>
        Apply(symbol, F.Seq(first, F.Comma, second));

    private static Formula Dispersion(Formula n, Formula samples) =>
        Apply(Sub(F.SigmaLower, Id("c")), n, samples);

    private static Formula Monotonicities() => F.Seq(
        Clause(Dispersion(Add(Id("n"), Num(1)), Id("N")), Dispersion(Id("n"), Id("N"))),
        F.Sp, F.Land, F.Sp,
        Clause(Dispersion(Id("n"), Id("N")), Dispersion(Id("n"), Add(Id("N"), Num(1)))));

    private static Formula Clause(Formula left, Formula right) =>
        F.Seq(F.OpenBracket, F.Forall, F.Sp, Id("n"), F.Comma, Id("N"), F.Sp,
            F.InMacro, F.Sp, F.Mathbb, F.Grp(Id("N")), F.Comma, F.Sp,
            Num(3), F.Sp, F.Le, F.Sp, Id("n"), F.Sp, F.Rightarrow, F.Sp,
            Num(1), F.Sp, F.Le, F.Sp, Id("N"), F.Sp, F.Rightarrow, F.Sp,
            left, F.Sp, F.Le, F.Sp, right, F.CloseBracket);
}
