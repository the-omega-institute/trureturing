using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Stieltjes;

internal sealed class FarihFourthMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Stieltjes/FarihFourthMoment.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Convexity/farih2026meanefficiency");

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Laws => F.Seq(F.Mathcal, F.Grp(F.Id("M")), F.Open, Real, F.Close);
    private static Formula X => F.Id("x");
    private static Formula K => F.Id("k");
    private static Formula M => F.Id("m");
    private static Formula U => F.Seq(F.Mu, F.Underscore, F.Grp(F.D(4)));
    private static Formula W => F.Seq(F.Mu, F.Underscore, F.Grp(F.D(3)));
    private static Formula Power => F.Seq(X, F.Caret, F.Grp(K));
    private static Formula OnePlusX => F.Seq(F.D(1), F.Plus, X);
    private static Formula ElevenEighteenths => Ratio(11, 18);
    private static Formula ThirtySevenSixtieths => Ratio(37, 60);

    private static Formula Digits(int number) =>
        number < 10 ? F.D((byte)number) : F.D((byte)(number / 10), (byte)(number % 10));

    private static Formula Ratio(int numerator, int denominator) =>
        F.Seq(F.Frac, F.Grp(Digits(numerator)), F.Grp(Digits(denominator)));

    private static Formula Call(string name, params Formula[] arguments) =>
        F.Seq(F.Operatorname, F.Grp(F.Id(name)), F.Open, F.Seq(arguments), F.Close);

    private static Formula Integral(Formula integrand, Formula measure) =>
        F.Seq(F.Int, F.Underscore, F.Grp(Real), F.Sp, integrand, F.Thin,
            F.Mathrm, F.Grp(F.Id("d")), measure, F.Open, X, F.Close);

    private static Formula Moment(Formula k, Formula m) =>
        Call("HasRawMoment", F.Mu, F.Comma, k, F.Comma, m);

    private static Formula MomentClass(byte k, Formula measure) =>
        F.Seq(F.Id("M"), F.Underscore, F.Grp(F.D(k)), F.Open, measure, F.Close);

    private static Formula Mean(Formula measure) => Call("meanEfficiency", measure);

    private static Formula Dirac(Formula point) => F.Seq(F.DeltaLower, F.Underscore, F.Grp(point));

    private static Formula ForAll(Formula variable, Formula domain, Formula clause) =>
        F.Seq(F.Forall, F.Sp, variable, F.Colon, domain, F.Comma, F.Sp, clause);

    private static Formula And(params Formula[] clauses) =>
        F.Seq(clauses.SelectMany((clause, index) =>
            index == 0 ? new[] { clause } : new[] { F.Sp, F.Land, F.Sp, clause }).ToArray());

    private static Formula InParens(Formula clause) => F.Seq(F.Open, clause, F.Close);

    private static Formula AlmostEverywhere(Formula measure, Formula clause) =>
        F.Seq(F.Forall, F.Caret, F.Grp(F.Mathrm, F.Grp(F.Id("ae"))),
            F.Underscore, F.Grp(X, F.Sim, measure), F.Sp, InParens(clause));

    private static Formula FirstThree => F.Seq(MomentClass(3, F.Mu), F.Iff, F.Sp, And(
        Call("IsProbabilityMeasure", F.Mu),
        AlmostEverywhere(F.Mu, F.Seq(F.D(0), F.Le, F.Sp, X)),
        Moment(F.D(1), F.D(1)),
        Moment(F.D(2), Ratio(5, 3)),
        Moment(F.D(3), F.D(3))));

    private static Formula NoTwoPoints => ForAll(F.Seq(F.Id("a"), F.Comma, F.Id("b")), Real,
        F.Seq(F.Neg, InParens(AlmostEverywhere(F.Mu,
            F.Seq(X, F.Eq, F.Id("a"), F.Lor, F.Sp, X, F.Eq, F.Id("b"))))));

    private static Formula UpperBound => ForAll(F.Mu, Laws,
        F.Seq(MomentClass(4, F.Mu), F.Implies, Mean(F.Mu), F.Le, ElevenEighteenths));

    private static Formula StrictImprovement => ForAll(F.Nu, Laws,
        F.Seq(MomentClass(4, F.Nu), F.Implies, Mean(F.Nu), F.Lt, Mean(W)));

    private static Formula Conjunct(Formula clause) => F.Seq(F.Amp, F.Land, F.Sp, clause);

    private static Formula Result => new Formula.Aligned([
        F.Seq(F.Amp, And(MomentClass(4, U), F.Seq(Mean(U), F.Eq, ElevenEighteenths))),
        Conjunct(InParens(UpperBound)),
        Conjunct(InParens(ForAll(F.Mu, Laws, F.Seq(MomentClass(4, F.Mu), F.Implies, NoTwoPoints)))),
        Conjunct(And(MomentClass(3, W), F.Seq(Mean(W), F.Eq, ThirtySevenSixtieths))),
        Conjunct(InParens(StrictImprovement))
    ]);

    private static DocumentBlock.Describe Definition(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)), provenance,
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At one prescribed moment vector, a feasible three-moment law has mean efficiency 37/60, above the attained four-moment maximum 11/18. No two-point law satisfies all four moments.",
        H("Farih’s exact fourth-moment maximum"),
        Blocks(
            Definition("farih-raw-moment", "rawMoment", "Raw moment",
                F.Seq(Call("rawMoment", F.Mu, F.Comma, K), F.Eq, Integral(Power, F.Mu)),
                AssessedProvenance.FromRepo(Source),
                "The variable μ ranges over Borel measures on the real line and k over natural numbers. The integral is the real Bochner integral."),
            Definition("farih-prescribed-raw-moment", "HasRawMoment", "Prescribed integrable moment",
                F.Seq(Moment(K, M), F.Iff, F.Sp, And(
                    Call("Integrable", X, F.Mapsto, F.Sp, Power, F.Comma, F.Mu),
                    F.Seq(Call("rawMoment", F.Mu, F.Comma, K), F.Eq, M))),
                AssessedProvenance.FromRepo(Source),
                "The function x ↦ xᵏ must be integrable against μ, and its raw moment must equal the real number m. The integrability hypothesis gives the moment its usual interpretation throughout the proof."),
            Definition("farih-three-moments", "FirstThreeMoments", "First-three-moment class",
                FirstThree, AssessedProvenance.FromRepo(Source),
                "Here M₃(μ) denotes FirstThreeMoments μ. The structure requires probability, nonnegative x almost everywhere with respect to μ, and integrable raw moments 1, 5/3 and 3 in orders one, two and three."),
            Definition("farih-four-moments", "FirstFourMoments", "First-four-moment class",
                F.Seq(MomentClass(4, F.Mu), F.Iff, F.Sp, And(MomentClass(3, F.Mu), Moment(F.D(4), Ratio(17, 3)))),
                AssessedProvenance.FromRepo(Source),
                "Here M₄(μ) denotes FirstFourMoments μ. It retains all five fields of FirstThreeMoments and prescribes the integrable fourth raw moment 17/3."),
            Definition("farih-pointwise-efficiency", "efficiency", "Efficiency at α = 1",
                F.Seq(Call("efficiency", X), F.Eq, F.Frac, F.Grp(F.D(1)), F.Grp(OnePlusX)),
                AssessedProvenance.FromLiterature(Source),
                "The real function uses the inverse of 1+x. Farih’s law is supported almost everywhere on x ≥ 0, where the denominator is positive."),
            Definition("farih-mean-efficiency", "meanEfficiency", "Mean efficiency",
                F.Seq(Mean(F.Mu), F.Eq, Integral(Call("efficiency", X), F.Mu)),
                AssessedProvenance.FromLiterature(Source),
                "Mean efficiency is the Bochner integral against μ. The proof establishes integrability on every feasible law using the bound by one on the nonnegative half-line."),
            Definition("farih-uniform-law", "uniform012", "The attaining four-moment law",
                F.Seq(U, F.Eq, Ratio(1, 3), Dirac(F.D(0)), F.Plus, Ratio(1, 3), Dirac(F.D(1)),
                    F.Plus, Ratio(1, 3), Dirac(F.D(2))),
                AssessedProvenance.FromRepo(Source),
                "μ₄ is uniform012. Each δ denotes a Dirac measure at its subscript. The nonnegative weights act as scalars in the extended nonnegative reals."),
            Definition("farih-relaxed-law", "threeMomentWitness", "The first-three-moment witness",
                F.Seq(W, F.Eq, Ratio(10, 27), Dirac(F.D(0)), F.Plus,
                    Ratio(16, 27), Dirac(Ratio(3, 2)), F.Plus, Ratio(1, 27), Dirac(F.D(3))),
                AssessedProvenance.FromRepo(Source),
                "μ₃ is threeMomentWitness. Its exact weights and atoms give the first three prescribed moments."),
            Describe.Lean(
                DescribeId.Create("farih-exact-fourth-moment-answer"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Attainment, two-point infeasibility, and strict improvement"),
                StatementSource.FromAuthor(F.Disp(Result)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write ℳ(ℝ) for all Borel measures on ℝ. The superscript ae and subscript x ∼ μ bind x almost everywhere with respect to μ. The upper bound holds for every feasible μ, and μ₄ attains it. Two-point concentration is impossible for any pair of real points, including a repeated point. Every four-moment feasible law ν lies strictly below the specific relaxed witness μ₃.")),
                    Paragraph(Text("The quartic Q(x) = (x⁴ − 7x³ + 20x² − 32x + 36)/36 has gap Q(x) − (1+x)⁻¹ = x(x−1)²(x−2)²/[36(1+x)]. This identity gives a pointwise majorant on x ≥ 0. All its monomials are integrable on a feasible law. Integrating Q gives 11/18, and the gap vanishes at the three atoms of μ₄.")),
                    Paragraph(Text("Concentration on a pair a,b forces the raw-moment recurrence mₙ₊₂ = (a+b)mₙ₊₁ − ab mₙ. Normalization and the first three moments force a+b = 2 and ab = 1/3, hence m₄ = 49/9. This conflicts with 17/3 for every such pair.")),
                    Paragraph(Text("Direct integration on μ₃ gives 37/60, exceeding 11/18 by 1/180. In the paper’s earlier bracket, variance 5/3 − 1 = 2/3 gives the upper endpoint U(1,2/3) = 5/8 by Eqs. (13) and (30), a gap of 1/72 from the four-moment maximum. The Lean result carries the strict witness comparison. The general fourth-moment hierarchy, the exact three-moment optimum and its attainment, and optimizer uniqueness lie outside its statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("farih-fourth-moment-mean-efficiency"),
                    ResolutionKind.Proved)))));
}
