using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SedlakMaximalTesterOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality";
    private const string Problem = "sedlak-reitzner-chiribella-ziman-2016-maximal-tester-orthogonality";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/sedlakreitznerchiribellaziman2016testers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One-step testers are maximally incompatible exactly when their normalization states are orthogonal.",
        H("Maximal incompatibility of one-step testers"),
        Blocks(
            Paragraph(Text(
                "Let d₀ and d₁ be the input and output dimensions, and p and q the respective outcome counts of A and B. "
                + "Write HasNormalization(A, ρ) when A has positive semidefinite effects with sum I ⊗ ρ, and likewise for B and σ. "
                + "The density condition additionally requires the input matrix to be positive semidefinite with trace one. "
                + "Tester robustness is the infimum of the mixing weights in the unit interval at which separate arbitrary "
                + "noise testers make the mixtures marginals of a joint tester.")),
            Describe.Lean(DescribeId.Create("cover-entry"), DeclarationHandle.Create(Module + ".coverEntry"),
                H("Entry of the explicit joint cover"), Hand(CoverEntryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This matrix-valued definition takes real p, q, ε and M and complex square matrices X and Y on a "
                    + "common finite index type with decidable equality. The identity acts on that same matrix space. "
                    + "The positive-count and size conditions used for the cover are hypotheses of the construction theorem."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("is-joint-cover"), DeclarationHandle.Create(Module + ".IsJointCover"),
                H("Positive cover with dominating marginals"), Hand(JointCoverFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A, B and C act on output times input, and H acts on input. The lift is I ⊗ H. The inequalities use positive "
                    + "semidefinite order. The sum over j,k is over all product outcomes. This is the feasible cover in "
                    + "the one-step specialization of Ragini–Sazim's published covering SDP, Appendix A, (A18)–(A28)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("explicit-joint-cover"), DeclarationHandle.Create(Module + ".explicitJointCover"),
                H("Construct a joint cover"), Hand(ExplicitCoverFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive p and q, input density matrices ρ and σ, and families with the corresponding "
                    + "normalization identities and positive effects, take real ε and M satisfying the displayed bounds. "
                    + "The effects and lifted states are positive contractions. Expanding the square of the difference "
                    + "of the two effects gives entry positivity. Completing a positive sandwich with the opposite "
                    + "lifted state gives row and column domination because M bounds the squares of both outcome counts. "
                    + "Summing the entries gives the lift of H."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("compatible-at-of-joint-cover"),
                DeclarationHandle.Create(Module + ".compatibleAt_of_jointCover"),
                H("Convert a cover into actual mixing witnesses"), Hand(CompatibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume positive output dimension, density matrices ρ and σ, the corresponding normalization "
                    + "hypotheses on A and B, and a joint cover C with input matrix H. Taking traces of the input "
                    + "normalization inequalities gives t ≥ 1. Divide the cover by t. If t > 1, divide its two marginal "
                    + "slacks by t − 1 for the two noise testers. If t = 1, the positive slacks vanish, so the cover "
                    + "already has the required marginals at zero weight."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonorthogonal-upper-bound"),
                DeclarationHandle.Create(Module + ".nonorthogonal_upper_bound"),
                H("Strict upper bound from normalization overlap"), Hand(UpperBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume positive d₀, d₁, p and q, input densities ρ and σ, the corresponding normalization "
                    + "hypotheses on A and B, and ρσ ≠ 0. The real trace δ of ρσ lies in (0, 1]. "
                    + "With M = max(p,q)², the choice ε = δ/(M d₀) satisfies the cover bounds. Substituting it "
                    + "in the real trace of H gives the displayed t. The cover-to-compatibility theorem supplies "
                    + "the feasible weight 1 − 1/t, so the same weight bounds the infimum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalization-orthogonal-iff-effectwise"),
                DeclarationHandle.Create(Module + ".normalization_orthogonal_iff_effectwise"),
                H("Normalization and effectwise orthogonality"), Hand(EffectwiseFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Assume positive output dimension, that ρ is an input density matrix, and the positivity and "
                    + "sum hypotheses for A with ρ and B with σ. This is the operator equivalence used in Proposition 12 of Sedlák "
                    + "et al. If the normalization product vanishes, trace monotonicity bounds each positive "
                    + "effect pairing by zero. Zero trace pairing of positive matrices forces their product to vanish. "
                    + "Conversely, summing the zero products gives I ⊗ (ρσ) = 0, and the lift is injective."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Maximal robustness and orthogonality"), Hand(ClaimFormula(definition: true)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive d₀, d₁, p and q, the families A and B are indexed by Fin p and Fin q "
                    + "and act on Fin d₁ × Fin d₀. The input matrices ρ and σ act on Fin d₀. The hypotheses "
                    + "explicitly require both densities, both tester predicates, and the two positivity and normalization "
                    + "conditions HasNormalization(A, ρ) and HasNormalization(B, σ). The displayed conjunction is "
                    + "the conclusion under all these hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Resolve the §V.C converse"), Hand(ClaimFormula(definition: false)), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The result proves claim with the same quantifiers and hypotheses. For nonorthogonal input "
                        + "states, the strict upper bound supplies a feasible noise weight below one half. The "
                        + "zero-perturbation cover gives compatibility at one half for all such tester pairs.")),
                    Paragraph(Text(
                        "For orthogonal input states, any compatible pair has a joint normalization dominating each "
                        + "original state scaled by 1 − λ. Taking traces against the support and kernel projections "
                        + "of ρ gives 1 ≥ 2(1 − λ), so the infimum is at least one half. Proposition 12's "
                        + "effectwise equivalence gives the second conjunct.")),
                    Paragraph(Text(
                        "Ragini and Sazim formulate one-step compatibility using a joint cover in New Journal "
                        + "of Physics (2024), DOI 10.1088/1367-2630/ad93f6. The positive joint family above "
                        + "gives the quantitative estimate and the strict inequality for nonorthogonal inputs."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create(Problem), ResolutionKind.Proved)))));

    private static Formula CoverEntryFormula()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        return Seq(Call("coverEntry", F.Id("p"), F.Id("q"), Varepsilon, F.Id("M"), x, y), Eq,
            Div(x, F.Id("q")), Plus, Div(y, F.Id("p")), Minus, Varepsilon, Par(SymmetrizedProduct(x, y)),
            Plus, Div(Seq(F.Id("M"), Sq(Varepsilon)), Seq(F.Id("p"), F.Id("q"))), F.Id("I"));
    }

    private static Formula JointCoverFormula()
    {
        var j = F.Id("j");
        var k = F.Id("k");
        var pairs = Seq(j, Comma, k);
        var entry = Seq(F.Id("C"), Par(pairs));
        return new Formula.Aligned([
            Seq(Call("IsJointCover", F.Id("A"), F.Id("B"), F.Id("C"), F.Id("H")), Amp, Leftrightarrow,
                Par(Seq(Forall, Sp, pairs, Comma, entry, Geq, D(0))), Land,
                Par(Seq(Sub(Sum, pairs), entry, Eq, Call("liftInput", F.Id("H"))))),
            Seq(Amp, Land, Par(Seq(Forall, Sp, j, Comma, Sub(F.Id("A"), j), Leq, Sub(Sum, k), entry)),
                Land, Par(Seq(Forall, Sp, k, Comma, Sub(F.Id("B"), k), Leq, Sub(Sum, j), entry))),
        ]);
    }

    private static Formula ExplicitCoverFormula() =>
        Seq(D(0), Leq, Varepsilon, Leq, Min, Par(Seq(Inv(F.Id("p")), Comma, Inv(F.Id("q")))),
            Quad, Max, Par(Seq(Sq(F.Id("p")), Comma, Sq(F.Id("q")))), Leq, Sp, F.Id("M"),
            Quad, Longrightarrow, Quad, Call("IsJointCover", F.Id("A"), F.Id("B"), F.Id("C"), F.Id("H")),
            Quad, Sp, F.Id("C"), Par(Seq(F.Id("j"), Comma, F.Id("k"))), Eq,
            Call("coverEntry", F.Id("p"), F.Id("q"), Varepsilon, F.Id("M"),
                Sub(F.Id("A"), F.Id("j")), Sub(F.Id("B"), F.Id("k"))),
            Quad, Sp, F.Id("H"), Eq, Rho, Plus, SigmaLower, Minus, Varepsilon, Par(SymmetrizedProduct(Rho, SigmaLower)),
            Plus, F.Id("M"), Sq(Varepsilon), Sub(F.Id("I"), Sub(F.Id("d"), D(0))));

    private static Formula CompatibilityFormula() =>
        Seq(F.Id("t"), Eq, RealTrace(F.Id("H")), Quad,
            D(1), Leq, Sp, F.Id("t"), Land, Call("TesterCompatibleAt", NoiseWeight(), F.Id("A"), F.Id("B")));

    private static Formula UpperBoundFormula() =>
        Seq(DeltaLower, Eq, RealTrace(Seq(Rho, SigmaLower)), Quad, Sp,
            F.Id("t"), Eq, D(2), Minus,
            Div(Sq(DeltaLower), Seq(Sq(Seq(Max, Par(Seq(F.Id("p"), Comma, F.Id("q"))))), Sub(F.Id("d"), D(0)))),
            Quad, D(1), Leq, Sp, F.Id("t"), Land, Sp, Robustness(), Leq, NoiseWeight(), Land, NoiseWeight(), Lt, Div(D(1), D(2)));

    private static Formula ClaimFormula(bool definition)
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var quantifiers = Seq(Forall, Sp, Sub(F.Id("d"), D(0)), Comma, Sub(F.Id("d"), D(1)),
            Comma, F.Id("p"), Comma, F.Id("q"), Gt, D(0), Comma,
            Quad, Forall, Sp, a, Comma, b, Comma, Rho, Comma, SigmaLower, Comma);
        var assumptions = Seq(Call("IsDensity", Rho), Land, Call("IsDensity", SigmaLower),
            Land, Call("IsTester", a), Land, Call("IsTester", b), Land,
            Call("HasNormalization", a, Rho), Land, Call("HasNormalization", b, SigmaLower));
        return new Formula.Aligned([
            definition ? Seq(F.Id("claim"), Amp, Leftrightarrow, quantifiers) : Seq(Amp, quantifiers),
            Seq(Amp, Par(assumptions)),
            Seq(Amp, Longrightarrow,
                Par(Seq(Robustness(), Eq, Div(D(1), D(2)), Leftrightarrow, NormalizationOrthogonal())),
                Land, Par(EffectwiseFormula())),
        ]);
    }

    private static Formula EffectwiseFormula() =>
        Seq(NormalizationOrthogonal(), Leftrightarrow, Forall, Sp, F.Id("j"), Comma, F.Id("k"), Comma,
            Sub(F.Id("A"), F.Id("j")), Sub(F.Id("B"), F.Id("k")), Eq, D(0));

    private static Formula NormalizationOrthogonal() => Seq(Rho, SigmaLower, Eq, D(0));
    private static Formula NoiseWeight() => Seq(D(1), Minus, Inv(F.Id("t")));
    private static Formula Robustness() =>
        new Formula.Apply(Sub(F.Id("R"), F.Id("t")), [F.Id("A"), F.Id("B")]);
    private static Formula RealTrace(Formula value) => Seq(Re, Call("tr", value));
    private static Formula SymmetrizedProduct(Formula x, Formula y) => Seq(x, y, Plus, y, x);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Inv(Formula value) => new Formula.Power(value, Seq(Minus, D(1)));
    private static Formula Sq(Formula value) => new Formula.Power(value, D(2));
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static StatementSource Hand(Formula formula) => StatementSource.FromAuthor(Disp(formula));
}
