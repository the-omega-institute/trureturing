using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeCalibratedArithmeticBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete native posterior and its rectangle kernel use the same calibration.",
        H("Full native posterior, shared calibration and arithmetic phase"),
        Blocks(
            Paragraph(Text(
                    "For natural M, q and history length s, S is any native support of cardinality q; e is the pair or path "
                    + "experiment and o is a complete native history. The compensation c is rq/(M-q), using the natural difference. "
                    + "Row scores, weights and inclusion probabilities are the original full fixed-size posterior quantities. No "
                    + "reference model replaces the actual posterior.")),
            Paragraph(Text(
                    "Write alpha = log((1+r)/(1-c)), beta = log((1-r)/(1+c)), zzero = k alpha + l beta, and sigmoid(x) = "
                    + "1/(1+exp(-x)). For the complete count law put p(a,b) = referenceParameter M q r (a,b) = sigmoid(a alpha + b "
                    + "beta - log((M-q)/q)); Q_i(a,b) is rowReference S r L i (a,b). Counts and natural cardinalities are embedded "
                    + "into the reals in these formulas.")),
            Paragraph(Text(
                    "For a four-cell rectangle, cell j means nativeCalibrationCells S e o k l j, with j in Fin 4. At a rectangle "
                    + "count t the calibrated mean m(t,x) and variance v(t,x) are calibratedMean and calibratedVariance evaluated "
                    + "on the same outside scores, r, c, total N and margins R,U. Their four coefficients are t, U-t, R-t and "
                    + "N-R-U+t. The checkerboard response Delta(x) is checkerboard r c x.")),
            Paragraph(Text(
                    "The native calibration and posterior-kernel relations are repository-derived. The cited Library notes "
                    + "describe classical Poisson, hypergeometric and small-ball tools and their applicability boundaries.")),
            Describe.Lean(
                DescribeId.Create("reference-likelihood-ratio"),
                DeclarationHandle.Create(Module + "NativeReferenceCalibration.reference_likelihood_ratio"),
                H("Complete signal-to-background reference likelihood ratio"),
                StatementSource.FromAuthor(Formula1()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial")),
                Blocks(
                Paragraph(Text(
                    "For every M, q, L, support S, real r and kappa, assume kappa > 0, r > 0, r <= 1-kappa, c <= 1-kappa and 1 <= "
                    + "L. Choose any signal row i in S and background row j outside S. The reference sums below range over every "
                    + "natural count pair.")),
                Paragraph(Text(
                    "The common exponential factor of the two Poisson masses cancels. Their count-dependent ratio is the original "
                    + "score weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-calibration-mean-variance"),
                DeclarationHandle.Create(Module + "NativeReferenceCalibration.reference_calibration_mean_variance"),
                H("Exact complete reference calibration and variance"),
                StatementSource.FromAuthor(Formula2()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial")),
                Blocks(
                Paragraph(Text(
                    "For every M, q, L, support S, real r and kappa, assume kappa > 0, r > 0, r <= 1-kappa, c <= 1-kappa and 1 <= "
                    + "L. Choose any signal row i in S and background row j outside S. The reference sums below range over every "
                    + "natural count pair.")),
                Paragraph(Text(
                    "In addition assume 1 <= q < M. The first identity is exact mean calibration, not a finite-count "
                    + "approximation. The second identity expresses the complete Bernoulli variance as a signal-row complement sum.")),
                Paragraph(Text(
                    "Countwise calibration follows from the signal-to-background reference ratio. Summation over the complete "
                    + "normalized signal and background Poisson laws gives both identities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-reference-calibration-deviation"),
                DeclarationHandle.Create(Module + "NativeReferenceCalibration.native_reference_calibration_deviation"),
                H("Joint native calibration and variance deviation"),
                StatementSource.FromAuthor(Formula3()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/lecam1960poissonbinomial"), LibraryNoteRef.Create("D5/L/Estimation/grinsteadsnell2006probability")),
                Blocks(
                Paragraph(Text(
                    "Fix 0 < kappa < 1. There exist real A > 0, a natural Mzero >= 1 and real etazero > 0 depending only on "
                    + "kappa. For every M, q, L and r assume Mzero <= M, 1 <= q < M, 0 < r <= 1-kappa, c <= 1-kappa, 1 <= L, L/M <= "
                    + "etazero, and A L^2/M <= 1/2. The same constants work for every true support S, either experiment e, every "
                    + "finite row set I and every admitted weight function g.")),
                Paragraph(Text(
                    "Also assume 6 <= M and L/M <= 1/45. Choose every support S, either experiment e, a signal row i and a "
                    + "background row j, and arbitrary real b,h > 0. Put V = sum over all M rows and all natural count pairs of "
                    + "p(a,b)(1-p(a,b))Q_i(a,b), where the inner summation variables are independent of the deviation threshold b.")),
                Paragraph(Text(
                    "Pzero(o) is the sum over every original row of p at its actual count pair. Dzero(o) is the sum of p(1-p) at "
                    + "those same pairs. Put B = 3q + 8(A L^3/M)q^2 + 10 M^2 exp(-(8 log 4 - 6)L). The constants A, Mzero and "
                    + "etazero are chosen before S,e,i,j,b,h.")),
                Paragraph(Text(
                    "The exact complete reference identities and the full weighted deviation estimate control both observables. A "
                    + "union bound gives their joint deviation probability under the same native law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-calibration-sum"),
                DeclarationHandle.Create(Module + "SharedRectangleCalibration.native_full_calibration_sum"),
                H("One full calibration sum from all native rows"),
                StatementSource.FromAuthor(Formula4()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "For every M,q,s,S,r,e,o,k,l and every real x, let C_j be the cardinality of nativeCalibrationCells S e o k l "
                    + "j. Here m uses N = C_0+C_1+C_2+C_3, R = C_0+C_2, U = C_0+C_1, and outside scores score(q,r,e,o,i)-zzero on "
                    + "exactly the rows whose nativeRowCell is none.")),
                Paragraph(Text(
                    "No positivity or population hypothesis is required for this identity. Partitioning all original rows into "
                    + "the four cells and their outside complement gives the displayed calibration sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-group-zero-centers"),
                DeclarationHandle.Create(Module + "SharedRectangleCalibration.native_group_zero_centers"),
                H("Exact centers of the complete zero-count group"),
                StatementSource.FromAuthor(Formula5()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "For all M,q,s,r,e,o,k,l assume 1 <= q < M, 0 < r < 1, and 0 <= c < 1. Let t be any positive real and i0 any "
                    + "row with counts k and l. Define All as the whole Fin M support, G = nativeCalibrationCells All e o k l 0 and "
                    + "Bzero = (M-q)/q.")),
                Paragraph(Text(
                    "G includes every original row with the displayed counts, regardless of membership in the true support. Equal "
                    + "count scores give equal fixed-size inclusion probabilities and equal calibrated Bernoulli values. The first "
                    + "expression is a group sum, not an average."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-environment-outside-counts"),
                DeclarationHandle.Create(Module + "SharedRectangleCalibration.native_environment_outside_counts"),
                H("Outside counts fixed by the margin rectangle readout"),
                StatementSource.FromAuthor(Formula6()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "Let k,l be arbitrary natural counts and let y,z lie in Fiber S e o, the actual signal-assignment fiber. "
                    + "Equality of the indicated environment readouts is an explicit hypothesis; the histories and all derived "
                    + "counts remain in this same fiber.")),
                Paragraph(Text(
                    "For every M,q,s,S,e,o,k,l assume the nativeMarginRectangleReadout values of y and z agree. For every i in "
                    + "Fin M whose nativeRowCell at z is none, the displayed two count equalities and outside-row membership at y "
                    + "hold. No drift, positivity or density condition is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-environment-mean-variance"),
                DeclarationHandle.Create(Module + "NativeCalibratedArithmeticBridge.native_environment_mean_variance"),
                H("Full mean and variance in one minimal native environment"),
                StatementSource.FromAuthor(Formula7()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "Let k,l be arbitrary natural counts and let y,z lie in Fiber S e o, the actual signal-assignment fiber. "
                    + "Equality of the indicated environment readouts is an explicit hypothesis; the histories and all derived "
                    + "counts remain in this same fiber.")),
                Paragraph(Text(
                    "For every M,q,s,S,r,e,o,k,l assume a finite Sites s e type, equal nativeMinimalRectangleReadout values for y "
                    + "and z, 1 <= q < M, 0 < r < 1 and 0 <= c < 1. The identities hold for every real x.")),
                Paragraph(Text(
                    "V is nativeRectangleRows S e o k l z, N is its cardinality, R and U count its rows whose positive and "
                    + "negative counts equal k and l, respectively, and A is nativeRectangleACount S e o k l y. Outside scores come "
                    + "from z on exactly the rows whose nativeRowCell at z is none. Thus both identities use one fixed outside list "
                    + "and one varying rectangle count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("posterior-phase-iff-parity-band"),
                DeclarationHandle.Create(Module + "NativeCalibratedArithmeticBridge.posterior_phase_iff_parity_band"),
                H("Exact phase-to-parity-band equivalence"),
                StatementSource.FromAuthor(Formula8()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "For every pair of integers ell,t and every real mu,tau, the equivalence holds. There is no positivity "
                    + "assumption on tau and no nonzero assumption on ell.")),
                Paragraph(Text(
                    "Doubling the phase produces a lattice point with the displayed parity. The inverse change of integer "
                    + "variable is justified by that congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-posterior-central-kernel-bound"),
                DeclarationHandle.Create(Module + "NativeCalibratedArithmeticBridge.native_posterior_central_kernel_bound"),
                H("Original posterior phase dominated by one native central kernel"),
                StatementSource.FromAuthor(Formula9()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/siegrist2026hypergeometric"), LibraryNoteRef.Create("D5/L/Estimation/lahirichatterjeemaiti2007hypergeometric"), LibraryNoteRef.Create("D5/L/Estimation/nguyenvu2013smallball"), LibraryNoteRef.Create("D5/L/Estimation/juskevicius2024kolmogorovrogozin")),
                Blocks(
                Paragraph(Text(
                    "There exist absolute real C > 0 and Vzero > 0, chosen before all model data. For every natural M,q,s, "
                    + "support S, real r, experiment e, original history o, and finite Sites s e type assume 1 <= q < M, 0 < r < 1 "
                    + "and 0 <= c < 1. Choose arbitrary natural k,l, anchor z in Fiber S e o, function theta from the reals to the "
                    + "reals, integer ell and real tau,w,D.")),
                Paragraph(Text(
                    "Let All be the full support and BG = nativeCalibrationCells All e o k l 0 minus S. Let V be "
                    + "nativeRectangleRows at z, N = |V|, and R,U its positive and negative count margins. Put nu = UR/N and "
                    + "outside(i) = score(q,r,e,z,i)-zzero on the outside rows. Env is the set of all y in the same "
                    + "signal-assignment fiber with the same nativeMinimalRectangleReadout as z.")),
                Paragraph(Text(
                    "For y in Env set t(y) = nativeRectangleACount S e o k l y. Require Vzero <= D; for every y in Env with "
                    + "|t(y)-nu| <= w require m(t(y),theta(t(y))) = q and D <= v(t(y),theta(t(y))). All calibration and variance "
                    + "hypotheses refer to this same environment and the same theta.")),
                Paragraph(Text(
                    "Q(y) means that some integer a satisfies |ell(1/2-mu0(y))-a| <= tau, where mu0(y) is the sum of the original "
                    + "inclusion probabilities over nativeCalibrationCells All e y k l 0. P(t) means |t-nu| > w or that some "
                    + "integer a satisfies |2 ell((|BG|+t)sigmoid(theta(t))-t/2)-a| <= 2 tau + 2|ell| C(|BG|+nu+w)/D.")),
                Paragraph(Text(
                    "H(N,R,U,t) is zero when t > U and otherwise equals choose(R,t) choose(N-R,U-t)/choose(N,U), with the natural "
                    + "differences of the Lean definition. The numerator and denominator on the left are actual "
                    + "conditionalFiberMass values. Their quotient uses the totalized real division of the Lean statement; no extra "
                    + "positive-environment-mass assumption is imposed.")),
                Paragraph(Text(
                    "The full-row posterior approximation first reduces the original phase to a central lattice event or a count "
                    + "tail. The conditional native rectangle law then transfers that single event to its hypergeometric count "
                    + "kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("balanced-shared-curve"),
                DeclarationHandle.Create(Module + "NativeCalibratedArithmeticBridge.balanced_shared_curve"),
                H("One differentiable calibrated curve on the balanced count window"),
                StatementSource.FromAuthor(Formula10()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "Let iota be any finite type, outside any real-valued function on iota, and r, epsilon, N,R,U,q,delta,w "
                    + "arbitrary reals. Assume N > 0, q > 0, q < |iota|+N, delta > 0, w <= delta^2 N/2, delta N <= R <= (1-delta)N "
                    + "and delta N <= U <= (1-delta)N. Neither r nor epsilon is constrained by this theorem, and no lower bound on "
                    + "w is added.")),
                Paragraph(Text(
                    "Here m and v use outside,r,epsilon,N,R,U. Delta is checkerboard r epsilon. The displayed derivative means "
                    + "HasDerivAt theta of -Delta(theta(t))/v(t,theta(t)) at t. LocalCalibration(t) means m(u,theta(u)) = q for "
                    + "every u in some neighborhood of t, equivalently eventually for u in the neighborhood filter at t.")),
                Paragraph(Text(
                    "The margin bounds keep all four real cell coefficients nonnegative on an open interval around the specified "
                    + "window. The shared calibration curve applies on that interval, and its positive variance controls the "
                    + "implicit derivative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-outside-rectangle-card"),
                DeclarationHandle.Create(Module + "NativeCalibratedArithmeticBridge.native_outside_rectangle_card"),
                H("Rectangle and outside rows exhaust the original population"),
                StatementSource.FromAuthor(Formula11()),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text(
                    "For every M,q,s,S,e,o,k,l and every z in Fiber S e o, the displayed cardinality identity holds. There are no "
                    + "additional population, drift or positivity assumptions.")),
                Paragraph(Text(
                    "The outside subtype and nativeRectangleRows partition all original rows. Consequently the calibration root "
                    + "range uses the original population M."))),
                DescribeRole.Theorem)
        )));

    private static Formula Formula1() => Disp(Seq(
            Forall, Open, F.Id("a"), Comma, F.Id("b"), Close, InMacro, Mathbb, Grp(F.Id("N")), Caret, D(2), Comma, Quad,
            F.Id("Q"), Underscore, F.Id("i"), Open, F.Id("a"), Comma, F.Id("b"), Close, Eq, Exp, Open, F.Id("a"), Alpha, Plus,
            F.Id("b"), Beta, Close, F.Id("Q"), Underscore, F.Id("j"), Open, F.Id("a"), Comma, F.Id("b"), Close));

    private static Formula Formula2() => Disp(Seq(
            F.Id("q"), Sum, Underscore, Grp(F.Id("a"), Comma, F.Id("b"), Ge, D(0)), F.Id("p"), Open, F.Id("a"), Comma,
            F.Id("b"), Close, F.Id("Q"), Underscore, F.Id("i"), Open, F.Id("a"), Comma, F.Id("b"), Close, Plus, Open,
            F.Id("M"), Minus, F.Id("q"), Close, Sum, Underscore, Grp(F.Id("a"), Comma, F.Id("b"), Ge, D(0)), F.Id("p"), Open,
            F.Id("a"), Comma, F.Id("b"), Close, F.Id("Q"), Underscore, F.Id("j"), Open, F.Id("a"), Comma, F.Id("b"), Close, Eq,
            F.Id("q"), Quad, Land, Quad, F.Id("q"), Sum, Underscore, Grp(F.Id("a"), Comma, F.Id("b"), Ge, D(0)), F.Id("p"),
            Open, F.Id("a"), Comma, F.Id("b"), Close, Open, D(1), Minus, F.Id("p"), Open, F.Id("a"), Comma, F.Id("b"), Close,
            Close, F.Id("Q"), Underscore, F.Id("i"), Open, F.Id("a"), Comma, F.Id("b"), Close, Plus, Open, F.Id("M"), Minus,
            F.Id("q"), Close, Sum, Underscore, Grp(F.Id("a"), Comma, F.Id("b"), Ge, D(0)), F.Id("p"), Open, F.Id("a"), Comma,
            F.Id("b"), Close, Open, D(1), Minus, F.Id("p"), Open, F.Id("a"), Comma, F.Id("b"), Close, Close, F.Id("Q"),
            Underscore, F.Id("j"), Open, F.Id("a"), Comma, F.Id("b"), Close, Eq, F.Id("q"), Sum, Underscore,
            Grp(F.Id("a"), Comma, F.Id("b"), Ge, D(0)), Open, D(1), Minus, F.Id("p"), Open, F.Id("a"), Comma, F.Id("b"), Close,
            Close, F.Id("Q"), Underscore, F.Id("i"), Open, F.Id("a"), Comma, F.Id("b"), Close));

    private static Formula Formula3() => Disp(Seq(
            D(0), Le, F.Id("V"), Le, F.Id("q"), Quad, Land, Quad, F.Id("P"), OpenBracket, Bar, F.Id("Pzero"), Minus, F.Id("q"),
            Bar, Gt, F.Id("b"), Lor, Bar, F.Id("Dzero"), Minus, F.Id("V"), Bar, Gt, F.Id("h"), CloseBracket, Le, Frac,
            Grp(F.Id("B")), Grp(F.Id("b"), Caret, D(2)), Plus, Frac, Grp(F.Id("B")), Grp(F.Id("h"), Caret, D(2))));

    private static Formula Formula4() => Disp(Seq(
            Sum, Underscore, Grp(F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close), Mathrm,
            Grp(F.Id("sigmoid")), Open, F.Id("x"), Plus, Mathrm, Grp(F.Id("score")), Open, F.Id("i"), Close, Minus,
            F.Id("zzero"), Close, Eq, F.Id("m"), Open, F.Id("C"), Underscore, D(0), Comma, F.Id("x"), Close));

    private static Formula Formula5() => Disp(Seq(
            Sum, Underscore, Grp(F.Id("i"), InMacro, F.Id("G")), Mathrm, Grp(F.Id("inclusion")), Open, F.Id("i"), Close, Eq,
            Bar, F.Id("G"), Bar, Mathrm, Grp(F.Id("inclusion")), Open, F.Id("i"), Underscore, D(0), Close, Quad, Land, Quad,
            Sum, Underscore, Grp(F.Id("i"), InMacro, F.Id("G")), Frac,
            Grp(F.Id("t"), Mathrm, Grp(F.Id("weight")), Open, F.Id("i"), Close),
            Grp(F.Id("Bzero"), Plus, F.Id("t"), Mathrm, Grp(F.Id("weight")), Open, F.Id("i"), Close), Eq, Bar, F.Id("G"), Bar,
            Mathrm, Grp(F.Id("sigmoid")), Open, F.Id("zzero"), Minus, Log, F.Id("Bzero"), Plus, Log, F.Id("t"), Close));

    private static Formula Formula6() => Disp(Seq(
            F.Id("nplus"), Open, F.Id("i"), Comma, F.Id("y"), Close, Eq, F.Id("nplus"), Open, F.Id("i"), Comma, F.Id("z"),
            Close, Quad, Land, Quad, F.Id("nminus"), Open, F.Id("i"), Comma, F.Id("y"), Close, Eq, F.Id("nminus"), Open,
            F.Id("i"), Comma, F.Id("z"), Close, Quad, Land, Quad, Mathrm, Grp(F.Id("nativeRowCell")), Open, F.Id("y"), Comma,
            F.Id("i"), Close, Eq, Mathrm, Grp(F.Id("none"))));

    private static Formula Formula7() => Disp(Seq(
            Sum, Underscore, Grp(F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close), Mathrm,
            Grp(F.Id("sigmoid")), Open, F.Id("x"), Plus, Mathrm, Grp(F.Id("score")), Open, F.Id("y"), Comma, F.Id("i"), Close,
            Minus, F.Id("zzero"), Close, Eq, F.Id("m"), Open, F.Id("A"), Comma, F.Id("x"), Close, Quad, Land, Quad, Sum,
            Underscore, Grp(F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close), Mathrm,
            Grp(F.Id("sigmoid")), Open, F.Id("x"), Plus, Mathrm, Grp(F.Id("score")), Open, F.Id("y"), Comma, F.Id("i"), Close,
            Minus, F.Id("zzero"), Close, Open, D(1), Minus, Mathrm, Grp(F.Id("sigmoid")), Open, F.Id("x"), Plus, Mathrm,
            Grp(F.Id("score")), Open, F.Id("y"), Comma, F.Id("i"), Close, Minus, F.Id("zzero"), Close, Close, Eq, F.Id("v"),
            Open, F.Id("A"), Comma, F.Id("x"), Close));

    private static Formula Formula8() => Disp(Seq(
            Open, Exists, F.Id("a"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Bar, Ell, Open, D(1), Slash, D(2), Minus, Mu,
            Close, Minus, F.Id("a"), Bar, Le, Tau, Close, Iff, Open, Exists, F.Id("z"), InMacro, Mathbb, Grp(F.Id("Z")), Comma,
            F.Id("z"), Equiv, Ell, Open, D(1), Minus, F.Id("t"), Close, Pmod, D(2), Land, Bar, D(2), Ell, Open, Mu, Minus,
            F.Id("t"), Slash, D(2), Close, Minus, F.Id("z"), Bar, Le, D(2), Tau, Close));

    private static Formula Formula9() => Disp(Seq(
            Frac, Grp(Mathrm, Grp(F.Id("conditionalFiberMass")), Open, F.Id("EnvQ"), Close),
            Grp(Mathrm, Grp(F.Id("conditionalFiberMass")), Open, F.Id("Env"), Close), Le, Sum, Underscore,
            Grp(F.Id("t"), Eq, D(0)), Caret, Grp(F.Id("U")), Grp(Mathrm, Grp(F.Id("indicator"))), Underscore,
            Grp(F.Id("P"), Open, F.Id("t"), Close), F.Id("H"), Open, F.Id("N"), Comma, F.Id("R"), Comma, F.Id("U"), Comma,
            F.Id("t"), Close));

    private static Formula Formula10() => Disp(Seq(
            Exists, Theta, Colon, Mathbb, Grp(F.Id("R")), To, Mathbb, Grp(F.Id("R")), Comma, Forall, F.Id("t"), InMacro,
            Mathbb, Grp(F.Id("R")), Comma, Bar, F.Id("t"), Minus, F.Id("UR"), Slash, F.Id("N"), Bar, Le, F.Id("w"), Rightarrow,
            Open, F.Id("m"), Open, F.Id("t"), Comma, Theta, Open, F.Id("t"), Close, Close, Eq, F.Id("q"), Land, Theta, Caret,
            Grp(Apos), Open, F.Id("t"), Close, Eq, Minus, Delta, Open, Theta, Open, F.Id("t"), Close, Close, Slash, F.Id("v"),
            Open, F.Id("t"), Comma, Theta, Open, F.Id("t"), Close, Close, Land, Mathrm, Grp(F.Id("LocalCalibration")), Open,
            F.Id("t"), Close, Land, F.Id("v"), Open, F.Id("t"), Comma, Theta, Open, F.Id("t"), Close, Close, Gt, D(0), Close));

    private static Formula Formula11() => Disp(Seq(
            Bar, OpenBrace, F.Id("i"), InMacro, Mathrm, Grp(F.Id("Fin")), Open, F.Id("M"), Close, Colon, Mathrm,
            Grp(F.Id("nativeRowCell")), Open, F.Id("z"), Comma, F.Id("i"), Close, Eq, Mathrm, Grp(F.Id("none")), CloseBrace,
            Bar, Plus, Bar, Mathrm, Grp(F.Id("nativeRectangleRows")), Open, F.Id("z"), Close, Bar, Eq, F.Id("M")));

}
