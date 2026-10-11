using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class GaussianFrequencyKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel.";
    private static Formula I(string n) => F.Id(n);
    private static Formula A(string n, params Formula[] xs) => Call(n, xs);
    private static Formula R => I("Real");
    private static Formula Pair => A("Prod", R, R);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Add(Formula x, Formula y) => F.Seq(x, F.Plus, y);
    private static Formula Sub(Formula x, Formula y) => F.Seq(x, F.Minus, y);
    private static Formula Smul(Formula x, Formula y) => A("smul", x, y);
    private static Formula All(string n, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(n), type)], body);
    private static Formula Exists(string n, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(n), type)], body);
    private static Formula Lam(string n, Formula type, Formula body) =>
        F.Seq(F.Open, I(n), F.Colon, type, F.Mapsto, F.Sp, body, F.Close);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula App(Formula f, Formula x) => A("apply", f, x);
    private static Formula Norm(Formula x) => A("norm", x);
    private static Formula Integral(Formula f, Formula mu) => A("integral", f, mu);
    private static Formula Mu => A("spatialMeasure", I("c"), I("kappa"));
    private static Formula Mass => A("spatialMass", I("c"), I("kappa"));
    private static Formula Prod => A("prod", Mu, Mu);
    private static Formula HSpace => A("Lp", R, F.D(2), Mu);
    private static Formula RSpace => A("Lp", R, F.D(2), I("P"));
    private static Formula Omega => Div(A("pi"), F.D(2));
    private static Formula Rho(Formula x) => Multiply(I("c"), A("exp", Div(
        F.Seq(F.Minus, Multiply(I("kappa"), Pow(x, 2))), F.D(2))));
    private static Formula Diff => F.Seq(F.Open, Sub(A("fst", I("z")), A("snd", I("z"))), F.Close);
    private static Formula Gamma => Integral(Lam("x", R, Rho(I("x"))), I("volume"));
    private static Formula Q => A("squareDifference", I("c"), I("kappa"), I("hc"), I("hkappa"));
    private static Formula D(Formula v) => A("gaussianFrequency", I("c"), I("kappa"), I("hc"), I("hkappa"), v);
    private static Formula J(Formula v) => A("quotientFrequency", I("c"), I("kappa"), I("hc"), I("hkappa"), v);
    private static Formula Z(Formula v) => A("quadraticFrequency", I("c"), I("kappa"), I("hc"), I("hkappa"), I("P"), I("W"), I("hW"), v);
    private static Formula I2 => A("secondIntegral", Mu, I("P"), I("W"), I("hW"));
    private static Formula ScalarBound => Div(Multiply(Multiply(A("sqrt", F.D(3)), Pow(Omega, 2)), Mass), I("kappa"));
    private static Formula BStar => Add(Add(F.D(1), Multiply(F.D(2), A("eulerMascheroniConstant"))), Multiply(F.D(2), I("D")));
    private static Formula HS => A("regularKernel", I("c"), I("kappa"), I("hc"), I("hkappa"), I("D"), I("s"));
    private static Formula SpatialPrimitive => A("intervalIntegral", Lam("v", R, Div(Sub(
        A("cos", Multiply(Multiply(Omega, I("v")), Diff)), F.D(1)), I("v"))), F.D(0), A("exp", I("s")), I("volume"));
    private static Formula CiRemainder => Lam("z", Pair, Multiply(F.D(2), A("cosineIntegral",
        Multiply(Multiply(Omega, A("exp", I("s"))), A("abs", Diff)))));
    private static Formula DifferenceFormula => A("AEEq", A("coeFn", A("val", Sub(HS, I("H")))), CiRemainder, Prod);
    private static Formula SingularFormula => A("AEEq", A("coeFn", A("val", I("H"))),
        Lam("z", Pair, Sub(Add(F.D(1), Multiply(F.D(2), I("D"))), Multiply(F.D(2), A("log", Multiply(Omega, A("abs", Diff)))))), Prod);
    private static Formula QuadraticIntegral => SetIntegral(Lam("v", R, Smul(A("inv", I("v")), Z(I("v")))));
    private static Formula RemainderNoiseFormula => All("D", R, All("H", A("symmetricKernel", Mu),
        Eq(App(I2, Sub(HS, I("H"))), Sub(Add(
            Smul(Add(BStar, Multiply(F.D(2), I("s"))), A("centeredSquare", Mu, I("P"), I("W"), I("hW"), A("oneVector", Mu))),
            Smul(F.D(2), QuadraticIntegral)), App(I2, I("H"))))));
    private static Formula Window => A("Icc", F.D(0), A("exp", I("s")));
    private static Formula SetIntegral(Formula f) => A("setIntegral", f, Window, I("volume"));
    private static Formula Params(Formula body, bool positive = true) => F.Disp(All("c", R,
        All("kappa", R, positive ? All("hc", Le(F.D(0), I("c")),
        All("hkappa", Lt(F.D(0), I("kappa")), body)) : body)));
    private static Formula Noise(Formula body) => Params(All("Omega", I("Type"),
        All("SigmaOmega", A("MeasurableSpace", I("Omega")),
        All("P", A("Measure", I("Omega")), All("hprob", A("IsProbabilityMeasure", I("P")),
        All("W", A("LinearIsometry", R, HSpace, RSpace),
        All("hW", All("f", HSpace, A("HasLaw", A("coeFn", App(I("W"), I("f"))),
            A("gaussianReal", F.D(0), A("toNNReal", Pow(Norm(I("f")), 2))), I("P"))), body)))))));
    private static Formula NoiseSquare(string vector, Formula v) => Pow(
        A("evaluation", App(I("W"), A(vector, Mu, v)), I("omega")), 2);
    private static Formula RawNoise(Formula v) => Lam("omega", I("Omega"), Sub(
        Add(NoiseSquare("cosineVector", v), NoiseSquare("sineVector", v)), Pow(
        A("evaluation", App(I("W"), A("oneVector", Mu)), I("omega")), 2)));
    private static Formula Center(string vector, Formula v) => A("centeredSquare", Mu, I("P"), I("W"), I("hW"), A(vector, Mu, v));
    private static DocumentBlock Entry(string name, string title, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create("gf-" + name.ToLowerInvariant().Replace('_', '-')),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(statement),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
        Blocks(Paragraph(Text(prose))), name is "regularKernel" or "spatialMeasure" or "spatialMass" or "squareDifference" or "gaussianFrequency" or "quotientFrequency" or "quadraticFrequency" ? DescribeRole.Definition : DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Gaussian density controls the zero-frequency quotient and the logarithmic singular H in actual symmetric product L2.",
        H("Gaussian frequency integration"), Blocks(
        Entry("spatialMeasure", "Actual weighted measure", Params(Eq(Mu, A("withDensity", I("volume"),
            Lam("x", R, A("ofReal", Rho(I("x")))))), false),
            "For arbitrary real c and kappa, spatialMeasure is the Lebesgue measure with density ofReal(c exp(-kappa x^2/2)). Positive kappa and nonnegative c are required only by the subsequent estimates."),
        Entry("spatialMass", "Gaussian normalization constant", Params(Eq(Mass,
            Multiply(I("c"), A("sqrt", Div(Multiply(F.D(2), A("pi")), I("kappa"))))), false),
            "The mass expression retains the unnormalized coefficient c."),
        Entry("spatialMeasure_normalized", "Density normalization", Params(Eq(Mu,
            Smul(A("ofReal", Mass), A("gaussianReal", F.D(0), A("toNNReal", Div(F.D(1), I("kappa"))))))),
            "For c nonnegative and kappa positive, the actual weighted measure is its mass times the centered Gaussian probability measure with variance 1/kappa. This is an equality of measures derived from their densities, including c=0."),
        Entry("spatialMass_eq_integral", "Original spatial mass", Params(Eq(Mass, Gamma)),
            "The normalization constant equals the integral of the original real density. Thus gamma is the actual unnormalized mass, rather than an imposed probability normalization."),
        Entry("spatialMeasure_finite", "Finite Gaussian weight", Params(A("IsFiniteMeasure", Mu)),
            "The density normalization supplies finiteness for every nonnegative c and positive kappa."),
        Entry("gaussian_difference_law", "Product-coordinate difference law", F.Disp(All("v", I("NNReal"), Eq(
            A("map", A("prod", A("gaussianReal", F.D(0), I("v")), A("gaussianReal", F.D(0), I("v"))), Lam("z", Pair, Diff)),
            A("gaussianReal", F.D(0), Add(I("v"), I("v")))))),
            "Independent coordinates of the actual Gaussian product measure have centered difference law with variance 2v. The pinned Gaussian convolution and map theorems supply this statement, including v=0."),
        Entry("gaussian_fourth", "Reused scalar fourth moment", F.Disp(All("v", I("NNReal"), Eq(
            Integral(Lam("x", R, Pow(I("x"), 4)), A("gaussianReal", F.D(0), I("v"))), Multiply(F.D(3), Pow(A("coe", I("v")), 2))))),
            "The scalar fourth moment is 3v^2, using centralMoment_two_mul in its existing owner. Zero variance is included."),
        Entry("spatial_difference_fourth", "Exact fourth spatial difference moment", Params(Eq(
            Integral(Lam("z", Pair, Pow(Diff, 4)), Prod), Div(Multiply(F.D(1,2), Pow(Gamma, 2)), Pow(I("kappa"), 2)))),
            "The actual product-measure integral of (x-y)^4 is 12 gamma^2/kappa^2. Density normalization, the product-coordinate difference law and the existing scalar moment determine every constant."),
        Entry("spatial_difference_fourth_integrable", "Fourth difference integrability", Params(A("Integrable", Lam("z", Pair, Pow(Diff, 4)), Prod)),
            "Gaussian finite-moment integrability transports through the actual difference map and finite scaling of each coordinate measure."),
        Entry("squareDifference", "Actual square-difference class", Params(And(A("HasType", Q, A("Lp", R, F.D(2), Prod)), Eq(Q, A("toLp", A("memLpOfIntegrableSquare", A("spatialDifferenceFourthIntegrable", I("c"), I("kappa"), I("hc"), I("hkappa"))), Lam("z", Pair, Pow(Diff, 2)))))),
            "This is the toLp class of (x-y)^2, with its membership witness obtained from fourth difference integrability."),
        Entry("squareDifference_coe", "Square-difference representative", Params(A("AEEq", A("coeFn", Q), Lam("z", Pair, Pow(Diff, 2)), Prod)),
            "The L2 class has the displayed actual product-measure representative."),
        Entry("squareDifference_norm", "Exact dominating class norm", Params(Eq(Norm(Q), Div(
            Multiply(Multiply(F.D(2), A("sqrt", F.D(3))), Mass), I("kappa")))),
            "The fourth difference integral gives the norm 2 sqrt(3) gamma/kappa, with no positivity-of-mass assumption."),
        Entry("gaussianFrequency", "Original frequency kernel", Params(All("v", R, Eq(D(I("v")), A("val", A("frequencyKernel", Mu, I("v")))))),
            "This is the existing frequencyKernel, viewed in the actual symmetric L2 subspace using the derived finite-measure instance. No kernel or noise is replaced."),
        Entry("gaussianFrequency_coe", "Cosine-difference representative", Params(All("v", R, A("AEEq", A("coeFn", A("val", D(I("v")))), Lam("z", Pair,
            Sub(A("cos", Multiply(Multiply(Omega, I("v")), Diff)), F.D(1))), Prod))),
            "For every real frequency v, the representative is cos((pi/2)v(x-y))-1."),
        Entry("frequency_norm_bound", "Quadratic zero-frequency bound", Params(All("v", R, Le(Norm(D(I("v"))), Multiply(ScalarBound, Pow(I("v"), 2))))),
            "The global cosine remainder inequality and exact square-difference norm give ||D_v|| <= sqrt(3)(pi/2)^2 gamma v^2/kappa for every real v, including zero."),
        Entry("frequency_lipschitz", "Global frequency regularity", Params(Exists("K", I("NNReal"),
            A("LipschitzWith", I("K"), Lam("v", R, D(I("v")))))),
            "There is a finite nonnegative Lipschitz constant for the actual Gaussian frequency kernel on the whole real line. The proof uses the same cosine bound and dominating L2 class 1+(x-y)^2 as frequency continuity, whose proof consumes this helper. The helper adds no mathematical content credit. Composition with the original second integral gives the regularity needed by the existing jointly measurable L2 version theorem, on the original probability space."),
        Entry("frequency_continuous", "Frequency L2 continuity", Params(A("Continuous", Lam("v", R, D(I("v"))))),
            "The consumed global Lipschitz helper supplies continuity in the actual symmetric product L2 space."),
        Entry("quotientFrequency", "Zero-inclusive quotient", Params(All("v", R, Eq(J(I("v")), Smul(A("inv", I("v")), D(I("v")))))),
            "Real inverse assigns zero at zero, so J_v=v^-1 D_v has J_0=0 and the original D_v/v representative elsewhere."),
        Entry("quotientFrequency_norm", "Linear quotient bound", Params(All("v", R, Le(Norm(J(I("v"))), Multiply(ScalarBound, A("abs", I("v")))))),
            "Cancellation of one frequency factor gives ||J_v|| <= sqrt(3)(pi/2)^2 gamma |v|/kappa. The zero case is proved separately."),
        Entry("quotientFrequency_continuous", "Continuity at the boundary", Params(A("Continuous", Lam("v", R, J(I("v"))))),
            "Away from zero, continuity follows from inverse and scalar multiplication. At zero, the linear norm bound squeezes J_v to J_0=0."),
        Entry("quotientFrequency_integrable", "Every original finite window", Params(All("s", R, A("IntegrableOn", Lam("v", R, J(I("v"))), Window, I("volume")))),
            "Continuity on the compact closed interval [0,exp(s)] supplies Bochner integrability for every real s. The boundary is included."),
        Entry("frequency_integral_coe", "Actual spatial integral representative", Params(All("s", R,
            A("AEEq", A("coeFn", A("val", SetIntegral(Lam("v", R, J(I("v")))))), Lam("z", Pair, SpatialPrimitive), Prod))),
            "For each real s, the symmetric L2 Bochner integral on [0,exp(s)] has the almost-everywhere representative obtained by integrating the actual cosine quotient in frequency. The continuous L2 primitive and its jointly measurable spatial quotient supply product integrability and Fubini."),
        Entry("regularKernel", "Original finite-frequency kernel", Params(All("D", R, All("s", R, Eq(HS,
            Add(Smul(Add(BStar, Multiply(F.D(2), I("s"))), A("diagonalKernel", Mu, A("oneVector", Mu))),
                Smul(F.D(2), SetIntegral(Lam("v", R, J(I("v")))))))))),
            "The original H_s is constructed in the actual symmetric product L2 space. Its constant coefficient is b_*+2s, where b_*=1+2 Euler+2D, and its frequency integral includes the zero endpoint."),
        Entry("regularKernel_difference", "Off-diagonal Ci identity", Params(All("D", R, All("s", R,
            All("H", A("symmetricKernel", Mu), All("hH", SingularFormula, DifferenceFormula))))),
            "For any H with the original logarithmic representative, H_s-H has representative 2Ci((pi/2)exp(s)|x-y|). The actual Gaussian density gives a null spatial diagonal, including c=0. Cosine evenness, positive scaling and the positive Ci/Euler normalization identify the spatial primitive; the desired kernel identity is a conclusion."),
        Entry("quadraticFrequency", "Actual same-W quadratic frequency", Noise(All("v", R, Eq(Z(I("v")), Sub(
            Add(Center("cosineVector", I("v")), Center("sineVector", I("v"))), A("centeredSquare", Mu, I("P"), I("W"), I("hW"), A("oneVector", Mu)))))),
            "For one fixed original isometry W and its centered Gaussian marginal laws on P, the quadratic class is the sum of the centered cosine and sine squares minus the centered constant square."),
        Entry("quadraticFrequency_representation", "Exact same-noise identification", Noise(All("v", R, And(
            Eq(App(I2, D(I("v"))), Z(I("v"))), A("AEEq", A("coeFn", Z(I("v"))), RawNoise(I("v")), I("P"))))),
            "The continuous second integral agrees with the finite construction. Trigonometric energy cancels the centering terms, so the displayed representative is |F(v)|^2-Y^2 for the same W and P."),
        Entry("frequency_integral_sameNoise", "Bochner commutation and centered remainder", Noise(All("s", R, And(
            A("IntegrableOn", Lam("v", R, Smul(A("inv", I("v")), Z(I("v")))), Window, I("volume")),
            And(Eq(App(I2, SetIntegral(Lam("v", R, J(I("v"))))), QuadraticIntegral), RemainderNoiseFormula)))),
            "The original second integral commutes with the integrable frequency quotient on every finite window. For every D and symmetric H, its image of H_s-H is (b_*+2s) times the centered original Y square, plus twice the same-W quadratic quotient integral, minus I2(H). This is an equality of actual L2(P) classes. Identifying the selected original R and E processes and their common paths requires the corresponding process version identification."),
        Entry("log_square_bound", "Two-sided logarithmic control", F.Disp(All("x", R, All("hx", Lt(F.D(0), I("x")),
            Le(Pow(A("log", I("x")), 2), Add(Multiply(F.Seq(F.D(1), F.D(6)), A("rpow", I("x"), Div(F.Seq(F.Minus, F.D(1)), F.D(2)))), Pow(I("x"), 2)))))),
            "For every positive x, log(x)^2 <= 16 x^(-1/2)+x^2. Below one, the reciprocal power bound controls the logarithmic singularity; above one, log(x) <= x controls the tail. This estimate is consumed by Gaussian logarithmic integrability."),
        Entry("log_square_gaussian_integrable", "Gaussian integrability at the singularity", F.Disp(All("b", R, All("hb", Lt(F.D(0), I("b")),
            A("Integrable", Lam("x", R, Multiply(Pow(A("log", A("abs", I("x"))), 2), A("exp", F.Seq(F.Minus, Multiply(I("b"), Pow(I("x"), 2)))))), I("volume"))))),
            "The actual function log(|x|)^2 exp(-b x^2) is Lebesgue integrable for every b>0. The previous bound is dominated by the pinned Gaussian power integrals with exponents -1/2 and 2 on the positive half-line; reflection covers the negative half-line. The assigned value at zero has no integral effect."),
        Entry("gaussian_log_square_integrable", "Logarithmic moment of the actual Gaussian law", F.Disp(All("v", I("NNReal"), All("hv", A("Not", Eq(I("v"), F.D(0))),
            A("Integrable", Lam("x", R, Pow(A("log", A("abs", I("x"))), 2)), A("gaussianReal", F.D(0), I("v")))))),
            "For every nonzero nonnegative variance v, log(|x|)^2 is integrable under gaussianReal(0,v). The Gaussian density identity directly consumes the proved weighted Lebesgue integrability. No logarithmic moment premise is supplied."),
        Entry("singularKernel_exists", "Singular H and its actual Ci remainder", Params(All("D", R,
            Exists("H", A("symmetricKernel", Mu), And(SingularFormula, All("s", R, DifferenceFormula))))),
            "For every real D, nonnegative c and positive kappa, one H in the actual symmetric product L2 space has representative 1+2D-2 log((pi/2)|x-y|), and for every real s its difference from the constructed H_s has the Ci representative. Apply D=D_w for the original kernel. The Gaussian logarithmic moment and unnormalized mass include c=0; the spatial diagonal is null. This assertion gives the spatial kernel and all its fixed-time differences. It does not assert a common pointwise W version or a process limit."))));
}
