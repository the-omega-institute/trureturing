using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class GeneralDyneSteadyStateOptimalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/GeneralDyneSteadyStateOptimality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/kuaserafinigenoni2025daemonic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The aligned pure general-dyne measurement attains the smallest stationary covariance determinant for a stable thermal optical parametric oscillator, among all physical general-dyne measurements and physical stationary solutions.",
        H("Global steady-state optimality of aligned general-dyne monitoring"),
        Blocks(
            Node("drift", "OPO drift", "driftA", DriftFormula(),
                "Section VI, following Eq. (57), gives the diagonal drift. The symbols kappa and chi denote the real damping and pump parameters.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coupling", "Passive system-bath coupling", "coupling", CouplingFormula(),
                "In the physical q,p coordinates, Omega is the displayed real matrix. The coupling C = sqrt(kappa) Omega produces the drift damping and diffusion following Eq. (57), and the unrotated aligned measurement of Eq. (66).",
                AssessedProvenance.FromLiterature(Source)),
            Node("e", "Correlated diffusion coefficient", "eMat", EFormula(),
                "The text following Eq. (25) defines E = Omega C sigmaIn times the inverse square root of sigmaIn plus M. Here sigmaIn is nu times the identity, M is the measurement covariance, and CFC.sqrt is applied to the inverse matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Node("b", "Monitoring coefficient", "bMat", BFormula(),
                "The text following Eq. (22) defines B = C Omega times the same inverse square root. The finite covariance domain includes arbitrary phases, squeezing and measurement impurity.",
                AssessedProvenance.FromLiterature(Source)),
            Node("steady", "The stationary covariance equation", "steadyEq", SteadyFormula(),
                "Equation (55) sets the conditional Riccati derivative to zero. S denotes the conditional covariance; diffusion is kappa times nu times the identity. Matrix.transpose is the ordinary real transpose. The equation is stated before any dimensionless reduction.",
                AssessedProvenance.FromLiterature(Source)),
            Node("value", "The exact optimal symplectic eigenvalue", "vStar", ValueFormula(),
                "For 0 <= r < 1 and nu >= 1, this is the positive root of v squared minus (nu minus one) times sqrt(1 minus r squared) times v minus nu. The real square roots are total functions; the theorem uses the stable thermal regime.",
                AssessedProvenance.FromRepo(Source)),
            Node("measurement", "The aligned pure measurement", "optMeas", MeasurementFormula(),
                "Page 12, Section VI: As regards the optimization over all the generaldyne measurement, one proves that if one fixes the measurement phase to zero, ϑ_m = 0, then the conditional steady-state purity, and as a consequence the daemonic ergotropy is maximized for the general-dyne parameter z_m,opt = (1 − χ̃)/(1 + χ̃). (66) The displayed matrix is diag(z_m,opt, 1/z_m,opt), with r = chi tilde.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The global optimality conjecture", "claim", ClaimFormula(),
                "Page 12, Section VI after Eq. (66): We have also numerically verified that non-zero phases ϑ_m lead to worse result, and we can thus conjecture that this fully characterizes the optimal steady-state general-dyne monitoring. The real parameters kappa, chi and nth are κ, χ and n_th; nu = 2 nth + 1 and r = 2 chi / kappa. The matrices M and S represent σ_m and σ. IsGaussianMeasurementCov is the existing GaussianThermometryJointMeasurementRefutation predicate at m = 1: symmetry and S + i Omega positive semidefinite. The first conjunct bounds every physical stationary solution for every physical measurement; the second gives a physical stationary solution at the aligned measurement with equality. No uniqueness of the minimizing measurement is asserted.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("general-dyne-physical-forward"), DeclarationHandle.Create(Prefix + "physical_forward"),
                H("Physical one-mode covariances are positive definite"),
                StatementSource.FromAuthor(Disp(All("M", Matrices(), Implies(
                    Seq(Q("D5", "S3", "Estimation", "GaussianThermometryJointMeasurementRefutation", "IsGaussianMeasurementCov"),
                        Sp, Parenthesized(Seq(X("m"), Sp, Colon, Eq, Sp, D(1))), Sp, Parenthesized(X("M"))),
                    And(App(Q("Matrix", "PosDef"), X("M")), AtMost(D(1), App(Q("Matrix", "det"), X("M")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A real two-by-two covariance satisfying IsGaussianMeasurementCov at m = 1 is positive definite and has determinant at least one. The stationary covariance lower bound uses these properties through physical_iff; GaussianAtemporalityEntanglement uses positive definiteness to invert both local covariance blocks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("general-dyne-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The aligned measurement achieves the global optimum"),
                StatementSource.FromAuthor(Disp(ClaimBodyFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write Q = (nu I + M) inverse, V = S minus nu I, D0 = diag(1+r, 1-r), and R = nu I minus (D0 S + S D0)/2. The stationary equation gives R = V Q V. The matrix N = I minus nu Q is positive definite, so W = V N V is positive semidefinite and det W = det M times det R.")),
                    Paragraph(Text(
                        "With v = sqrt(det S), c = sqrt(1-r squared), h = S(0,1), and T = (1+r) S(0,0) + (1-r) S(1,1), two determinant identities express the product of the quadratic factors Fplus and Fminus as the sum of a nonnegative correlation term, a nonnegative drift-weighted imbalance term, and (det M minus one) det R. Positivity of W gives nu T <= 2 det S, while T >= 2 c v, hence v >= nu c. For positive r, Fplus = (v minus nu c) squared + (nu minus one) c (v minus nu c) + nu r squared is strictly positive. Consequently Fminus is nonnegative and v is at least vStar.")),
                    Paragraph(Text(
                        "At zero pump the matrix equation forces S = nu I for every physical stationary solution. For all stable pumps, the diagonal covariance with entries c vStar/(1+r) and c vStar/(1-r) is physical and solves the stationary equation at optMeas; its determinant square root is vStar. These arguments include mixed measurement covariances and zero bath occupation. They establish the global value and an aligned attainer, without classifying all equality cases."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kua-serafini-genoni-2025-general-dyne-optimality"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("general-dyne-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Matrices() => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Reals());
    private static Formula Identity() => Parenthesized(Seq(D(1), Sp, Colon, Sp, Matrices()));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Smul(Formula scalar, Formula matrix) => App(Q("HSMul", "hSMul"), scalar, matrix);
    private static Formula SqrtReal(Formula value) => App(Q("Real", "sqrt"), value);
    private static Formula Transpose(Formula value) => App(Q("Matrix", "transpose"), value);
    private static Formula MatrixLiteral(Formula a, Formula b, Formula c, Formula d) => Seq(
        Bang, Bang, OpenBracket, a, Comma, Sp, b, Semi, Sp, c, Comma, Sp, d, CloseBracket);
    private static Formula OmegaMatrix() => MatrixLiteral(D(0), D(1), new Formula.Negate(D(1)), D(0));
    private static Formula InputMatrix() => Smul(X("nu"), Identity());
    private static Formula InverseRoot() => App(Q("CFC", "sqrt"), Pow(Add(InputMatrix(), X("M")), new Formula.Negate(D(1))));
    private static Formula DriftFormula() => All("kappa", Reals(), All("chi", Reals(), Equal(
        Call("driftA", X("kappa"), X("chi")), MatrixLiteral(
            Sub(Div(new Formula.Negate(X("kappa")), D(2)), X("chi")), D(0), D(0),
            Add(Div(new Formula.Negate(X("kappa")), D(2)), X("chi"))))));
    private static Formula CouplingFormula() => All("kappa", Reals(), Equal(Call("coupling", X("kappa")),
        Smul(SqrtReal(X("kappa")), OmegaMatrix())));
    private static Formula EFormula() => All("kappa", Reals(), All("nu", Reals(), All("M", Matrices(), Equal(
        Call("eMat", X("kappa"), X("nu"), X("M")),
        Mul(Mul(Mul(OmegaMatrix(), Call("coupling", X("kappa"))), InputMatrix()), InverseRoot())))));
    private static Formula BFormula() => All("kappa", Reals(), All("nu", Reals(), All("M", Matrices(), Equal(
        Call("bMat", X("kappa"), X("nu"), X("M")),
        Mul(Mul(Call("coupling", X("kappa")), OmegaMatrix()), InverseRoot())))));
    private static Formula SteadyFormula()
    {
        var e = Call("eMat", X("kappa"), X("nu"), X("M"));
        var b = Call("bMat", X("kappa"), X("nu"), X("M"));
        var a = Add(Call("driftA", X("kappa"), X("chi")), Mul(e, Transpose(b)));
        var expression = Sub(Add(Add(Mul(a, X("S")), Mul(X("S"), Transpose(a))),
            Parenthesized(Sub(Smul(Mul(X("kappa"), X("nu")), Identity()), Mul(e, Transpose(e))))),
            Mul(Mul(Mul(X("S"), b), Transpose(b)), X("S")));
        return All("kappa", Reals(), All("chi", Reals(), All("nu", Reals(), All("M", Matrices(), All("S", Matrices(),
            Iff(Call("steadyEq", X("kappa"), X("chi"), X("nu"), X("M"), X("S")), Equal(expression, D(0))))))));
    }
    private static Formula ValueFormula()
    {
        var stable = Sub(D(1), Pow(X("r"), D(2)));
        var value = Div(Add(Mul(Sub(X("nu"), D(1)), SqrtReal(stable)),
            SqrtReal(Add(Mul(Pow(Sub(X("nu"), D(1)), D(2)), stable), Mul(D(4), X("nu"))))), D(2));
        return All("r", Reals(), All("nu", Reals(), Equal(Call("vStar", X("r"), X("nu")), value)));
    }
    private static Formula MeasurementFormula() => All("r", Reals(), Equal(Call("optMeas", X("r")), MatrixLiteral(
        Div(Sub(D(1), X("r")), Add(D(1), X("r"))), D(0), D(0), Div(Add(D(1), X("r")), Sub(D(1), X("r"))))));
    private static Formula Physical(Formula value) => Seq(Q("IsGaussianMeasurementCov"), Sp,
        Parenthesized(Seq(X("m"), Sp, Colon, Eq, Sp, D(1))), Sp, Parenthesized(value));
    private static Formula ClaimFormula() => Iff(Q("claim"), ClaimBodyFormula());
    private static Formula ClaimBodyFormula()
    {
        var r = Div(Mul(D(2), X("chi")), X("kappa"));
        var nu = Add(Mul(D(2), X("nth")), D(1));
        var optimum = Call("vStar", r, nu);
        var determinantRoot = SqrtReal(App(Q("Matrix", "det"), X("S")));
        var universal = All("M", Matrices(), All("S", Matrices(), Implies(Physical(X("M")), Implies(Physical(X("S")),
            Implies(Call("steadyEq", X("kappa"), X("chi"), nu, X("M"), X("S")), AtMost(optimum, determinantRoot))))));
        var attainer = Some("S", Matrices(), And(Physical(X("S")), And(
            Call("steadyEq", X("kappa"), X("chi"), nu, Call("optMeas", r), X("S")), Equal(determinantRoot, optimum))));
        return All("kappa", Reals(), All("chi", Reals(), All("nth", Reals(),
            Implies(Less(D(0), X("kappa")), Implies(AtMost(D(0), X("chi")),
            Implies(Less(X("chi"), Div(X("kappa"), D(2))), Implies(AtMost(D(0), X("nth")), And(universal, attainer))))))));
    }
}
