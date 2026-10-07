using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class ActualSpectralSeriesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/ActualSpectralSeries.";
    private static Formula I(string s) => F.Id(s);
    private static Formula A(string s, params Formula[] xs) => Call(s, xs);
    private static Formula R => A("Real");
    private static Formula H => A("Lp", R, F.D(2), I("mu"));
    private static Formula KP => A("Lp", R, F.D(2), A("prod", I("mu"), I("mu")));
    private static Formula SK => A("symmetricKernel", I("mu"));
    private static Formula All(string s, Formula t, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(s), t)], body);
    private static Formula Ex(string s, Formula t, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(s), t)], body);
    private static Formula L(string s, Formula t, Formula body) =>
        F.Seq(F.Open, I(s), F.Colon, t, F.Mapsto, body, F.Close);
    private static Formula Eq(Formula x, Formula y) => A("Eq", x, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Norm(Formula x) => A("norm", x);
    private static Formula Sq(Formula x) => A("pow", x, F.D(2));
    private static Formula B(Formula i) => A("b", i);
    private static Formula C(Formula i) => A("c", i);
    private static Formula Diag(Formula x) => A("diagonalKernel", I("mu"), x);
    private static Formula TK => A("T", A("val", I("K")));
    private static Formula I2 => A("secondIntegral", I("mu"), I("P"), I("W"), I("hW"), I("K"));
    private static Formula Inner(Formula x, Formula y) => A("inner", R, x, y);
    private static Formula KernelSum => A("HasSum", L("i", I("index"),
        A("smul", C(I("i")), Diag(B(I("i"))))), I("K"));
    private static Formula NoiseSum => A("HasSum", L("i", I("index"),
        A("smul", C(I("i")), A("centeredSquare", I("mu"), I("P"), I("W"), I("hW"), B(I("i"))))), I2);
    private static Formula Eigen => All("i", I("index"),
        Eq(A("apply", TK, B(I("i"))), A("smul", C(I("i")), B(I("i")))));
    private static Formula NoiseHyp => All("f", H,
        A("HasLaw", L("omega", I("Omega"), A("W", I("f"), I("omega"))),
            A("gaussianReal", F.D(0), A("toNNReal", Sq(Norm(I("f"))))), I("P")));
    private static Formula Spatial(Formula body) => All("X", I("Type"),
        All("mX", A("MeasurableSpace", I("X")), All("mu", A("Measure", I("X")),
            All("hfinite", A("IsFiniteMeasure", I("mu")), body))));
    private static Formula Operator(Formula body) => Spatial(All("T", A("ContinuousLinearMap", R, KP,
        A("ContinuousLinearMap", R, H, H)), All("hT", All("K", KP, All("f", H,
            A("AEEq", L("x", I("X"), A("T", I("K"), I("f"), I("x"))),
                L("x", I("X"), A("integral", L("y", I("X"),
                    A("mul", A("K", A("pair", I("x"), I("y"))), A("f", I("y")))), I("mu"))), I("mu")))), body)));
    private static Formula Noise(Formula body) => All("Omega", I("Type"),
        All("mOmega", A("MeasurableSpace", I("Omega")), All("P", A("Measure", I("Omega")),
            All("hprob", A("IsProbabilityMeasure", I("P")),
                All("W", A("LinearIsometry", R, H, A("Lp", R, F.D(2), I("P"))),
                    All("hW", NoiseHyp, body))))));
    private static Formula Basis(Formula body) => All("index", I("Type"),
        All("hcount", A("Countable", I("index")),
            All("b", A("HilbertBasis", I("index"), R, H),
                All("c", A("Function", I("index"), R), body))));
    private static Formula SpectralConclusion => And(A("Summable", L("i", I("index"), Sq(C(I("i"))))),
        And(Eq(A("tsum", L("i", I("index"), Sq(C(I("i"))))), Sq(Norm(I("K")))),
            And(Eq(Sq(Norm(I("K"))), A("div", A("variance", I2, I("P")), F.D(2))),
                And(All("i", I("index"), A("Le", A("abs", C(I("i"))), Norm(TK))),
                    And(A("Le", A("iSup", L("i", I("index"), A("abs", C(I("i"))))), Norm(TK)), NoiseSum)))));
    private static Formula OldJoint => All("s", A("Finset", I("index")),
        All("n", A("Nat"), All("old", A("Function", A("Fin", I("n")), H),
            A("HasGaussianLaw", L("omega", I("Omega"), L("j", A("Sum", I("s"), A("Fin", I("n"))),
                A("W", A("sumElim", L("i", I("s"), B(A("val", I("i")))), I("old"), I("j")), I("omega")))), I("P")))));
    private static Formula Constructed => Ex("index", I("Type"),
        Ex("hcount", A("Countable", I("index")), Ex("b", A("HilbertBasis", I("index"), R, H),
            Ex("c", A("Function", I("index"), R), And(Eigen, And(KernelSum,
                And(SpectralConclusion, And(A("iIndepFun", L("i", I("index"), L("omega", I("Omega"),
                    A("W", B(I("i")), I("omega")))), I("P")),
                    And(All("i", I("index"), A("HasLaw", L("omega", I("Omega"), A("W", B(I("i")), I("omega"))),
                        A("gaussianReal", F.D(0), F.D(1)), I("P"))), OldJoint)))))))));

    private static Formula TransportFormula()
    {
        Formula idx = I("index"), e = I("e"), coeff = I("coeff"), op = I("T");
        Formula ei(Formula i) => A("e", i);
        Formula ci(Formula i) => A("coeff", i);
        Formula sum = A("HasSum", L("i", idx, A("smul", ci(I("i")), Diag(ei(I("i"))))), I("K"));
        Formula eigen = All("i", idx, Eq(A("T", ei(I("i"))), A("smul", ci(I("i")), ei(I("i")))));
        Formula mapped = A("HasSum", L("i", idx, A("smul", ci(I("i")),
            A("centeredSquare", I("mu"), I("P"), I("W"), I("hW"), ei(I("i"))))), I2);
        Formula conclusion = And(A("Summable", L("i", idx, Sq(ci(I("i"))))),
            And(Eq(A("tsum", L("i", idx, Sq(ci(I("i"))))), Sq(Norm(I("K")))),
                And(Eq(Sq(Norm(I("K"))), A("div", A("variance", I2, I("P")), F.D(2))),
                    And(All("i", idx, A("Le", A("abs", ci(I("i"))), Norm(op))),
                        And(A("Le", A("iSup", L("i", idx, A("abs", ci(I("i"))))), Norm(op)), mapped)))));
        return Spatial(Noise(All("K", SK, All("T", A("ContinuousLinearMap", R, H, H),
            All("index", I("Type"), All("hcount", A("Countable", idx),
                All("e", A("Function", idx, H), All("coeff", A("Function", idx, R),
                    Imp(And(A("Orthonormal", R, e), And(eigen, sum)), conclusion)))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integral kernels have complete same-noise spectral series, including nullspace and zero variance.",
        H("Actual kernel spectral construction"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-pairing"),
                DeclarationHandle.Create(Module + "integral_operator_pairing"),
                H("Actual kernel pairing"), StatementSource.FromAuthor(F.Disp(Operator(All("K", KP, All("f", H, All("g", H, Eq(Inner(A("T", I("K"), I("f")), I("g")), Inner(A("rankOne", I("mu"), I("g"), I("f")), I("K"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("For every finite measure and every continuous kernel factory with the actual a.e. integral representation, Fubini identifies the operator pairing with the product-space rank-one pairing. Integrability follows from the two actual L2 classes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-injective"),
                DeclarationHandle.Create(Module + "integral_operator_injective"),
                H("Kernel identification"), StatementSource.FromAuthor(F.Disp(Operator(A("Injective", I("T"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Equality of actual integral operators implies equality of their L2 kernels. The proof consumes the pairing identity and the original rank-one totality supplier; it introduces no identification premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-diagonal"),
                DeclarationHandle.Create(Module + "integral_operator_diagonal"),
                H("Actual rank-one operator"), StatementSource.FromAuthor(F.Disp(Operator(All("f", H, All("g", H, Eq(A("T", A("rankOne", I("mu"), I("f"), I("f")), I("g")), A("smul", Inner(I("f"), I("g")), I("f")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("A diagonal kernel acts by f times inner(f,g) on the original spatial Hilbert space. This consumed helper identifies every finite approximation used to prove compactness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-symmetric"),
                DeclarationHandle.Create(Module + "integral_operator_symmetric"),
                H("Kernel symmetry"), StatementSource.FromAuthor(F.Disp(Operator(All("K", SK, A("IsSymmetric", TK))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("The fixed subspace of coordinate swap gives a symmetric actual operator. Swap is an isometry on the same product measure, and the rank-one swap supplier is consumed in the proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-compact"),
                DeclarationHandle.Create(Module + "integral_operator_compact"),
                H("Compactness from actual kernels"), StatementSource.FromAuthor(F.Disp(Operator(All("K", SK, A("IsCompactOperator", TK))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Dense finite diagonal-kernel sums map to genuine finite-rank operators. Continuity of the kernel factory and the closedness of compact operators pass compactness to every actual symmetric L2 kernel. Compactness is constructed, not assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-eigenbasis"),
                DeclarationHandle.Create(Module + "integral_operator_eigenbasis"),
                H("Complete countable eigenfamily"), StatementSource.FromAuthor(F.Disp(Operator(All("hgenerated", A("CountablyGenerated", I("X")), All("K", SK, Ex("index", I("Type"), Ex("hcount", A("Countable", I("index")), Ex("b", A("HilbertBasis", I("index"), R, H), Ex("c", A("Function", I("index"), R), Eigen))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Nonzero eigenspaces use the pinned finite-dimensional eigenspace theorem and finite orthonormal bases. Their Hilbert bases and the zero-eigenspace Hilbert basis are assembled using the pinned compact spectral totality theorem. The zero eigenspace is retained. Orthonormality and separability make the resulting family countable, including empty and zero-operator cases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-orthonormal"),
                DeclarationHandle.Create(Module + "diagonal_orthonormal"),
                H("Diagonal orthonormality"), StatementSource.FromAuthor(F.Disp(Spatial(All("index", I("Type"), All("e", A("Function", I("index"), H), Imp(A("Orthonormal", R, I("e")), A("Orthonormal", R, L("i", I("index"), Diag(A("e", I("i"))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("An orthonormal spatial family gives an orthonormal family of diagonal kernels under the product-measure inner product."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-kernel-sum"),
                DeclarationHandle.Create(Module + "kernel_hasSum_of_eigenbasis"),
                H("Complete actual kernel series"), StatementSource.FromAuthor(F.Disp(Operator(All("K", SK, Basis(Imp(Eigen, KernelSum)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Bessel gives square summability of actual diagonal-kernel coefficients. Its convergent kernel series has the same action on every eigenbasis vector as the original operator. Completeness and kernel-to-operator injectivity identify the limit with the original K. No kernel HasSum is supplied as a premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-transport"),
                DeclarationHandle.Create(Module + "same_noise_series_of_kernel_hasSum"),
                H("Consumed same-noise transport"), StatementSource.FromAuthor(F.Disp(TransportFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("This conditional transport helper is consumed by actual_same_noise_spectral after kernel HasSum is constructed. It maps the kernel series through the original secondIntegral and derives exact square sum, variance and operator-norm bounds. It receives zero independent content credit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-joint"),
                DeclarationHandle.Create(Module + "same_noise_finite_joint"),
                H("Joint laws of the original W"), StatementSource.FromAuthor(F.Disp(Spatial(Noise(All("index", I("Type"), All("hfiniteIndex", A("Finite", I("index")), All("f", A("Function", I("index"), H), A("HasGaussianLaw", L("omega", I("Omega"), L("i", I("index"), A("W", A("f", I("i")), I("omega")))), I("P"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("Every scalar linear combination of the finite coordinates is an evaluation of the same W, almost everywhere. The pinned Gaussian linear-functional characterization yields the finite joint Gaussian law on the same P. No product noise or joint-Gaussian premise is introduced. Empty families and arbitrary old fixed vectors remain in scope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-independence"),
                DeclarationHandle.Create(Module + "same_noise_finite_independence"),
                H("Finite row independence"), StatementSource.FromAuthor(F.Disp(Spatial(Noise(All("index", I("Type"), All("hfiniteIndex", A("Finite", I("index")), All("e", A("Function", I("index"), H), Imp(A("Orthonormal", R, I("e")), A("iIndepFun", L("i", I("index"), L("omega", I("Omega"), A("W", A("e", I("i")), I("omega")))), I("P")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("The constructed finite joint law and orthonormal covariance identity give independence on the original P. This consumed helper extends to the countable spectral row by finite restrictions; no independence from old vectors or between rows is claimed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-construction"),
                DeclarationHandle.Create(Module + "actual_same_noise_spectral"),
                H("Actual same-noise spectral representation"), StatementSource.FromAuthor(F.Disp(Operator(Noise(All("hgenerated", A("CountablyGenerated", I("X")), All("K", SK, Constructed)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
                Blocks(Paragraph(Text("For every actual symmetric kernel, the construction returns a complete countable orthonormal eigenbasis, the complete kernel HasSum, exact coefficient square sum equal to the kernel norm squared and variance divided by two, coefficient and supremum operator bounds, and the actual infinite L2(P) second-integral series. Its standard Gaussian coordinates are independent within the row and jointly Gaussian with every finite old-vector append under the original W and P. Zero coefficients, nullspace and zero variance are included. Each row may have its own eigenbasis. This result does not assert the original covariance asymptotics, real-filter limit, increment estimates, path tightness, completed-field mixing or full original process goal."))), DescribeRole.Theorem))));
}
