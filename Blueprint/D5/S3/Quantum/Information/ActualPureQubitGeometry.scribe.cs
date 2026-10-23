using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitGeometryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.",
        H("Pure-qubit affine geometry"),
        Blocks(
            Paragraph(Text("All matrices, vector spaces, predicates and maps below use the indicated Lean and Mathlib objects. Fin m is the outcome index type, and EuclideanSpace over the reals on Fin 3 is the Bloch-vector space. DensityState on Fin 2 is the canonical space of positive trace-one qubit states; Subtype.val exposes its CStarMatrix value. Real scalars enter complex matrices through Complex.ofReal, and WithLp.toLp 2 equips coordinate functions with the Euclidean structure. Division by zero and the real square root use their total real conventions.")),
            Paragraph(Text("The spectral expression specifies the chosen eigenvector unitary and eigenvalues of the positive matrix. Linear maps are determined by their typed underlying functions. The rank-two conclusion uses the coordinate isometry OrthonormalBasis.repr of the chosen basis.")),
            Describe.Lean(DescribeId.Create("spectral-sld-information"),
                DeclarationHandle.Create(Module + "spectralQFI"), H("Spectral SLD information"),
                StatementSource.FromAuthor(SpectralFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The spectral expression uses the chosen Hermitian eigenbasis and assigns zero to terms with zero denominator."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guarded-real-infimum"),
                DeclarationHandle.Create(Module + "guardedInfimum"), H("Guarded real infimum"),
                StatementSource.FromAuthor(GuardedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real infimum with explicit nonempty and bounded-below guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-density-bridge"),
                DeclarationHandle.Create(Module + "densityBridge"), H("Canonical density-state bridge"),
                StatementSource.FromAuthor(DensityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bridge constructs the canonical density state represented by the given positive trace-one matrix. Its state value is CStarMatrix.ofMatrix M, its positivity proof is map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg, and its trace proof is ht. The recovered-matrix equality is reflexive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-program-class"),
                DeclarationHandle.Create(Module + "IsProgram"), H("Full actual program class"),
                StatementSource.FromAuthor(ProgramFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predicate quantifies the full finite measurement and pure-curve data. The interval contains the closed radius interval, and the Born equation is an equality in the complex numbers with the real affine value embedded in them. The final clause quantifies over every proof of positivity at zero, exactly as displayed, even for arbitrary real R."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-set"),
                DeclarationHandle.Create(Module + "costs"), H("Attainable actual costs"),
                StatementSource.FromAuthor(CostsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set ranges over all actual programs in the preceding class."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-infimum"),
                DeclarationHandle.Create(Module + "C2"), H("Cost infimum"),
                StatementSource.FromAuthor(CtwoFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "C2 applies the guarded infimum to the attainable cost set; when the guard fails its value is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bloch"),
                DeclarationHandle.Create(Module + "bloch"), H("Bloch vector"),
                StatementSource.FromAuthor(BlochFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three real Bloch coordinates of a two by two matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochmatrix"),
                DeclarationHandle.Create(Module + "blochMatrix"), H("Bloch matrix"),
                StatementSource.FromAuthor(BlochMatrixFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hermitian matrix with a specified real trace and Bloch vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochmatrix-trace"),
                DeclarationHandle.Create(Module + "blochMatrix_trace"), H("Trace of a Bloch matrix"),
                StatementSource.FromAuthor(Disp(TraceBlochMatrixFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar coordinate is the complex trace, with the real scalar embedded in the complex numbers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bloch-blochmatrix"),
                DeclarationHandle.Create(Module + "bloch_blochMatrix"), H("Bloch coordinates of a Bloch matrix"),
                StatementSource.FromAuthor(Disp(InverseBlochFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch map recovers the vector coordinate for every real scalar and every real three-dimensional vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hermitian-bloch-geometry"),
                DeclarationHandle.Create(Module + "bloch_geometry_of_isHermitian"), H("Hermitian Bloch geometry"),
                StatementSource.FromAuthor(Disp(HermitianBlochFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Hermitian qubit matrix is determined by its trace and Bloch vector. If it has trace one and is idempotent, its Bloch vector has norm one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-bloch-bound"),
                DeclarationHandle.Create(Module + "norm_bloch_le_trace_of_posSemidef"), H("Positive Bloch norm bound"),
                StatementSource.FromAuthor(Disp(PositiveBlochBoundFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive semidefinite qubit matrix, the Bloch-vector norm is at most the real part of the trace. The determinant equals one quarter of the difference between the squared trace and the squared Bloch norm."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("effectreadout"),
                DeclarationHandle.Create(Module + "effectReadout"), H("Visible readout map"),
                StatementSource.FromAuthor(ReadoutFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframe"),
                DeclarationHandle.Create(Module + "reframe"), H("Orthogonal change of Bloch coordinates"),
                StatementSource.FromAuthor(ReframeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An orthogonal change of the Bloch vector preserves the trace coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochlinear"),
                DeclarationHandle.Create(Module + "blochLinear"), H("Linear Bloch map"),
                StatementSource.FromAuthor(BlochLinearFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch coordinates form a real linear map on complex matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframelinear"),
                DeclarationHandle.Create(Module + "reframeLinear"), H("Linear change of matrix coordinates"),
                StatementSource.FromAuthor(ReframeLinearFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed orthogonal Bloch frame induces a real linear map on matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root"),
                DeclarationHandle.Create(Module + "root"), H("Small quadratic root"),
                StatementSource.FromAuthor(RootFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radiusmap"),
                DeclarationHandle.Create(Module + "radiusMap"), H("Radius map"),
                StatementSource.FromAuthor(RadiusFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This real function converts an arc parameter into a radius for the effect-family statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extendedcost"),
                DeclarationHandle.Create(Module + "extendedCost"), H("Extended family cost"),
                StatementSource.FromAuthor(ExtendedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost formula extends through the zero transverse parameter for the normalization branch."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upperdiag"),
                DeclarationHandle.Create(Module + "upperDiag"), H("Upper diagonal coefficient"),
                StatementSource.FromAuthor(UpperFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complementary quadratic root determines the upper diagonal effect coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effect"),
                DeclarationHandle.Create(Module + "effect"), H("Actual effect matrix"),
                StatementSource.FromAuthor(EffectFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two diagonal coefficients and the normalized direction determine each effect matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arc"),
                DeclarationHandle.Create(Module + "arc"), H("Pure-state arc"),
                StatementSource.FromAuthor(ArcFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-rank-two-parameters"),
                DeclarationHandle.Create(Module + "actual_rank_two_parameters"), H("Actual rank-two arc and feasible coefficients"),
                StatementSource.FromAuthor(RankTwoFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The basis supplies a fixed coordinate frame. The coefficients and the signed square-root coordinate satisfy exactly the conjunction below; the last bound holds for every nonnegative radius whose closed interval lies in I.")))))));

    private static Formula TraceBlochMatrixFormula() => All("a", Reals(), All("r", BlochVectors(),
        Equal(Trace(Call("blochMatrix", X("a"), X("r"))), OfReal(X("a")))));

    private static Formula InverseBlochFormula() => All("a", Reals(), All("r", BlochVectors(),
        Equal(Call("bloch", Call("blochMatrix", X("a"), X("r"))), X("r"))));

    private static Formula HermitianBlochFormula() => All("M", QubitMatrices(),
        Implies(IsHermitian(X("M")), And(
            Equal(X("M"), Call("blochMatrix", RealPart(Trace(X("M"))), Call("bloch", X("M")))),
            Implies(Equal(Trace(X("M")), Num(1)),
                Implies(Equal(Multiply(X("M"), X("M")), X("M")),
                    Equal(new Formula.Norm(Call("bloch", X("M"))), Num(1)))))));

    private static Formula PositiveBlochBoundFormula() => All("M", QubitMatrices(),
        Implies(PosSemidef(X("M")), LE(new Formula.Norm(Call("bloch", X("M"))), RealPart(Trace(X("M"))))));

    private static Formula SpectralFormula()
    {
        Formula matrices = Matrices(X("n"));
        Formula unitary = Field(Field(X("hp"), "isHermitian"), "eigenvectorUnitary");
        Formula eigenvalues = Field(Field(X("hp"), "isHermitian"), "eigenvalues");
        Formula matrixUnitary = Typed(X("U"), matrices);
        return Disp(All("n", Seq(X("Type"), Star), Instances(X("n"),
            All("rho", matrices, All("B", matrices, All("hp", PosSemidef(X("rho")),
                Let("U", At(Qualified("Matrix", "unitaryGroup"), X("n"), Complexes()), unitary,
                    Let("M", matrices, Multiply(Multiply(Call("star", matrixUnitary), X("B")), matrixUnitary),
                        Equal(Call("spectralQFI", X("rho"), X("B"), X("hp")),
                            SumOver("i", X("n"), SumOver("j", X("n"), Fraction(
                                Multiply(Num(2), At(Qualified("Complex", "normSq"), At(X("M"), X("i"), X("j")))),
                                Add(At(eigenvalues, X("i")), At(eigenvalues, X("j")))))))))))))));
    }

    private static Formula GuardedFormula() => Disp(All("S", RealSets(),
        Equal(Call("guardedInfimum", X("S")), Call("ite",
            And(At(Qualified("Set", "Nonempty"), X("S")), Call("BddBelow", X("S"))),
            Call("sInf", X("S")), Num(0)))));

    private static Formula DensityFormula()
    {
        Formula bridge = Call("densityBridge", X("M"), X("hM"), X("ht"));
        Formula densityType = Call("Subtype", LambdaOf("rho", DensityStates(),
            Equal(UnderlyingMatrix(X("rho")), X("M"))));
        Formula positiveProof = At(new Formula.Subscript(Name("map"), X("nonneg")),
            Qualified("CStarMatrix", "ofMatrixStarAlgEquiv"), Field(X("hM"), "nonneg"));
        Formula state = Tuple(At(Qualified("CStarMatrix", "ofMatrix"), X("M")), positiveProof, X("ht"));
        return Disp(All("M", QubitMatrices(), All("hM", PosSemidef(X("M")),
            All("ht", Equal(Trace(X("M")), Num(1)), And(
                Equal(Typed(bridge, densityType), Tuple(state, X("rfl"))),
                Equal(UnderlyingMatrix(Val(bridge)), X("M")))))));
    }

    private static Formula ProgramFormula()
    {
        Formula state = At(X("rho"), X("u"));
        Formula affine = Add(At(X("p"), X("j")), Multiply(X("u"), At(X("v"), X("j"))));
        Formula conditions = Conjoin(
            Call("IsOpen", X("I")), Call("IsPreconnected", X("I")), Subset(RadiusInterval(X("R")), X("I")),
            All("j", Fin(X("m")), PosSemidef(At(X("N"), X("j")))),
            Equal(SumOver("j", Fin(X("m")), At(X("N"), X("j"))), Typed(Num(1), QubitMatrices())),
            Call("ContDiffOn", Reals(), Num(1), X("rho"), X("I")),
            AllIn("u", X("I"), Conjoin(PosSemidef(state), Equal(Trace(state), Num(1)),
                Equal(Multiply(state, state), state), Ex("r", DensityStates(), Equal(UnderlyingMatrix(X("r")), state)))),
            AllIn("u", X("I"), All("j", Fin(X("m")), And(
                Equal(Trace(Multiply(At(X("N"), X("j")), state)), OfReal(affine)), LT(Num(0), affine)))),
            All("h", PosSemidef(At(X("rho"), Num(0))), Equal(
                Call("spectralQFI", At(X("rho"), Num(0)), Call("deriv", X("rho"), Num(0)), X("h")), X("Q"))));
        return Disp(All("m", Naturals(), All("p", Scores(), All("v", Scores(), All("R", Reals(),
            All("N", Effects(), All("rho", Curves(), All("I", RealSets(), All("Q", Reals(),
                Iff(Call("IsProgram", X("p"), X("v"), X("R"), X("N"), X("rho"), X("I"), X("Q")), conditions))))))))));
    }

    private static Formula CostsFormula() => Disp(All("m", Naturals(), All("p", Scores(), All("v", Scores(), All("R", Reals(),
        Equal(Call("costs", X("p"), X("v"), X("R")), Seq(OpenBrace, Typed(X("Q"), Reals()), Mid, Sp,
            Ex("N", Effects(), Ex("rho", Curves(), Ex("I", RealSets(),
                Call("IsProgram", X("p"), X("v"), X("R"), X("N"), X("rho"), X("I"), X("Q"))))), CloseBrace)))))));

    private static Formula CtwoFormula() => Disp(All("m", Naturals(), All("p", Scores(), All("v", Scores(), All("R", Reals(),
        Equal(Call("C2", X("p"), X("v"), X("R")), Call("guardedInfimum", Call("costs", X("p"), X("v"), X("R")))))))));

    private static Formula BlochFormula() => Disp(All("M", QubitMatrices(), Equal(Call("bloch", X("M")),
        ToLp(Vector(Multiply(Num(2), RealPart(At(X("M"), Num(0), Num(1)))),
            Multiply(Negate(Num(2)), ImaginaryPart(At(X("M"), Num(0), Num(1)))),
            Subtract(RealPart(At(X("M"), Num(0), Num(0))), RealPart(At(X("M"), Num(1), Num(1)))))))));

    private static Formula BlochMatrixFormula() => Disp(All("a", Reals(), All("r", BlochVectors(),
        Equal(Call("blochMatrix", X("a"), X("r")), MatrixTwo(
            Fraction(OfReal(Add(X("a"), At(X("r"), Num(2)))), Num(2)),
            Fraction(Subtract(OfReal(At(X("r"), Num(0))), Multiply(OfReal(At(X("r"), Num(1))), Qualified("Complex", "I"))), Num(2)),
            Fraction(Add(OfReal(At(X("r"), Num(0))), Multiply(OfReal(At(X("r"), Num(1))), Qualified("Complex", "I"))), Num(2)),
            Fraction(OfReal(Subtract(X("a"), At(X("r"), Num(2)))), Num(2)))))));

    private static Formula ReadoutFormula() => Disp(All("m", Naturals(), All("N", Effects(),
        Equal(At(Qualified("DFunLike", "coe"), Typed(Call("effectReadout", X("N")),
                RealLinear(BlochVectors(), Scores()))),
            LambdaOf("r", BlochVectors(), LambdaOf("j", Fin(X("m")), Fraction(
                Seq(new Formula.Subscript(Seq(Langle, Call("bloch", At(X("N"), X("j"))), Comma, Sp, X("r"), Rangle), Reals())),
                Num(2))))))));

    private static Formula ReframeFormula() => Disp(All("O", Frames(), All("M", QubitMatrices(),
        Equal(Call("reframe", X("O"), X("M")),
            Call("blochMatrix", RealPart(Trace(X("M"))), At(X("O"), Call("bloch", X("M"))))))));

    private static Formula BlochLinearFormula() => Disp(Equal(
        At(Qualified("DFunLike", "coe"), Typed(Name("blochLinear"), RealLinear(QubitMatrices(), BlochVectors()))), Name("bloch")));

    private static Formula ReframeLinearFormula() => Disp(All("O", Frames(), Equal(
        At(Qualified("DFunLike", "coe"), Typed(Call("reframeLinear", X("O")), RealLinear(QubitMatrices(), QubitMatrices()))),
        Call("reframe", X("O")))));

    private static Formula RootFormula() => Disp(ScalarParameters(Equal(
        Call("root", X("p"), X("d"), X("alpha"), X("e"), X("w")),
        Fraction(Multiply(Multiply(Multiply(Num(2), Subtract(Num(1), X("e"))), Square(X("w"))), Square(X("d"))),
            Add(QuadraticCenter(), QuadraticRadical())))));

    private static Formula RadiusFormula() => Disp(All("B", Reals(), All("alpha", Reals(), All("w", Arrow(Reals(), Reals()), All("t", Reals(),
        Equal(Call("radiusMap", X("B"), X("alpha"), X("w"), X("t")), Fraction(
            Multiply(Subtract(Multiply(Multiply(Num(2), X("t")), SqrtReal(Subtract(Num(1), Square(X("t"))))),
                Multiply(new Formula.Absolute(X("alpha")), Square(X("t")))), At(X("w"), Square(X("t")))),
            Multiply(Add(Num(1), X("t")), SqrtReal(X("B"))))))))));

    private static Formula ExtendedFormula() => Disp(All("B", Reals(), All("alpha", Reals(), All("w", Arrow(Reals(), Reals()), All("e", Reals(),
        Equal(Call("extendedCost", X("B"), X("alpha"), X("w"), X("e")), Fraction(
            Multiply(Fraction(X("B"), Square(At(X("w"), X("e")))), Multiply(Num(4), Subtract(Num(1), X("e")))),
            Subtract(Multiply(Num(4), Subtract(Num(1), X("e"))), Multiply(Square(X("alpha")), X("e"))))))))));

    private static Formula UpperFormula() => Disp(ScalarParameters(Equal(
        Call("upperDiag", X("p"), X("d"), X("alpha"), X("e"), X("w")),
        Fraction(Add(QuadraticCenter(), QuadraticRadical()), Multiply(Num(2), Subtract(Num(1), X("e")))))));

    private static Formula EffectFormula() => Disp(ScalarParameters(Equal(
        Call("effect", X("p"), X("d"), X("alpha"), X("e"), X("w")), MatrixTwo(
            OfReal(Call("upperDiag", X("p"), X("d"), X("alpha"), X("e"), X("w"))), OfReal(Multiply(X("w"), X("d"))),
            OfReal(Multiply(X("w"), X("d"))), OfReal(Call("root", X("p"), X("d"), X("alpha"), X("e"), X("w")))))));

    private static Formula ArcFormula() => Disp(All("e", Reals(), All("x", Reals(), All("c", Reals(), All("u", Reals(),
        Equal(Call("arc", X("e"), X("x"), X("c"), X("u")), Call("blochMatrix", Num(1),
            ToLp(Vector(AffineCoordinate(), SqrtReal(Subtract(ArcRadiusSquared(X("e")), Square(AffineCoordinate()))),
                Subtract(Num(1), Multiply(Num(2), X("e"))))))))))));

    private static Formula RankTwoFormula()
    {
        Formula state = At(X("rho"), X("u"));
        Formula affine = Add(At(X("p"), X("j")), Multiply(X("u"), At(X("v"), X("j"))));
        Formula hypotheses = Conjoin(
            Call("IsOpen", X("I")), Call("IsPreconnected", X("I")), Member(Num(0), X("I")), NotEqual(X("v"), Num(0)),
            All("j", Fin(X("m")), PosSemidef(At(X("N"), X("j")))),
            Equal(SumOver("j", Fin(X("m")), At(X("N"), X("j"))), Typed(Num(1), QubitMatrices())),
            Call("ContDiffOn", Reals(), Num(1), X("rho"), X("I")),
            AllIn("u", X("I"), Conjoin(PosSemidef(state), Equal(Trace(state), Num(1)), Equal(Multiply(state, state), state))),
            AllIn("u", X("I"), All("j", Fin(X("m")), Equal(RealPart(Trace(Multiply(At(X("N"), X("j")), state))), affine))),
            Equal(At(Qualified("Module", "finrank"), Reals(), At(Qualified("LinearMap", "range"), Call("effectReadout", X("N")))), Num(2)));
        Formula coefficients = All("j", Fin(X("m")), Conjoin(
            LE(Num(0), At(X("q"), X("j"))), LE(Num(0), At(X("A"), X("j"))),
            LE(Square(At(X("b"), X("j"))), Multiply(At(X("A"), X("j")), At(X("q"), X("j")))),
            Equal(At(X("b"), X("j")), Fraction(At(X("v"), X("j")), X("c"))),
            Equal(At(X("A"), X("j")), Fraction(Subtract(Subtract(At(X("p"), X("j")),
                Multiply(At(X("b"), X("j")), X("x"))), Multiply(X("epsilon"), At(X("q"), X("j")))), Subtract(Num(1), X("epsilon"))))));
        Formula coordinates = ToLp(Vector(AffineCoordinate(),
            Multiply(X("s"), SqrtReal(Subtract(ArcRadiusSquared(X("epsilon")), Square(AffineCoordinate())))),
            Subtract(Num(1), Multiply(Num(2), X("epsilon")))));
        Formula conclusion = Ex("basis", Call("OrthonormalBasis", Fin(Num(3)), Reals(), BlochVectors()),
            Ex("x", Reals(), Ex("c", Reals(), Ex("epsilon", Reals(), Ex("s", Reals(),
            Ex("A", Scores(), Ex("q", Scores(), Ex("b", Scores(), Conjoin(
                LT(Num(0), X("c")), LT(Num(0), X("epsilon")), LE(X("epsilon"), Fraction(Num(1), Num(2))),
                Or(Equal(X("s"), Num(1)), Equal(X("s"), Negate(Num(1)))), coefficients,
                Equal(SumOver("j", Fin(X("m")), At(X("q"), X("j"))), Num(1)),
                AllIn("u", X("I"), Equal(Call("reframe", At(Qualified("OrthonormalBasis", "repr"), X("basis")), state),
                    Call("blochMatrix", Num(1), coordinates))),
                AllIn("u", X("I"), LT(Square(AffineCoordinate()), ArcRadiusSquared(X("epsilon")))),
                All("R", Reals(), Implies(LE(Num(0), X("R")), Implies(Subset(RadiusInterval(X("R")), X("I")),
                    LT(Add(new Formula.Absolute(X("x")), Multiply(X("c"), X("R"))), SqrtReal(ArcRadiusSquared(X("epsilon"))))))))))))))));
        return Disp(All("m", Naturals(), All("N", Effects(), All("rho", Curves(), All("p", Scores(), All("v", Scores(), All("I", RealSets(),
            Implies(hypotheses, conclusion))))))));
    }

    private static Formula QuadraticCenter() => Subtract(X("p"), Multiply(Multiply(Multiply(X("alpha"), X("e")), X("w")), X("d")));
    private static Formula QuadraticRadical() => SqrtReal(Subtract(Square(QuadraticCenter()),
        Multiply(Multiply(Multiply(Multiply(Num(4), X("e")), Subtract(Num(1), X("e"))), Square(X("w"))), Square(X("d")))));
    private static Formula AffineCoordinate() => Add(X("x"), Multiply(X("c"), X("u")));
    private static Formula ArcRadiusSquared(Formula e) => Multiply(Multiply(Num(4), e), Subtract(Num(1), e));
    private static Formula ScalarParameters(Formula body) => All("p", Reals(), All("d", Reals(), All("alpha", Reals(), All("e", Reals(), All("w", Reals(), body)))));
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Field(Formula value, string name) => Seq(Parenthesized(value), Dot, X(name));
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrices(Formula n) => Call("Matrix", n, n, Complexes());
    private static Formula QubitMatrices() => Matrices(Fin(Num(2)));
    private static Formula BlochVectors() => Call("EuclideanSpace", Reals(), Fin(Num(3)));
    private static Formula RealSets() => Call("Set", Reals());
    private static Formula Scores() => Arrow(Fin(X("m")), Reals());
    private static Formula Effects() => Arrow(Fin(X("m")), QubitMatrices());
    private static Formula Curves() => Arrow(Reals(), QubitMatrices());
    private static Formula RealLinear(Formula source, Formula target) => Call("LinearMap", At(Qualified("RingHom", "id"), Reals()), source, target);
    private static Formula Frames() => Call("LinearIsometryEquiv", At(Qualified("RingHom", "id"), Reals()), BlochVectors(), BlochVectors());
    private static Formula DensityStates() => At(Qualified("FiniteStateChannel", "DensityState"), Fin(Num(2)));
    private static Formula Val(Formula value) => At(Qualified("Subtype", "val"), value);
    private static Formula UnderlyingMatrix(Formula rho) => At(Field(Qualified("CStarMatrix", "ofMatrix"), "symm"), Val(rho));
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula RealPart(Formula value) => At(Qualified("Complex", "re"), value);
    private static Formula ImaginaryPart(Formula value) => At(Qualified("Complex", "im"), value);
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula ToLp(Formula value) => At(Qualified("WithLp", "toLp"), Num(2), value);
    private static Formula SqrtReal(Formula value) => At(Qualified("Real", "sqrt"), value);
    private static Formula PosSemidef(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);
    private static Formula IsHermitian(Formula value) => At(Qualified("Matrix", "IsHermitian"), value);
    private static Formula RadiusInterval(Formula radius) => At(Qualified("Set", "Icc"), Negate(radius), radius);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula AllIn(string name, Formula set, Formula body) => All(name, Reals(), Implies(Member(X(name), set), body));
    private static Formula LambdaOf(string name, Formula domain, Formula body) => Parenthesized(Seq(Typed(X(name), domain), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Name("let"), Sp, Typed(X(name), type), Sp, Colon, Eq, Sp, Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula Instances(Formula type, Formula body) => Seq(
        OpenBracket, Call("Fintype", type), CloseBracket, Sp, OpenBracket, Call("DecidableEq", type), CloseBracket, Sp, body);
    private static Formula SumOver(string name, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Sum, Typed(X(name), domain)), Sp, Parenthesized(body));
    private static Formula Vector(Formula a, Formula b, Formula c) => Seq(Bang, OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket);
    private static Formula MatrixTwo(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(X("pmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(X("pmatrix")));
    private static Formula Tuple(params Formula[] values)
    {
        Formula result = values[0];
        for (int i = 1; i < values.Length; i++) result = Seq(result, Comma, Sp, values[i]);
        return Seq(Langle, result, Rangle);
    }
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) result = And(clauses[i], result);
        return result;
    }
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subset(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Num(2));
}
