using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class PurityPythagorasDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise orthogonal basis measurements split density-matrix purity excess into "
            + "visible probability energy and orthogonal residual mass.",
        H("Purity Pythagoras Decomposition"),
        Blocks(
            AddedNode("matrix-inner-trace", "matrix_inner_eq_trace_conjTranspose_mul",
                "The complex matrix inner product is a trace pairing", MatrixInnerTraceFormula(),
                "The Hilbert–Schmidt inner product of two square complex matrices is the trace of the conjugate transpose of the first times the second. This identity applies in every natural dimension, including zero."),
            AddedNode("hermitian-trace-real", "trace_mul_real_of_hermitian",
                "Products of Hermitian matrices have real trace", HermitianTraceFormula(),
                "The two Hermitian factors need not commute. Taking the conjugate of their product trace reverses their order, and cyclicity of trace restores the original value. Thus the complex trace is its real part embedded into the complex numbers."),
            AddedNode("centered-hermitian-norm", "centered_hermitian_norm_sq",
                "Centering removes the squared scalar trace component", CenteredHermitianFormula(),
                "For a Hermitian matrix in nonzero dimension, subtracting trace(H)/d times the identity removes exactly (real trace H) squared divided by d from its squared Hilbert–Schmidt norm. The trace is real and the remaining matrix has trace zero."),
            AddedNode("trace-zero-measurement-norm", "traceZero_measurement_norm_sq",
                "Measurement energy is the sum of squared trace coordinates", TraceZeroMeasurementFormula(),
                "A trace-zero Hermitian matrix X is a Hermitian matrix with trace zero, represented by its underlying matrix X.1.1. For a complete rank-one record context, its measured matrix is the sum of P_j X P_j. The rank-one compression identity expresses this as a sum of trace coordinates times P_j, and these projectors are orthonormal in the Hilbert–Schmidt inner product. Its squared norm is therefore the sum of squared real trace coordinates."),
            AddedNode("trace-zero-context-pythagoras", "traceZero_context_pythagoras",
                "Orthogonal contexts split every trace-zero Hermitian matrix", TraceZeroPythagorasFormula(),
                "Each context is a family of normalized Hermitian rank-one idempotents resolving the identity. A record context has pairwise orthogonal projectors. Assume that the measurement images of distinct contexts are mutually orthogonal for the real Hilbert–Schmidt inner product; this is the expanded hypothesis below. The underlying trace-zero Hermitian matrix then splits into the sum of all measured components and their orthogonal residual. The formula expands each measured component as its compression sum and the residual as the original matrix minus the sum of these components. No positivity or trace-one assumption is imposed on the input."),
            Describe.Lean(
                DescribeId.Create("visible-measurements-are-orthogonal-to-the-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/PurityPythagorasDecomposition."
                        + "measurement_inner_residualVector"),
                H("Every visible measurement is orthogonal to the residual"),
                StatementSource.FromAuthor(ResidualOrthogonalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a finite family of complete rank-one record measurements on "
                            + "the trace-zero Hermitian space. Assume the ranges of the "
                            + "corresponding real orthogonal projections are pairwise "
                            + "orthogonal.")),
                    Paragraph(Text(
                        "For any chosen context, projected test vector, and state, the real "
                            + "Hilbert--Schmidt inner product of that visible component with "
                            + "the state minus the sum of all visible components is zero. Thus "
                            + "the defined residual lies in the orthogonal complement of every "
                            + "visible measurement image.")),
                    Paragraph(Text(
                        "Symmetry and idempotence identify the selected context's contribution "
                            + "with its pairing against the original state, while pairwise "
                            + "orthogonality removes every cross-context contribution."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("purity-excess-splits-into-visible-and-residual-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/PurityPythagorasDecomposition."
                        + "purity_pythagoras_decomposition"),
                H("Purity excess splits into visible and residual mass"),
                StatementSource.FromAuthor(PurityDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a positive semidefinite complex matrix of trace one in "
                            + "dimension d. Centering it by the maximally mixed state produces "
                            + "a trace-zero Hermitian vector whose squared Hilbert--Schmidt norm "
                            + "is the real trace purity minus the inverse dimension.")),
                    Paragraph(Text(
                        "For each complete rank-one record context, the squared norm of its "
                            + "visible projection is the sum over outcomes of the squared Born "
                            + "probability deviations from the uniform value. Pairwise "
                            + "orthogonality makes these visible energies add without cross "
                            + "terms.")),
                    Paragraph(Text(
                        "The preceding residual-orthogonality result then gives an exact "
                            + "Pythagorean split: purity excess equals the double sum of visible "
                            + "probability energies plus the squared norm of the remaining "
                            + "component. The family need not be tomographically complete; any "
                            + "unseen mass is retained by the nonnegative residual term."))),
                DescribeRole.Theorem))));

    private static DocumentBlock AddedNode(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("purity-" + id),
            DeclarationHandle.Create("D5/S3/Quantum/Tomography/PurityPythagorasDecomposition." + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula MatrixType() => Call("Matrix", Call("Fin", X("d")), Call("Fin", X("d")), Complex());
    private static Formula Underlying(Formula value) => Seq(Parenthesized(value), Dot, D(1), Dot, D(1));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula NormSq(Formula value) => Square(new Formula.Norm(value));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula WithDimension(Formula body, bool nonzero = false) => All("d", Nat(),
        nonzero ? Seq(OpenBracket, Call("NeZero", X("d")), CloseBracket, Sp, body) : body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Projector(Formula context, Formula j) => Call("projector", context, j);
    private static Formula Measured(Formula context, Formula matrix) =>
        SumOver("j", Call("Fin", X("d")), Multiply(Multiply(Projector(context, X("j")), matrix), Projector(context, X("j"))));
    private static Formula Inner(Formula field, Formula a, Formula b) => Call("inner", field, a, b);

    private static Formula MatrixInnerTraceFormula() => Disp(WithDimension(
        All("A", MatrixType(), All("C", MatrixType(), Equal(Inner(Complex(), X("A"), X("C")),
            Call("trace", Multiply(Call("conjTranspose", X("A")), X("C"))))))));

    private static Formula HermitianTraceFormula()
    {
        var trace = Call("trace", Multiply(X("A"), X("C")));
        return Disp(WithDimension(All("A", MatrixType(), All("C", MatrixType(),
            Imp(Call("IsHermitian", X("A")), Imp(Call("IsHermitian", X("C")),
                Equal(trace, Cast(Call("re", trace), Complex()))))))));
    }

    private static Formula CenteredHermitianFormula()
    {
        var trace = Call("trace", X("H"));
        var centered = Subtract(X("H"), Call("smul", new Formula.Fraction(trace, Cast(X("d"), Complex())),
            Cast(D(1), MatrixType())));
        var norm = Subtract(Call("re", Call("trace", Multiply(X("H"), X("H")))),
            new Formula.Fraction(Square(Call("re", trace)), Cast(X("d"), Real())));
        return Disp(WithDimension(All("H", MatrixType(), Imp(Call("IsHermitian", X("H")),
            Equal(NormSq(centered), norm))), true));
    }

    private static Formula TraceZeroMeasurementFormula()
    {
        var b = X("B"); var matrix = Underlying(X("X"));
        var coordinate = Call("re", Call("trace", Multiply(matrix, Projector(b, X("j")))));
        return Disp(WithDimension(All("B", Call("RankOneContext", X("d")),
            Imp(Call("IsRecordMeasurement", Call("projector", b)),
                All("X", Call("traceZeroHermitian", X("d")), Equal(NormSq(Measured(b, matrix)),
                    SumOver("j", Call("Fin", X("d")), Square(coordinate)))))), true));
    }

    private static Formula TraceZeroPythagorasFormula()
    {
        var l = X("l"); var k = X("k"); var c = X("C"); var s = Underlying(X("s"));
        var context = new Formula.Apply(c, [l]);
        var other = new Formula.Apply(c, [k]);
        var orthogonal = All("l", X("L"), All("k", X("L"), Imp(NotEqual(l, k),
            All("x", Call("traceZeroHermitian", X("d")), All("y", Call("traceZeroHermitian", X("d")),
                Equal(Inner(Real(), Measured(context, Underlying(X("x"))), Measured(other, Underlying(X("y")))), D(0)))))));
        var measured = Measured(context, s);
        var visible = SumOver("l", X("L"), measured);
        var conclusion = Equal(NormSq(s), Add(SumOver("l", X("L"), NormSq(measured)),
            NormSq(Subtract(s, visible))));
        var body = All("C", Parenthesized(new Formula.TypeArrow(X("L"), Call("RankOneContext", X("d")))),
            Imp(All("l", X("L"), Call("IsRecordMeasurement", Call("projector", context))),
                Imp(orthogonal, All("s", Call("traceZeroHermitian", X("d")), conclusion))));
        return Disp(WithDimension(All("L", Seq(X("Type"), Star), Seq(
            OpenBracket, Call("Fintype", X("L")), CloseBracket, Sp, body)), true));
    }

    private static Formula ResidualOrthogonalityFormula()
    {
        Formula dimension = F.Id("d");
        Formula family = F.Id("C");
        Formula index = F.Id("l");
        Formula test = F.Id("x");
        Formula state = F.Id("s");
        Formula context = Call("context", family, index);
        Formula projection = Call("traceZeroBasisMeasurement", context, test);
        Formula residual = Call("residualVector", family, state);

        return Disp(Seq(
            Call("RankOneContextFamily", family, dimension), Sp, Land, Sp,
            Call("RecordMeasurements", family), Sp, Land, Sp,
            Call("PairwiseOrthogonalMeasurements", family), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, index, Comma, Sp,
            test, Comma, Sp, state, Colon, Sp,
            Call("traceZeroHermitian", dimension), Comma, Sp,
            Call("innerR", projection, residual), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula PurityDecompositionFormula()
    {
        Formula dimension = F.Id("d");
        Formula family = F.Id("C");
        Formula index = F.Id("l");
        Formula outcome = F.Id("j");
        Formula rho = Rho;
        Formula inverseDimension = new Formula.Fraction(D(1), dimension);
        Formula probability = Call(
            "basisProbability", rho, Call("context", family, index), outcome);
        Formula squaredDeviation = Seq(
            Grp(probability, Sp, Minus, Sp, inverseDimension), Caret, Grp(D(2)));
        Formula centeredState = Call("centeredDensity", rho);

        return Disp(Seq(
            Call("NormalizedDensity", rho, dimension), Sp, Land, Sp,
            Call("RecordMeasurements", family), Sp, Land, Sp,
            Call("PairwiseOrthogonalMeasurements", family), Sp, Rightarrow, RowBreak, Grp(),
            Call("ReTr", Seq(rho, Caret, Grp(D(2)))), Sp, Minus, Sp,
            inverseDimension, Sp, Eq, RowBreak, Grp(),
            Sum, Underscore, Grp(index), Sp,
            Sum, Underscore, Grp(outcome), Sp,
            squaredDeviation, Sp, Plus, Sp,
            Call("purityResidual", family, centeredState), Dot));
    }
}
