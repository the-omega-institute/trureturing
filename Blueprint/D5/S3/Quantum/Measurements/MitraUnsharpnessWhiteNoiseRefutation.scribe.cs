using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class MitraUnsharpnessWhiteNoiseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation.";
    private const string Povm =
        "D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/mitra2022unsharpness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-outcome diagonal qubit observable contradicts the first inequality in Mitra's white-noise conjecture.",
        H("Mitra's white-noise conjecture for qubit observables"), Blocks(
            Paragraph(Text(
                "A qubit observable is a finite family of positive semidefinite complex two-by-two matrices summing to the identity. "
                    + "The predicate D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM has the following meaning:")),
            new DocumentBlock.DisplayFormula(PovmFormula()),
            Paragraph(Text(
                "All outcome indices are zero-based Fin indices. The numeral one of matrix type is the identity matrix. "
                    + "A centered dot with a real left operand denotes real scalar multiplication; a star denotes matrix multiplication. "
                    + "The notation (n : ℝ) denotes the cast from ℕ to ℝ, and every displayed quotient is real division. "
                    + "The definitions of the quantities below allow n = 0; the conjecture requires n ≥ 1.")),
            Node("opNorm", "The Euclidean operator norm", OpNormFormula(),
                "Section IV uses the operator norm. Matrix.toEuclideanCLM here has scalar field ℂ and index type Fin 2; its norm is the continuous-linear-map norm induced by the Euclidean norm on ℂ².",
                AssessedProvenance.FromLiterature(Source)),
            Node("X", "The norm-weighted matrix", XFormula(),
                "Section IV.A defines the X-matrix as the sum of each effect multiplied by its operator norm. The same matrix appears in equation (51).",
                AssessedProvenance.FromLiterature(Source)),
            Node("xMin", "The lowest Hermitian eigenvalue", XMinFormula(),
                "Theorem 3 uses the lowest eigenvalue of the Hermitian X-matrix. For any Hermitian two-by-two matrix M, the minimum of its two Matrix.IsHermitian.eigenvalues is its lowest eigenvalue. The Hermitian proof argument hM of xMin is not displayed in the application xMin(M); it is retained in the eigenvalue applications. No ordering of the two eigenvalue indices is assumed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sigma1", "The first spectral quantity", Sigma1Formula(),
                "Theorem 3, equation (50), defines Σ₁ as the lowest eigenvalue of the X-matrix minus 1/n. The proof argument hA of sigma1 is displayed in its application; the Hermitian proof argument of xMin is not displayed. The matrix passed to xMin is X(A).",
                AssessedProvenance.FromLiterature(Source)),
            Node("sigma2", "The second spectral quantity", Sigma2Formula(),
                "Theorem 3, equation (50), defines Σ₂ as the mean effect norm minus the lowest eigenvalue of the X-matrix. The proof argument hA of sigma2 is displayed in its application; the Hermitian proof argument of xMin is not displayed. The matrix passed to xMin is X(A).",
                AssessedProvenance.FromLiterature(Source)),
            Node("sigma1Prime", "The first trace quantity", Sigma1PrimeFormula(),
                "Theorem 4, equation (60), defines Σ′₁ using the normalized trace. In dimension two this is the real part of Matrix.trace of X(A), divided by two, minus 1/n. This definition places no positivity assumption on A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sigma2Prime", "The second trace quantity", Sigma2PrimeFormula(),
                "Theorem 4, equation (60), defines Σ′₂ as the mean effect norm minus the normalized trace of X(A). The displayed real part is Complex.re. This definition places no positivity assumption on A.",
                AssessedProvenance.FromLiterature(Source)),
            Node("E", "Operator-norm unsharpness", EFormula(),
                "Section IV.A, equation (44), gives the unsharpness as the operator norm of the identity minus the X-matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Node("EPrime", "Normalized-trace unsharpness", EPrimeFormula(),
                "Section IV.A, equation (48), gives the trace of (I/d)(I − X). Here d = 2, the factor 1/2 acts on the identity by real scalar multiplication, and Complex.re takes the real part of the trace of the matrix product.",
                AssessedProvenance.FromLiterature(Source)),
            Node("noisy", "Adding white noise", NoisyFormula(),
                "Theorems 3 and 4 use the mixture λAᵢ + (1 − λ)I/n. The definition accepts every real l; the conjecture restricts l to Set.Icc 0 1, the closed real interval from zero to one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Section IV.B, page 11, Conjecture 1 states: For any qubit observable A, inequality Σ₁ ≥ Σ₂ and inequality Σ′₁ ≥ Σ′₂ hold and therefore, E(A^λ) ≥ E(A) and E′(A^λ) ≥ E′(A) for all 1 ≥ λ ≥ 0. The formula retains all four assertions, for every n ≥ 1 and every qubit observable, without a diagonal or distinctness condition. The proof argument hA of sigma1 and sigma2 is displayed in their applications. Theorems 3 and 4 explain the two inequalities used by the conjecture; their equivalences are not asserted here.",
                AssessedProvenance.FromLiterature(Source)),
            Node("diag2", "A real diagonal complex matrix", Diag2Formula(),
                "The two real entries are embedded in ℂ before Matrix.diagonal forms the matrix. This construction supplies diagonal observables for the quantities in Section IV.",
                AssessedProvenance.FromRepo(Source)),
            Node("witness", "Four diagonal effects", WitnessFormula(),
                "The four effects, in outcome order, have diagonal entries (12/40, 1/40), (13/40, 1/40), (14/40, 1/40), and (1/40, 37/40). They are positive semidefinite and sum to the identity, so they form a qubit observable to which Conjecture 1 applies.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("mitra-white-noise-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal conjecture is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the four diagonal effects above, the operator norms are 12/40, 13/40, 14/40, and 37/40, "
                        + "with sum 19/10. Their X-matrix has diagonal entries 273/800 and 704/800, so its lowest eigenvalue is 273/800. "
                        + "Consequently Σ₁ = 73/800 < Σ₂ = 107/800. The first inequality in Conjecture 1 fails, which refutes the conjunction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mitra-2022-unsharpness-white-noise-monotonicity-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("mitra-white-noise-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PovmFormula() => FamilyBinders(Equivalence(Call(Povm, V("A")),
        And(All("i", Fin(V("n")), Call("Matrix.PosSemidef", At(V("A"), V("i")))),
            Equal(SumOver("i", Fin(V("n")), At(V("A"), V("i"))), One()))));

    private static Formula OpNormFormula() => All("M", Mat(),
        Equal(Typed(LocalCall("opNorm", V("M")), Reals()),
            new Formula.Norm(Call("Matrix.toEuclideanCLM", V("M")))));

    private static Formula XFormula() => FamilyBinders(
        Equal(Typed(LocalCall("X", V("A")), Mat()),
            SumOver("i", Fin(V("n")), Scalar(
                LocalCall("opNorm", At(V("A"), V("i"))), At(V("A"), V("i"))))));

    private static Formula XMinFormula() => All("M", Mat(),
        All("hM", Call("Matrix.IsHermitian", V("M")),
            Equal(Typed(LocalCall("xMin", V("M")), Reals()),
                Call("min", Call("Matrix.IsHermitian.eigenvalues", V("hM"), D(0)),
                    Call("Matrix.IsHermitian.eigenvalues", V("hM"), D(1))))));

    private static Formula Sigma1Formula() => ObservableBinders(
        Equal(Typed(LocalCall("sigma1", V("A"), V("hA")), Reals()),
            Subtract(LocalCall("xMin", LocalCall("X", V("A"))), Quotient(D(1), RealN()))));

    private static Formula Sigma2Formula() => ObservableBinders(
        Equal(Typed(LocalCall("sigma2", V("A"), V("hA")), Reals()),
            Subtract(Quotient(NormSum(), RealN()), LocalCall("xMin", LocalCall("X", V("A"))))));

    private static Formula Sigma1PrimeFormula() => FamilyBinders(
        Equal(Typed(LocalCall("sigma1Prime", V("A")), Reals()),
            Subtract(Quotient(RealTrace(LocalCall("X", V("A"))), D(2)), Quotient(D(1), RealN()))));

    private static Formula Sigma2PrimeFormula() => FamilyBinders(
        Equal(Typed(LocalCall("sigma2Prime", V("A")), Reals()),
            Subtract(Quotient(NormSum(), RealN()), Quotient(RealTrace(LocalCall("X", V("A"))), D(2)))));

    private static Formula EFormula() => FamilyBinders(
        Equal(Typed(LocalCall("E", V("A")), Reals()),
            LocalCall("opNorm", Subtract(One(), LocalCall("X", V("A"))))));

    private static Formula EPrimeFormula() => FamilyBinders(
        Equal(Typed(LocalCall("EPrime", V("A")), Reals()),
            RealTrace(MatrixProduct(Scalar(Typed(Quotient(D(1), D(2)), Reals()), One()),
                Subtract(One(), LocalCall("X", V("A")))))));

    private static Formula NoisyFormula() => FamilyBinders(All("l", Reals(),
        Equal(Typed(LocalCall("noisy", V("A"), V("l")), Family()),
            LambdaOf("i", Fin(V("n")), Add(Scalar(V("l"), At(V("A"), V("i"))),
                Scalar(Quotient(Subtract(D(1), V("l")), RealN()), One()))))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"), All("n", Naturals(),
        Imp(LE(D(1), V("n")), All("A", Family(), All("hA", Call(Povm, V("A")),
            And(LE(LocalCall("sigma2", V("A"), V("hA")), LocalCall("sigma1", V("A"), V("hA"))),
                And(LE(LocalCall("sigma2Prime", V("A")), LocalCall("sigma1Prime", V("A"))),
                    And(NoiseComparison("E"), NoiseComparison("EPrime")))))))));

    private static Formula NoiseComparison(string name) => All("l", Reals(),
        Imp(Member(V("l"), Call("Set.Icc", Typed(D(0), Reals()), D(1))),
            LE(LocalCall(name, V("A")), LocalCall(name, LocalCall("noisy", V("A"), V("l"))))));

    private static Formula Diag2Formula() => All("u", Reals(), All("v", Reals(),
        Equal(Typed(LocalCall("diag2", V("u"), V("v")), Mat()),
            Call("Matrix.diagonal", Vector(Typed(V("u"), Complexes()), Typed(V("v"), Complexes()))))));

    private static Formula WitnessFormula() => Equal(
        Typed(Local("witness"), Parenthesized(Arrow(Fin(D(4)), Mat()))),
        Vector(LocalCall("diag2", Ratio(1, 2, 4, 0), Ratio(1, 4, 0)),
            LocalCall("diag2", Ratio(1, 3, 4, 0), Ratio(1, 4, 0)),
            LocalCall("diag2", Ratio(1, 4, 4, 0), Ratio(1, 4, 0)),
            LocalCall("diag2", Ratio(1, 4, 0), Ratio(3, 7, 4, 0))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5.S3.Quantum.Measurements.MitraUnsharpnessWhiteNoiseRefutation." + name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Mat() => Call("Matrix", Fin(D(2)), Fin(D(2)), Complexes());
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Family() => Parenthesized(Arrow(Fin(V("n")), Mat()));
    private static Formula One() => Typed(D(1), Mat());
    private static Formula RealN() => Typed(V("n"), Reals());
    private static Formula RealTrace(Formula matrix) => Call("Complex.re", Call("Matrix.trace", matrix));
    private static Formula NormSum() => SumOver("i", Fin(V("n")), LocalCall("opNorm", At(V("A"), V("i"))));
    private static Formula Quotient(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Ratio(byte numerator, byte tens, byte units) =>
        Typed(Quotient(D(numerator), D(tens, units)), Reals());
    private static Formula Ratio(byte tens, byte units, byte denominatorTens, byte denominatorUnits) =>
        Typed(Quotient(D(tens, units), D(denominatorTens, denominatorUnits)), Reals());
    private static Formula Vector(params Formula[] entries) => Seq(Bang, OpenBracket,
        Seq([.. entries.SelectMany((entry, index) => index == 0
            ? new[] { entry } : new[] { Comma, Sp, entry })]), CloseBracket);
    private static Formula FamilyBinders(Formula body) => All("n", Naturals(), All("A", Family(), body));
    private static Formula ObservableBinders(Formula body) => FamilyBinders(All("hA", Call(Povm, V("A")), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Scalar(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula MatrixProduct(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Star, Sp, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
