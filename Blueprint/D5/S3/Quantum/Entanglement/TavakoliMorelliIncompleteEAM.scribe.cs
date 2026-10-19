using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TavakoliMorelliIncompleteEAMDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/tavakolimorelli2024schmidttracenorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equiangular measurements obey the Schmidt-number correlation trace-norm bound of Tavakoli and Morelli's Conjecture 2.",
        H("Schmidt-number bounds for incomplete equiangular measurements"),
        Blocks(
            Paragraph(Text(
                "All matrices have complex entries. Ket(I) is the record of a vector v : I → ℂ "
                    + "and the normalization equation Σ_i ‖v(i)‖² = 1; u.vec denotes "
                    + "the underlying vector. The trace norm is the real trace of the positive square root of X adjoint "
                    + "times X, equivalently the sum of singular values. Natural indices are "
                    + "cast into the indicated scalar field before scalar arithmetic.")),
            Node("Op", "Local operators", OperatorFormula(false),
                "Op(d) is the space of square operators on a d-dimensional local system.", DescribeRole.Definition),
            Node("BipartiteOp", "Bipartite operators", OperatorFormula(true),
                "The product index represents two local systems of the same dimension d.", DescribeRole.Definition),
            Node("proj", "The pure-state projector", ProjectorFormula(),
                "A normalized ket determines the rank-one density matrix with entries u_i times the conjugate of u_j. The outer product is the underlying matrix of its pure state.", DescribeRole.Definition),
            Node("coeff", "The coefficient matrix of a bipartite ket", CoefficientFormula(),
                "Reshaping the coordinates of a bipartite ket gives its coefficient matrix. Its rank is the Schmidt rank, and its singular values are the Schmidt coefficients.", DescribeRole.Definition),
            Node("SchmidtNumberLE", "Schmidt number at most r", SchmidtNumberFormula(),
                "Section II A defines the Schmidt number as the least positive r for which a state is a convex mixture of pure states of Schmidt rank at most r. This predicate expresses the at-most-r condition by a finite ensemble of normalized kets. The weights are nonnegative real numbers summing to one; each coefficient matrix has rank at most r. Positivity and trace one follow from the ensemble representation.", DescribeRole.Definition),
            Node("correlation", "The table of joint probabilities", CorrelationFormula(),
                "Equation (8) uses Born's rule for the joint outcome table of two local measurements. Here the entry is the real part of the trace of rho times the tensor product of the two effects, embedded into the complex numbers. The definition accepts arbitrary input matrices and finite operator families. For states and positive effects these entries are the joint probabilities.", DescribeRole.Definition),
            Node("moment", "The second moment of trace coordinates", MomentFormula(),
                "The moment sums the squared real trace coordinates of H against a finite operator family. No Hermitian hypothesis is imposed in this definition.", DescribeRole.Definition),
            Node("ScaledPure", "Nonnegative multiples of pure projectors", ScaledPureFormula(),
                "An operator is ScaledPure when it is a nonnegative real multiple of a normalized pure-state projector. The scalar zero is allowed.", DescribeRole.Definition),
            Node("MomentBound", "A uniform second-moment bound", MomentBoundFormula(),
                "For every Hermitian input, the moment is bounded by alpha times the real quadratic trace plus beta times the square of the real trace. Alpha and beta are arbitrary real parameters in this definition.", DescribeRole.Definition),
            Node("EAM", "Equiangular measurements", EAMFormula(),
                "Section V A, Eqs. (49)–(50), takes n greater than d normalized kets. Their projectors sum to n/d times the identity, and distinct kets have squared overlap (n-d)/(d(n-1)). Scaling their projectors by d/n gives measurement effects. Both the resolution of the identity and the prescribed overlap are included in the type.", DescribeRole.Definition),
            Node("EAM.effect", "The equiangular measurement effects", EffectFormula(),
                "The a-th effect is d/n times the projector of the a-th ket, as in Section V A. For positive d the effects sum to the identity.", DescribeRole.Definition),
            Node("Pn", "The EAM joint-probability table", PnFormula(),
                "The two sides choose equiangular measurements independently, with the same local dimension and number of outcomes. Pn is the n by n table formed from their effects.", DescribeRole.Definition),
            Node("traceNorm_mul_le_hsSq", "The Hilbert–Schmidt product bound", TraceNormProductFormula(),
                "For square complex matrices on any finite index type, the trace norm of their product is at most the product of their Frobenius norms. Here entryNormSq(M) is the sum of the squared absolute values of all entries of M. This is the Hilbert–Schmidt Hölder inequality, and it includes the empty index type.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo()),
            Node("ket_dot_self", "Normalization as a conjugate dot product", KetDotFormula(),
                "The conjugate dot product of a normalized ket with itself equals one, in the complex field.", DescribeRole.Theorem),
            Node("proj_eq_outer", "The projector as an outer product", ProjectorFormula(),
                "The pure-state matrix equals the outer product of the ket and its complex conjugate. This identifies its entries with the coordinates used in matrix factorization.", DescribeRole.Theorem),
            Node("scaledPure_hermitian", "Scaled pure projectors are Hermitian", ScaledHermitianFormula(),
                "A pure projector is Hermitian, and multiplication by a real scalar preserves Hermiticity.", DescribeRole.Theorem),
            Node("scaledPure_sandwich", "Compression by a scaled pure projector", ScaledSandwichFormula(),
                "Sandwiching an arbitrary operator M between two copies of a scaled pure projector multiplies that projector by the trace of M times the projector. The trace is complex and no Hermitian hypothesis on M is required.", DescribeRole.Theorem),
            Node("proj_overlap", "Trace overlap of two pure projectors", ProjectorOverlapFormula(),
                "The trace of the product of two pure projectors is the squared absolute overlap of their normalized kets, regarded as a complex number.", DescribeRole.Theorem),
            Node("schmidt_traceNorm_le_of_moment", "From second moments to a Schmidt-number bound", SchmidtBoundFormula(),
                "Two finite families of nonnegative multiples of pure projectors with the same nonnegative second-moment coefficients alpha and beta give a correlation table of trace norm at most alpha plus beta r on every state of Schmidt number at most r. The index type and the dimensions may be empty; this general statement adds no positivity assumptions on d or r.", DescribeRole.Theorem),
            Node("claim", "Tavakoli–Morelli Conjecture 2", ClaimFormula(),
                "Section V A, Conjecture 2, Eq. (52), asserts the displayed bound for a state of Schmidt number r. Since the bound increases with r, the statement uses Schmidt number at most r. It includes every positive local dimension, every r from one to d, and every pair of equiangular measurements with the same n greater than d. All subtractions in the bound are real subtractions.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("tavakoli-morelli-eam-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The equiangular Schmidt-number bound"),
                StatementSource.FromAuthor(Disp(X("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a pure ket, write its coefficient matrix as U D V adjoint by the singular value decomposition, with D diagonal and nonnegative. Put S equal to the positive square root of D. The correlation table factors as F adjoint times G, whose columns are the vectorizations of S U adjoint A_a U S and S V adjoint transpose(B_b) V S. The Hilbert–Schmidt Hölder inequality bounds its trace norm by the product of the two Frobenius norms. For rank-one effects, the squared Frobenius norms are the second moments of the corresponding Hermitian weight matrices.")),
                    Paragraph(Text(
                        "The equiangular Gram matrix and Cauchy–Schwarz give, for every Hermitian H, the second-moment bound with coefficients alpha = d(d-1)/(n(n-1)) and beta = (n-d)/(n(n-1)). For each weight matrix the quadratic trace is the sum of squared Schmidt coefficients, equal to one, while the squared trace is (sum of Schmidt coefficients) squared, at most r by Cauchy–Schwarz on their at most r nonzero entries. Thus the pure-state bound is alpha plus beta r. Real linearity of the probability table, the trace-norm triangle inequality, and homogeneity for nonnegative weights extend the bound to convex mixtures. Substitution of alpha and beta yields claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tavakoli-morelli-2024-conjecture-2-incomplete-eam-schmidt-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("tavakoli-morelli-eam-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + (name == "EAM.effect" ? "effect" : name)), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Cast(X(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(F.Exists, Sp, Cast(X(name), type), Comma, Sp, body);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Instances(Formula body, params Formula[] types)
    {
        for (var i = types.Length - 1; i >= 0; i--)
            body = Seq(OpenBracket, types[i], CloseBracket, Sp, body);
        return body;
    }
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Type() => Seq(X("Type"), Star);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula PairType(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Pairs(Formula d) => PairType(Fin(d), Fin(d));
    private static Formula MatrixType(Formula i) => Call("Matrix", i, i, Complex());
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Field(Formula value, string name) => Seq(Parenthesized(value), Dot, X(name));
    private static Formula Effect(Formula a) => Field(a, "effect");
    private static Formula Vec(Formula u) => Field(u, "vec");
    private static Formula Tr(Formula a) => Call("trace", a);
    private static Formula RePart(Formula a) => Call("re", a);
    private static Formula Hermitian(Formula a) => Call("IsHermitian", a);
    private static Formula Smul(Formula c, Formula a) => Call("smul", c, a);
    private static Formula Square(Formula a) => new Formula.Power(Parenthesized(a), D(2));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula LambdaOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Cast(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Dim(Formula body) => All("d", Nat(), body);
    private static Formula FiniteIndex(Formula body, bool decidable = false) => All("I", Type(),
        decidable ? Instances(body, Call("Fintype", X("I")), Call("DecidableEq", X("I")))
            : Instances(body, Call("Fintype", X("I"))));
    private static Formula Families(Formula body) => All("A", Arrow(X("I"), Call("Op", X("d"))),
        All("B", Arrow(X("I"), Call("Op", X("d"))), body));
    private static Formula EAMInputs(Formula body) => Dim(All("n", Nat(),
        All("A", Call("EAM", X("d"), X("n")), body)));

    private static Formula OperatorFormula(bool bipartite) => Disp(Dim(Equal(
        Call(bipartite ? "BipartiteOp" : "Op", X("d")), MatrixType(bipartite ? Pairs(X("d")) : Fin(X("d"))))));

    private static Formula ProjectorFormula() => Disp(FiniteIndex(All("u", Call("Ket", X("I")),
        Equal(Call("proj", X("u")), Call("vecMulVec", Vec(X("u")), Call("star", Vec(X("u")))))), true));

    private static Formula CoefficientFormula() => Disp(Dim(All("u", Call("Ket", Pairs(X("d"))),
        Equal(Call("coeff", X("u")), LambdaOver("i", Fin(X("d")), LambdaOver("j", Fin(X("d")),
            At(Vec(X("u")), Parenthesized(Seq(X("i"), Comma, Sp, X("j"))))))))));

    private static Formula SchmidtNumberFormula()
    {
        var rank = Call("rank", Call("coeff", At(X("u"), X("k"))));
        var mixture = SumOver("k", Fin(X("N")), Smul(Cast(At(X("p"), X("k")), Complex()),
            Call("proj", At(X("u"), X("k")))));
        var body = Some("N", Nat(), Some("p", Arrow(Fin(X("N")), Real()),
            Some("u", Arrow(Fin(X("N")), Call("Ket", Pairs(X("d")))),
                And(All("k", Fin(X("N")), Leq(D(0), At(X("p"), X("k")))),
                    And(Equal(SumOver("k", Fin(X("N")), At(X("p"), X("k"))), D(1)),
                        And(All("k", Fin(X("N")), Leq(rank, X("r"))), Equal(X("rho"), mixture)))))));
        return Disp(Dim(All("rho", Call("BipartiteOp", X("d")), All("r", Nat(),
            Iff(Call("SchmidtNumberLE", X("rho"), X("r")), body)))));
    }

    private static Formula CorrelationFormula()
    {
        var value = Cast(RePart(Tr(Mul(X("rho"), Call("kronecker", At(X("A"), X("a")),
            At(X("B"), X("b")))))), Complex());
        return Disp(Dim(FiniteIndex(All("rho", Call("BipartiteOp", X("d")), Families(
            Equal(Call("correlation", X("rho"), X("A"), X("B")),
                LambdaOver("a", X("I"), LambdaOver("b", X("I"), value))))))));
    }

    private static Formula MomentFormula() => Disp(Dim(FiniteIndex(
        All("A", Arrow(X("I"), Call("Op", X("d"))), All("H", Call("Op", X("d")),
            Equal(Call("moment", X("A"), X("H")), SumOver("a", X("I"),
                Square(RePart(Tr(Mul(X("H"), At(X("A"), X("a")))))))))))));

    private static Formula ScaledPureFormula() => Disp(Dim(All("A", Call("Op", X("d")),
        Iff(Call("ScaledPure", X("A")), Some("c", Real(), Some("u", Call("Ket", Fin(X("d"))),
            And(Leq(D(0), X("c")), Equal(X("A"), Smul(Cast(X("c"), Complex()), Call("proj", X("u")))))))))));

    private static Formula MomentBoundFormula()
    {
        var bound = Add(Mul(X("alpha"), RePart(Tr(Mul(X("H"), X("H"))))),
            Mul(X("beta"), Square(RePart(Tr(X("H"))))));
        return Disp(Dim(FiniteIndex(All("A", Arrow(X("I"), Call("Op", X("d"))),
            All("alpha", Real(), All("beta", Real(), Iff(Call("MomentBound", X("A"), X("alpha"), X("beta")),
                All("H", Call("Op", X("d")), Imp(Hermitian(X("H")), Leq(Call("moment", X("A"), X("H")), bound))))))))));
    }

    private static Formula EAMFormula()
    {
        var d = Cast(X("d"), Real()); var n = Cast(X("n"), Real());
        var overlap = Square(new Formula.Norm(Call("dotProduct", Call("star", Vec(At(X("u"), X("a")))),
            Vec(At(X("u"), X("b"))))));
        var conditions = And(Less(X("d"), X("n")), And(
            Equal(SumOver("a", Fin(X("n")), Call("proj", At(X("u"), X("a")))),
                Smul(new Formula.Fraction(Cast(X("n"), Complex()), Cast(X("d"), Complex())),
                    Cast(D(1), Call("Op", X("d"))))),
            All("a", Fin(X("n")), All("b", Fin(X("n")), Imp(NotEqual(X("a"), X("b")),
                Equal(overlap, new Formula.Fraction(Sub(n, d), Mul(d, Parenthesized(Sub(n, D(1)))))))))));
        return Disp(Dim(All("n", Nat(), Equal(Call("EAM", X("d"), X("n")),
            SetOf("u", Arrow(Fin(X("n")), Call("Ket", Fin(X("d")))), conditions)))));
    }

    private static Formula EffectFormula() => Disp(EAMInputs(All("a", Fin(X("n")),
        Equal(At(Effect(X("A")), X("a")), Smul(new Formula.Fraction(Cast(X("d"), Complex()), Cast(X("n"), Complex())),
            Call("proj", At(Field(X("A"), "val"), X("a"))))))));

    private static Formula PnFormula() => Disp(Dim(All("n", Nat(),
        All("rho", Call("BipartiteOp", X("d")), All("A", Call("EAM", X("d"), X("n")),
            All("B", Call("EAM", X("d"), X("n")), Equal(Call("Pn", X("rho"), X("A"), X("B")),
                Call("correlation", X("rho"), Effect(X("A")), Effect(X("B"))))))))));

    private static Formula KetDotFormula() => Disp(FiniteIndex(All("u", Call("Ket", X("I")),
        Equal(Call("dotProduct", Call("star", Vec(X("u"))), Vec(X("u"))), Cast(D(1), Complex())))));

    private static Formula ScaledHermitianFormula() => Disp(Dim(All("A", Call("Op", X("d")),
        Imp(Call("ScaledPure", X("A")), Hermitian(X("A"))))));

    private static Formula ScaledSandwichFormula() => Disp(Dim(All("A", Call("Op", X("d")),
        Imp(Call("ScaledPure", X("A")), All("M", Call("Op", X("d")),
            Equal(Mul(Mul(X("A"), X("M")), X("A")), Smul(Tr(Mul(X("M"), X("A"))), X("A"))))))));

    private static Formula ProjectorOverlapFormula() => Disp(Dim(All("u", Call("Ket", Fin(X("d"))),
        All("v", Call("Ket", Fin(X("d"))), Equal(Tr(Mul(Call("proj", X("u")), Call("proj", X("v")))),
            Cast(Square(new Formula.Norm(Call("dotProduct", Call("star", Vec(X("u"))), Vec(X("v"))))), Complex()))))));

    private static Formula SchmidtBoundFormula()
    {
        var conclusion = Leq(Call("traceNorm", Call("correlation", X("rho"), X("A"), X("B"))),
            Add(X("alpha"), Mul(X("beta"), Cast(X("r"), Real()))));
        var body = Imp(All("a", X("I"), Call("ScaledPure", At(X("A"), X("a")))),
            Imp(All("b", X("I"), Call("ScaledPure", At(X("B"), X("b")))),
                Imp(Leq(D(0), X("alpha")), Imp(Leq(D(0), X("beta")),
                    Imp(Call("MomentBound", X("A"), X("alpha"), X("beta")),
                        Imp(Call("MomentBound", X("B"), X("alpha"), X("beta")),
                            Imp(Call("SchmidtNumberLE", X("rho"), X("r")), conclusion)))))));
        return Disp(Dim(All("r", Nat(), FiniteIndex(All("rho", Call("BipartiteOp", X("d")),
            Families(All("alpha", Real(), All("beta", Real(), body))))))));
    }

    private static Formula ClaimFormula()
    {
        var d = Cast(X("d"), Real()); var n = Cast(X("n"), Real()); var r = Cast(X("r"), Real());
        var numerator = Add(Mul(d, Parenthesized(Sub(d, D(1)))), Mul(r, Parenthesized(Sub(n, d))));
        var bound = new Formula.Fraction(numerator, Mul(n, Parenthesized(Sub(n, D(1)))));
        var body = Dim(All("n", Nat(), All("r", Nat(), Imp(Leq(D(1), X("d")),
            Imp(Leq(D(1), X("r")), Imp(Leq(X("r"), X("d")),
                All("A", Call("EAM", X("d"), X("n")), All("B", Call("EAM", X("d"), X("n")),
                    All("rho", Call("BipartiteOp", X("d")), Imp(Call("SchmidtNumberLE", X("rho"), X("r")),
                        Leq(Call("traceNorm", Call("Pn", X("rho"), X("A"), X("B"))), bound)))))))))));
        return Disp(Iff(X("claim"), body));
    }

    private static Formula TraceNormProductFormula()
    {
        var matrix = MatrixType(X("K"));
        var bound = Mul(Seq(Sqrt, Grp(Call("entryNormSq", X("R")))),
            Seq(Sqrt, Grp(Call("entryNormSq", X("S")))));
        return Disp(All("K", Type(), Instances(All("R", matrix, All("S", matrix,
            Leq(Call("traceNorm", Mul(X("R"), X("S"))), bound))), Call("Fintype", X("K")))));
    }
}
