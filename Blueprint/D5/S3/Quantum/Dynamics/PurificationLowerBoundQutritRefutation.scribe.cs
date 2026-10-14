using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PurificationLowerBoundQutritRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/das2026krylovpurification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive definite qutrit state has greater time-dependent purification spread complexity than operator Krylov complexity.",
        H("The purification lower bound fails for a qutrit"), Blocks(
            Paragraph(Text(
                "The Krylov vectors are obtained by normalized Gram-Schmidt orthogonalization of successive powers of a complex continuous linear map. "
                    + "Matrix coordinates use D5.S3.Quantum.Matrix.CartesianVariance.vectorize, whose (i,j) coordinate is the (i,j) matrix entry. "
                    + "Its Euclidean inner product is the Hilbert-Schmidt inner product on matrices. Named objects retain their Lean namespaces. "
                    + "Complex.ofReal denotes the real-to-complex inclusion, and scalar multiplication uses the complex scalar action.")),
            Node("krylovVector", "Normalized Krylov vectors", KrylovFormula(),
                "Supplemental equation (S.1) gives the sequence of powers of the generator applied to the initial state. "
                    + "InnerProductSpace.gramSchmidtNormed orthogonalizes this sequence after normalizing its seed. "
                    + "For a Hermitian generator, the nonzero vectors agree with the Lanczos basis up to phases. "
                    + "Zero residuals give zero vectors, and the zero seed is included in the definition."),
            Node("spreadComplexity", "The mean Krylov index", SpreadFormula(),
                "Supplemental equations (S.2)-(S.4) express spread complexity as the mean basis index weighted by the squared moduli of the evolved amplitudes. "
                    + "The sum here ranges over Fin (Module.finrank Complex E); vectors beyond the Krylov chain contribute zero. "
                    + "NormedSpace.exp gives the evolution exp(-itL) of the normalized seed. "
                    + "This definition allows every real t and every complex continuous linear map L."),
            Node("liouvillianMatrix", "The matrix of the commutator", LiouvillianMatrixFormula(),
                "Supplemental equations (S.5)-(S.7) use the commutator with H as the operator generator. "
                    + "In system-first matrix coordinates its matrix is H tensor 1 minus 1 tensor the transpose of H. "
                    + "Matrix.kronecker denotes the Kronecker product, and each 1 is the identity matrix on Fin d."),
            Node("liouvillian", "The generator on the doubled Hilbert space", LiouvillianFormula(),
                "Matrix.toEuclideanCLM turns the commutator matrix into a continuous complex linear map on EuclideanSpace Complex (Fin d times Fin d). "
                    + "Vectorization turns [H,A] into the action of H tensor 1 minus 1 tensor the transpose of H on the vectorized A. "
                    + "For Hermitian H, its transpose is its entrywise complex conjugate H*. "
                    + "Thus exp(-itL) evolves the canonical purification by U_t tensor U_t*, with U_t = exp(-itH), as in equation (2). "
                    + "Here the star in H* and U_t* denotes entrywise complex conjugation."),
            Node("canonicalKet", "The canonical purification", CanonicalKetFormula(),
                "The purification definition before equation (1) gives, for full-rank density matrices, the canonical vector with (i,j) coefficient (sqrt rho)_{ij}. "
                    + "CFC.sqrt supplies the matrix square root, and D5.S3.Quantum.Matrix.CartesianVariance.vectorize places its entries in the doubled Hilbert space. "
                    + "For a positive semidefinite matrix of trace one, this vector has norm one and its reduced density matrix is rho. "
                    + "The displayed definition itself is made for every complex square matrix."),
            Node("operatorComplexity", "Operator Krylov complexity", OperatorComplexityFormula(),
                "Supplemental equations (S.5)-(S.11) define operator complexity using the commutator generator and the Hilbert-Schmidt-normalized initial operator. "
                    + "Vectorizing rho gives exactly that Hilbert-space calculation. "
                    + "For Hermitian rho and H, reversing the Heisenberg time sign leaves the squared Krylov amplitudes unchanged."),
            Node("purificationComplexity", "Spread complexity of the time-dependent purification", PurificationComplexityFormula(),
                "Equation (2) evolves the canonical purification with U_t tensor U_t*. "
                    + "Applying the same commutator generator to the vectorized CFC.sqrt rho therefore gives its spread complexity from supplemental equation (S.4). "
                    + "For density matrices the initial purification already has norm one."),
            Node("claim", "The left inequality of equation (4)", ClaimFormula(),
                "The left inequality of equation (4) asserts that the spread complexity of the time-dependent purification is bounded above by the mixed state's operator complexity. "
                    + "The displayed statement includes every dimension, positive definite rho of trace one, Hermitian H, and nonnegative real time. "
                    + "Positive definiteness restricts the source's density matrices to full rank, where its initial purification is the canonical one. "
                    + "A counterexample in this restricted class also disproves the source's inequality for all density matrices."),
            Describe.Lean(
                DescribeId.Create("purification-lower-bound-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A positive definite qutrit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take rho = diag(1,4,16)/21, H = [[2,1,0],[1,2,0],[0,0,4]], and t = pi/2. "
                            + "The state is positive definite with trace one, and H is Hermitian. "
                            + "Its canonical purification is (|00> + 2|11> + 4|22>)/sqrt(21).")),
                    Paragraph(Text(
                        "Both Krylov chains have length three. The squared successive off-diagonal Lanczos coefficients are "
                            + "(6/91,358/91) for the normalized vectorized density matrix and (2/21,82/21) for its canonical purification. "
                            + "On each cyclic subspace L cubed equals 4L, so at t = pi/2 the evolved seed is its initial value minus one half of L squared applied to it. "
                            + "The index-one amplitude vanishes, and the index-zero amplitudes are respectively 88/91 and 20/21.")),
                    Paragraph(Text(
                        "Consequently C_K = 2(1-(88/91)^2) = 1074/8281 and C_S = 2(1-(20/21)^2) = 82/441. "
                            + "Thus C_K < C_S, with C_S-C_K = 4192/74529 > 0, contradicting the left inequality of equation (4)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("das-mori-2026-purification-lower-bound-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("purification-lower-bound-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula KrylovFormula()
    {
        Formula sequence = Typed(
            LambdaOf("k", Naturals(), At(Power(X("L"), X("k")), Normalized(X("v")))),
            new Formula.TypeArrow(Naturals(), X("E")));
        return SpaceBinders(All("L", LinearMap(X("E")), All("v", X("E"), All("n", Naturals(),
            Equal(LocalCall("krylovVector", X("L"), X("v"), X("n")),
                At(Qualified("InnerProductSpace", "gramSchmidtNormed"), Complexes(), sequence, X("n")))))), false);
    }

    private static Formula SpreadFormula()
    {
        Formula index = At(Qualified("Fin", "val"), X("n"));
        Formula evolution = At(At(Qualified("NormedSpace", "exp"),
            Smul(Multiply(Seq(Minus, Parenthesized(At(Qualified("Complex", "ofReal"), X("t")))),
                Qualified("Complex", "I")), X("L"))), Normalized(X("v")));
        Formula amplitude = At(Qualified("inner"), Complexes(),
            LocalCall("krylovVector", X("L"), X("v"), index), evolution);
        Formula summand = Multiply(Typed(index, Reals()), At(Qualified("Complex", "normSq"), amplitude));
        return SpaceBinders(All("L", LinearMap(X("E")), All("v", X("E"), All("t", Reals(),
            Equal(LocalCall("spreadComplexity", X("L"), X("v"), X("t")),
                SumOver("n", FinOf(At(Qualified("Module", "finrank"), Complexes(), X("E"))), summand))))), true);
    }

    private static Formula LiouvillianMatrixFormula() => All("d", Naturals(), All("H", MatrixType(),
        Equal(LocalCall("liouvillianMatrix", X("H")),
            Subtract(At(Qualified("Matrix", "kronecker"), X("H"), Typed(D(1), MatrixType())),
                At(Qualified("Matrix", "kronecker"), Typed(D(1), MatrixType()),
                    At(Qualified("Matrix", "transpose"), X("H")))))));

    private static Formula LiouvillianFormula() => All("d", Naturals(), All("H", MatrixType(),
        Equal(Typed(LocalCall("liouvillian", X("H")), LinearMap(MatrixSpace())),
            At(Qualified("Matrix", "toEuclideanCLM"), LocalCall("liouvillianMatrix", X("H"))))));

    private static Formula CanonicalKetFormula() => All("d", Naturals(), All("rho", MatrixType(),
        Equal(LocalCall("canonicalKet", X("rho")),
            Vectorize(At(Qualified("CFC", "sqrt"), X("rho"))))));

    private static Formula OperatorComplexityFormula() => MatrixTimeBinders(
        Equal(LocalCall("operatorComplexity", X("H"), X("rho"), X("t")),
            LocalCall("spreadComplexity", LocalCall("liouvillian", X("H")), Vectorize(X("rho")), X("t"))));

    private static Formula PurificationComplexityFormula() => MatrixTimeBinders(
        Equal(LocalCall("purificationComplexity", X("H"), X("rho"), X("t")),
            LocalCall("spreadComplexity", LocalCall("liouvillian", X("H")),
                Vectorize(At(Qualified("CFC", "sqrt"), X("rho"))), X("t"))));

    private static Formula ClaimFormula() => Equivalence(Local("claim"),
        All("d", Naturals(), All("rho", MatrixType(), All("H", MatrixType(), All("t", Reals(),
            Imp(At(Qualified("Matrix", "PosDef"), X("rho")),
                Imp(Equal(At(Qualified("Matrix", "trace"), X("rho")), D(1)),
                    Imp(At(Qualified("Matrix", "IsHermitian"), X("H")), Imp(LE(D(0), X("t")),
                        LE(LocalCall("purificationComplexity", X("H"), X("rho"), X("t")),
                            LocalCall("operatorComplexity", X("H"), X("rho"), X("t"))))))))))));

    private static Formula SpaceBinders(Formula body, bool finiteDimensional)
    {
        Formula instances = Seq(
            OpenBracket, At(Qualified("NormedAddCommGroup"), X("E")), CloseBracket, Sp,
            OpenBracket, At(Qualified("InnerProductSpace"), Complexes(), X("E")), CloseBracket, Sp);
        if (finiteDimensional)
            instances = Seq(instances, OpenBracket,
                At(Qualified("FiniteDimensional"), Complexes(), X("E")), CloseBracket, Sp);
        return All("E", Qualified("Type"), Seq(instances, Comma, Sp, Parenthesized(body)));
    }

    private static Formula MatrixTimeBinders(Formula body) => All("d", Naturals(),
        All("H", MatrixType(), All("rho", MatrixType(), All("t", Reals(), body))));
    private static Formula Vectorize(Formula matrix) => At(Qualified("D5", "S3", "Quantum", "Matrix",
        "CartesianVariance", "vectorize"), X("d"), matrix);
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula MatrixSpace() => At(Qualified("EuclideanSpace"), Complexes(),
        Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("d")))));
    private static Formula LinearMap(Formula space) => Seq(space, Sp,
        new Formula.Subscript(To, Seq(X("L"), OpenBracket, Complexes(), CloseBracket)), Sp, space);
    private static Formula Normalized(Formula vector) => Smul(
        Power(At(Qualified("Complex", "ofReal"), new Formula.Norm(vector)), Seq(Minus, D(1))), vector);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Dynamics",
        "PurificationLowerBoundQutritRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(
        Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(
        Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
