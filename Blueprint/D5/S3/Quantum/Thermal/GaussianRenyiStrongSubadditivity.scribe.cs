using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class GaussianRenyiStrongSubadditivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/camilolandieliens2019renyissa");

    private static Formula X(string name) => name switch
    {
        "α" => Alpha, "ι" => Iota, "ω" => Omega,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Local(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula PairType(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Times, Sp, Parenthesized(right));
    private static Formula Indices => PairType(FinOf(X("n")), FinOf(D(2)));
    private static Formula MatrixOf(Formula indices, Formula scalars) => At(Qualified("Matrix"), indices, indices, scalars);
    private static Formula ModeMatrix => MatrixOf(Indices, Reals);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula GenericIndices(Formula body) => All("ι", Qualified("Type"),
        Instance(At(Qualified("Fintype"), Iota), Instance(At(Qualified("DecidableEq"), Iota), body)));
    private static Formula GenericMatrices(Formula body) => GenericIndices(
        All("V", MatrixOf(Iota, Reals), All("ω", MatrixOf(Iota, Reals), body)));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula RealMatrixInComplexes(Formula value) => At(Qualified("Matrix", "map"), value, Qualified("Complex", "ofReal"));
    private static Formula Submatrix(Formula matrix, Formula rows, Formula columns) => At(Qualified("Matrix", "submatrix"), matrix, rows, columns);
    private static Formula ToFunction(Formula equivalence) => At(Qualified("Equiv", "toFun"), equivalence);
    private static Formula Trans(Formula first, Formula second) => At(Qualified("Equiv", "trans"), first, second);
    private static Formula CanonicalEquivalence => Trans(
        Trans(At(Qualified("Equiv", "prodComm"), FinOf(X("n")), FinOf(D(2))),
            At(Qualified("Equiv", "prodCongr"), Qualified("finTwoEquiv"), At(Qualified("Equiv", "refl"), FinOf(X("n"))))),
        At(Qualified("Equiv", "boolProdEquivSum"), FinOf(X("n"))));
    private static Formula SymplecticDefinition() => All("n", Naturals,
        Equal(Typed(Local("symplecticForm", X("n")), ModeMatrix), Seq(
            Qualified("let"), Sp, X("e"), Colon, Eq, Sp, CanonicalEquivalence, Semi, Sp,
            Submatrix(Negate(At(Qualified("Matrix", "J"), FinOf(X("n")), Reals)), ToFunction(X("e")), ToFunction(X("e"))))));
    private static Formula PhysicalOnDefinition() => GenericMatrices(
        Equal(Local("physicalOn", X("V"), Omega), And(At(Qualified("Matrix", "IsSymm"), X("V")),
            At(Qualified("Matrix", "PosSemidef"), Add(RealMatrixInComplexes(X("V")),
                Smul(Qualified("Complex", "I"), RealMatrixInComplexes(Omega)))))));
    private static Formula CovarianceDefinition()
    {
        Formula equivalence = Trans(At(Qualified("finCongr"), At(Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id("mul"), Underscore, Grp(F.Id("comm")))), D(2), X("n"))),
            At(Qualified("Equiv", "symm"), At(Qualified("finProdFinEquiv"), X("n"), D(2))));
        Formula reordered = Submatrix(X("V"), ToFunction(equivalence), ToFunction(equivalence));
        return All("n", Naturals, All("V", ModeMatrix,
            Equal(Local("physicalCovariance", X("V")), At(Qualified("D5", "S3", "Estimation",
                "GaussianThermometryJointMeasurementRefutation", "IsGaussianMeasurementCov"), reordered))));
    }
    private static Formula ReducedIndices(string name) => At(Qualified("Subtype"), LambdaOf(name, Indices,
        Member(At(Qualified("Prod", "fst"), X(name)), X("X"))));
    private static Formula ReductionDefinition()
    {
        Formula projection = LambdaOf("p", ReducedIndices("q"), At(Qualified("Subtype", "val"), X("p")));
        return All("n", Naturals, All("V", ModeMatrix, All("X", At(Qualified("Finset"), FinOf(X("n"))),
            Equal(Typed(Local("reducedCovariance", X("V"), X("X")), MatrixOf(ReducedIndices("p"), Reals)),
                Submatrix(X("V"), projection, projection)))));
    }
    private static Formula OperatorDefinition()
    {
        Formula squareRoot = At(Qualified("CFC", "sqrt"), RealMatrixInComplexes(X("V")));
        return GenericMatrices(Equal(Typed(Local("symplecticOperator", X("V"), Omega), MatrixOf(Iota, Complexes)),
            Mul(Mul(squareRoot, Smul(Qualified("Complex", "I"), RealMatrixInComplexes(Omega))), squareRoot)));
    }
    private static Formula EntropyDefinition()
    {
        Formula condition = At(Qualified("Matrix", "IsHermitian"), Local("symplecticOperator", X("V"), Omega));
        Formula eigenvalue = At(Qualified("Matrix", "IsHermitian", "eigenvalues"), X("h"), X("i"));
        Formula summand = At(Qualified("D5", "S3", "Quantum", "Analysis", "BosonicRenyiStieltjes", "renyiFunction"),
            Alpha, new Formula.Absolute(eigenvalue));
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(X("i"), Colon, Sp, Iota)), Sp, Parenthesized(summand));
        Formula half = Typed(new Formula.Fraction(D(1), D(2)), Reals);
        Formula conditional = At(Qualified("dite"), condition,
            LambdaOf("h", condition, Mul(half, sum)),
            At(Qualified("Function", "const"), new Formula.Not(Parenthesized(condition)), Typed(D(0), Reals)));
        return GenericIndices(All("α", Reals, All("V", MatrixOf(Iota, Reals), All("ω", MatrixOf(Iota, Reals),
            Equal(Typed(Local("gaussianRenyiEntropy", Alpha, X("V"), Omega), Reals), conditional)))));
    }
    private static Formula Union(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cup, Sp, Parenthesized(right));
    private static Formula EntropyOn(Formula modes) => Local("gaussianRenyiEntropy", Alpha,
        Local("reducedCovariance", X("V"), modes), Local("reducedCovariance", Local("symplecticForm", X("n")), modes));
    private static Formula ClaimFormula()
    {
        Formula A = X("A");
        Formula B = X("B");
        Formula C = X("C");
        Formula modeSets = At(Qualified("Finset"), FinOf(X("n")));
        Formula inequality = new Formula.Relation(Add(EntropyOn(Union(A, B)), EntropyOn(Union(B, C))),
            FormulaRelationOperator.GreaterThanOrEqual, Add(EntropyOn(Union(Union(A, B), C)), EntropyOn(B)));
        Formula orders = All("α", Reals, Imp(LT(D(0), Alpha), Imp(LE(Alpha, D(2)), Imp(NE(Alpha, D(1)), inequality))));
        return All("n", Naturals, All("V", ModeMatrix, Imp(Local("physicalCovariance", X("V")),
            All("A", modeSets, All("B", modeSets, All("C", modeSets,
                Imp(At(Qualified("Disjoint"), A, B), Imp(At(Qualified("Disjoint"), A, C),
                    Imp(At(Qualified("Disjoint"), B, C), orders)))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bosonic Gaussian Renyi entropy satisfies strong subadditivity for every order from zero to two, with zero and one excluded.",
        H("Strong subadditivity of bosonic Gaussian Renyi entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symplectic-form"), DeclarationHandle.Create(Module + ".symplecticForm"),
                H("The canonical symplectic form"), StatementSource.FromAuthor(Disp(SymplecticDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The quadrature indices are pairs in Fin n × Fin 2. Reindexing the negative standard symplectic matrix by e gives the direct sum of n copies of the matrix with rows (0,1) and (−1,0). This is the form in the bosonic commutation relations of RenyiGaussian_v2.tex, lines 179–186."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-on"), DeclarationHandle.Create(Module + ".physicalOn"),
                H("The uncertainty condition on a finite index type"), StatementSource.FromAuthor(Disp(PhysicalOnDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary finite indices, V must be real symmetric and V+iω must be positive semidefinite. With the canonical symplectic form this is the bosonic uncertainty condition. The source writes V−iΩ in RenyiGaussian_v2.tex, lines 194–198, with Ω for the matrix ω here; for real V and ω, complex conjugation makes the two sign conventions equivalent."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-covariance"), DeclarationHandle.Create(Module + ".physicalCovariance"),
                H("Physical bosonic covariances"), StatementSource.FromAuthor(Disp(CovarianceDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The covariance is reindexed from mode–quadrature pairs to Fin (2*n) and tested by IsGaussianMeasurementCov. The index permutation identifies its uncertainty matrix with V+i symplecticForm(n), so this is the same bona fide covariance condition in RenyiGaussian_v2.tex, lines 188–198."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-covariance"), DeclarationHandle.Create(Module + ".reducedCovariance"),
                H("Reduction to a set of modes"), StatementSource.FromAuthor(Disp(ReductionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite set X of modes, retain both quadratures of each member of X. The reduced covariance is the principal submatrix on these indices. The same restriction applies to the symplectic form. These are the covariance reductions used for the subsystem entropies in Eq. RCMI (RenyiGaussian_v2.tex, lines 122–125)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symplectic-operator"), DeclarationHandle.Create(Module + ".symplecticOperator"),
                H("The Hermitian representative of the symplectic spectrum"), StatementSource.FromAuthor(Disp(OperatorDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Embed the real matrices into complex matrices and place iω between two copies of the positive square root of V. For a physical covariance the resulting matrix is Hermitian and has the spectrum of iωV. Its eigenvalues have absolute value at least one. This represents the symplectic eigenvalues described in RenyiGaussian_v2.tex, lines 201–205."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussian-renyi-entropy"), DeclarationHandle.Create(Module + ".gaussianRenyiEntropy"),
                H("Entropy from the symplectic eigenvalues"), StatementSource.FromAuthor(Disp(EntropyDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("When the symplectic operator is Hermitian, sum renyiFunction over the absolute values of all its eigenvalues and divide by two, accounting for the two signs of each symplectic eigenvalue. This gives Eq. renyi_bosonic_1 (RenyiGaussian_v2.tex, lines 216–220). The definition assigns zero in the non-Hermitian case. Empty mode sets also give zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("Strong subadditivity for the stated orders"),
                StatementSource.FromAuthor(Disp(Equal(Qualified("claim"), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every physical bosonic covariance and all pairwise disjoint mode sets A, B and C, the sum of the AB and BC entropies dominates the sum of the ABC and B entropies whenever 0<α≤2 and α differs from one. This is the positive-order validity part of the conjecture in RenyiGaussian_v2.tex, line 463, whose proof is requested again at line 532. The statement concerns the covariance entropy formula; order zero, order one, orders above two, fermions and non-Gaussian states are outside its scope."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Strong subadditivity of the covariance entropy"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("First identify the canonical uncertainty condition under the quadrature permutation. The symplectic form squares to minus the identity, as does its restriction to any full set of mode quadratures. The two positive semidefinite matrices V+iω and V−iω have average V. If V has a kernel vector, positivity forces it into the kernel of each uncertainty matrix and hence into the kernel of ω; invertibility of ω rules this out. Thus V is positive definite. These facts pass to each reduced covariance, whose index cardinality is twice the number of retained modes.")),
                    Paragraph(Text("Put J=iω, S=V^(1/2) and M=SJS. The matrix M is Hermitian and invertible. Congruencing the two uncertainty matrices by JS gives M²+M and M²−M positive semidefinite. Evaluating their quadratic forms on normalized eigenvectors gives λ²+λ≥0 and λ²−λ≥0. Since λ is nonzero, |λ|≥1. For 0≤x<1, the interpolation H_x=V+ixω=x(V+iω)+(1−x)V is Hermitian positive definite, and its principal blocks are the corresponding interpolations of the reduced covariances.")),
                    Paragraph(Text("To compute its determinant, use equality of the characteristic polynomials of SJS and JV, together with −J H_(−t)=tI−JV. Since J²=I and H_x transposed equals H_(−x), multiplication of the characteristic products at x and −x gives det(H_x)² equal to the product of λ²−x² over all eigenvalues λ of M. Every factor and det(H_x) are positive. Taking logarithms gives log(det(H_x)) equal to one half the sum of log(λ²−x²). Apply stieltjes_representation to each |λ| and interchange the finite sum and integrals. The resulting positive Stieltjes mixture is S_α(V)=n c_α+∫₀¹ w_α(x) log(det(V+ixω)) dx for 0<α<2, α different from one; its logarithmic integrand is integrable, including when a symplectic eigenvalue equals one.")),
                    Paragraph(Text("At order two, renyiFunction(2,ν)=log(ν). The determinant identity at x=0 therefore gives S_2(V)=one half of log(det(V)). This also applies to every reduced covariance.")),
                    Paragraph(Text("For a positive definite Hermitian block matrix with leading block P, off-diagonal block X and trailing block Q, the Schur complement Q−XᴴP⁻¹X is positive definite and det(H)=det(P) det(Q−XᴴP⁻¹X). The complement is at most Q in the positive semidefinite order; log_det_mono gives determinant monotonicity, and hence the Fischer product bound. Eliminate the common block B of the matrix on B together with A and C, then apply that product bound to the A and C blocks of the remaining Schur complement. Restriction commutes with this complement. The determinant factors give Koteljanskii’s inequality det(H_ABC) det(H_B)≤det(H_AB) det(H_BC). Positivity of all determinants converts it into the corresponding sum of logarithms. Empty blocks have determinant one and are included.")),
                    Paragraph(Text("Apply this logarithmic inequality to H_x on the four blocks AB, BC, ABC and B, using the disjoint quadrature sets associated with A, B and C. For 0<α<2 with α different from one, multiply the pointwise inequality by the positive weight w_α(x), integrate on (0,1), and use the integrability supplied by the Stieltjes mixture. The identity |A∪B|+|B∪C|=|A∪B∪C|+|B| also holds after casting the cardinalities to the real numbers and cancels the additive multiples of c_α. This gives the asserted entropy inequality. At α=2, apply the same logarithmic inequality at x=0 and multiply by one half."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("camilo-landi-eliens-2019-bosonic-gaussian-renyi-strong-subadditivity"),
                    ResolutionKind.Proved)))));
}
