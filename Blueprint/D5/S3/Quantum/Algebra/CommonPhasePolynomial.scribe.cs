using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CommonPhasePolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful actual common-phase polynomial invariants, quadratic generation and unique Hermitian representation.",
        H("Complete Common Phase Polynomial Invariants"), Blocks(
            Describe.Lean(DescribeId.Create("coeff-aeval-diag"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_aeval_diag"),
                H("Diagonal coefficient formula"), StatementSource.FromAuthor(Disp(All("sigma", F.Id("Type"), All("R", F.Id("Type"), Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Sp, All("d", Rel(F.Id("sigma"), To, F.Id("R")), All("f", Call("MvPolynomial", F.Id("sigma"), F.Id("R")), All("m", Call("Exponent", F.Id("sigma")), Rel(Call("coeff", Call("aevalDiag", F.Id("d"), F.Id("f")), F.Id("m")), Eq, Rel(Call("exponentProduct", F.Id("m"), F.Id("d")), Cdot, Call("coeff", F.Id("f"), F.Id("m")))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/toobysmith2026phasepolynomial")),
                Blocks(Paragraph(Text("For any commutative ring R and any variable type sigma, aevalDiag(d,f) substitutes C(d(i))*X(i) into f. Exponent(sigma) is sigma to finitely supported natural numbers. ExponentProduct(m,d) is the product over the support of m of d(i) raised to m(i). The coefficient of m after substitution is that product times the original coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coeff-eq-zero-of-charge-ne-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.coeff_eq_zero_of_charge_ne_zero"),
                H("Charge balance"), StatementSource.FromAuthor(Disp(All("sigma", F.Id("Type"), All("K", F.Id("Type"), Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp, All("w", Rel(F.Id("sigma"), To, Seq(Mathbb, Grp(F.Id("Z")))), All("c", F.Id("K"), Rel(Rel(F.Id("c"), Neq, D(0)), Implies, Rel(All("n", Seq(Mathbb, Grp(F.Id("Z"))), Rel(Rel(Call("zpow", F.Id("c"), F.Id("n")), Eq, D(1)), Implies, Rel(F.Id("n"), Eq, D(0)))), Implies, All("f", Call("MvPolynomial", F.Id("sigma"), F.Id("K")), Rel(Rel(Call("chargeSubstitution", F.Id("w"), F.Id("c"), F.Id("f")), Eq, F.Id("f")), Implies, All("m", Call("Exponent", F.Id("sigma")), Rel(Rel(Call("charge", F.Id("w"), F.Id("m")), Neq, D(0)), Implies, Rel(Call("coeff", F.Id("f"), F.Id("m")), Eq, D(0))))))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/toobysmith2026phasepolynomial")),
                Blocks(Paragraph(Text("For a field K, integer weights w and a nonzero scalar c, assume c^n=1 only for n=0 among all integers. ChargeSubstitution substitutes C(c raised to w(i))*X(i). Formal invariance under this substitution forces a coefficient to vanish whenever the sum over its finite exponent support of m(i)*w(i) is nonzero. No assumption about actual conjugate evaluation belongs to this supplier; that bridge is established separately."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-infiniteorder-unitary"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.exists_infiniteOrder_unitary"),
                H("An infinite-order complex unitary phase"), StatementSource.FromAuthor(Disp(Ex("w", Call("unitary", Seq(Mathbb, Grp(F.Id("C")))), All("n", Seq(Mathbb, Grp(F.Id("Z"))), Rel(Rel(Call("zpow", F.Id("w"), F.Id("n")), Eq, D(1)), Implies, Rel(F.Id("n"), Eq, D(0))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/toobysmith2026phasepolynomial")),
                Blocks(Paragraph(Text("There exists a complex unitary scalar with no nontrivial integer power equal to one. The phase exp(i) has this property by irrationality of pi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-cartesian"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_cartesian"),
                H("Actual evaluation"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, All("z", V, Rel(Call("eval", Call("cartesian", F.Id("z")), Call("toCartesian", F.Id("p"))), Eq, Actual(F.Id("p"), F.Id("z"))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Poly(iota) is the polynomial algebra over the complex numbers on iota plus a second copy of iota. Coefficients and finite supports are unrestricted. The first copy represents z and the second its conjugate. Cartesian substitution sends these variables to x+iy and x-iy. Actual evaluation sets the second copy to the complex conjugate of the first. For every vector, Cartesian evaluation after substitution equals actual evaluation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-injective"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_injective"),
                H("Faithfulness on the actual conjugate diagonal"), StatementSource.FromAuthor(Disp(Coordinates(Call("Injective", Call("actual", F.Id("iota"))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two paired-variable polynomials agreeing at every actual complex vector are equal. This follows by the invertible Cartesian substitution and polynomial extensionality on a product of infinite real axes. No injectivity on the conjugate diagonal is assumed. The coordinate type may be empty and need not be finite for this statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cartesian-totaldegree"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_totalDegree"),
                H("Total degree correspondence"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, Rel(Call("totalDegree", Call("toCartesian", F.Id("p"))), Eq, Call("totalDegree", F.Id("p")))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both inverse substitutions are linear homogeneous substitutions. Each weakly decreases total degree, so invertibility gives equality. The natural total-degree convention includes degree zero for the zero polynomial. Constants and arbitrary degrees remain in scope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-coordinates-unique"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.real_coordinates_unique"),
                H("Unique expansion of real-coordinate polynomials"), StatementSource.FromAuthor(Disp(Coordinates(All("q", P, Unique("p", P, All("z", V, Rel(Actual(F.Id("p"), F.Id("z")), Eq, Call("eval", Call("cartesian", F.Id("z")), F.Id("q")))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every polynomial in the real and imaginary coordinates has exactly one expansion in z and its conjugate with the same actual values. Complex coefficients permit all complex-valued polynomial functions on the underlying real coordinate space; real coefficients are included through their canonical embedding. The inverse substitution is x=(z+w)/2 and y=(z-w)/(2i)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cartesian-homogeneous"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.cartesian_homogeneous"),
                H("Homogeneous degree correspondence"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, All("n", Seq(Mathbb, Grp(F.Id("N"))), Rel(Call("IsHomogeneous", Call("toCartesian", F.Id("p")), F.Id("n")), Iff, Call("IsHomogeneous", F.Id("p"), F.Id("n"))))), false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, the polynomial is homogeneous of degree n exactly when its Cartesian image is. This uses the homogeneous substitution theorem in both directions. The zero polynomial is homogeneous of every degree, and no nonzero hypothesis is imposed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-monomial-mem-quadratic-adjoin"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.balanced_monomial_mem_quadratic_adjoin"),
                H("Unrestricted balanced-monomial generation"), StatementSource.FromAuthor(Disp(Coordinates(All("m", Call("PairedExponent", F.Id("iota")), Rel(Rel(Call("holo", F.Id("m")), Eq, Call("anti", F.Id("m"))), Implies, Rel(Call("monomial", F.Id("m"), D(1)), InMacro, Call("quadraticAlgebra", F.Id("iota")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PairedExponent(iota) denotes finitely supported natural exponents on the two copies of iota. Holo and anti are the sums on the first and second copy. QuadraticAlgebra is the complex subalgebra generated by all X(inl i) times X(inr j). Equal totals give membership by induction: when the common total is positive, select one positive exponent on each side, subtract that pair, and multiply the inductively obtained element by its quadratic generator. At total zero the monomial is one. The proof requires no supplied factorization certificate and includes empty coordinate types."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-phase-polynomial-theorem"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.common_phase_polynomial_theorem"),
                H("Actual invariance, balance and generation"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, And(Rel(Call("Invariant", F.Id("p")), Iff, Call("Balanced", F.Id("p"))), Rel(Call("Invariant", F.Id("p")), Iff, Rel(F.Id("p"), InMacro, Call("quadraticAlgebra", F.Id("iota"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Invariant means equality of actual values under multiplication of every coordinate by exp(i theta), for every complex vector and every real theta. Balanced means every nonzero coefficient has equal holomorphic and antiholomorphic totals. Faithful actual evaluation converts phase invariance into formal diagonal invariance. The diagonal charge theorem eliminates nonzero charges using an infinite-order unitary phase. Every balanced monomial then lies in the quadratic algebra by constructive pairing. Conversely every generator and hence every element of its generated algebra is invariant. Zero, constants, empty support and unrestricted degrees are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-quadratic-generation"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_generation"),
                H("Generation in the algebra of actual functions"),
                StatementSource.FromAuthor(Disp(Coordinates(All("p", P,
                    Rel(Call("Invariant", F.Id("p")), Implies,
                        Rel(Call("actual", F.Id("p")), InMacro,
                            Call("actualQuadraticAlgebra", F.Id("iota")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ActualQuadraticAlgebra is the complex subalgebra of all functions from complex coordinate vectors to complex values generated by the functions z_i times conjugate(z_j), with ordinary pointwise operations. Every invariant actual polynomial belongs to this algebra. The evaluation algebra homomorphism sends the formal generated algebra to this actual generated algebra."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-minimum-degree"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_minimum_degree"),
                H("Lower bound for nonconstant invariants"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, Rel(Call("Invariant", F.Id("p")), Implies, Rel(Seq(Neg, Sp, Ex("c", Seq(Mathbb, Grp(F.Id("C"))), Rel(F.Id("p"), Eq, Call("C", F.Id("c"))))), Implies, Rel(D(2), Leq, Call("totalDegree", F.Id("p"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every invariant which is not a constant polynomial has total degree at least two. Under balance, a nonzero supported exponent has total degree twice its holomorphic total. Degree less than two therefore leaves only the constant monomial. This implication makes no positive-dimension assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-degree-two"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_degree_two"),
                H("Attainment in positive dimension"), StatementSource.FromAuthor(Disp(Coordinates(All("i", F.Id("iota"), And(Call("Invariant", Call("quadraticGenerator", F.Id("i"), F.Id("i"))), Rel(Call("totalDegree", Call("quadraticGenerator", F.Id("i"), F.Id("i"))), Eq, D(2))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any supplied coordinate i gives the invariant z_i times its conjugate with degree exactly two. Supplying i expresses positive dimension; no nonconstant polynomial is asserted to exist when the coordinate type is empty."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-quadratic-matrix-unique"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.actual_quadratic_matrix_unique"),
                H("Uniqueness from actual values"), StatementSource.FromAuthor(Disp(Coordinates(All("H", M, All("K", M, Rel(All("z", V, Rel(Q(F.Id("H"), F.Id("z")), Eq, Q(F.Id("K"), F.Id("z")))), Implies, Rel(F.Id("H"), Eq, F.Id("K")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("StarDotMul(H,z) denotes star(z) dot (H times z). Equality of this value for every actual complex vector forces equality of H and K, with no Hermitian assumption. The proof turns both forms into paired-variable polynomials, uses faithful actual evaluation and compares their coefficients. The empty matrix case is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-quadratic-hermitian"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_hermitian"),
                H("Unique Hermitian representation"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, QuadraticConditions(F.Id("p"), UniqueMatrix(F.Id("p"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite coordinate type, every actual common-phase invariant polynomial which is homogeneous of degree two and real-valued at every complex vector has exactly one Hermitian matrix H whose quadratic form equals its actual values. The coefficient c_ij of z_i times conjugate(z_j) is placed at H_ji. Balanced degree-two exponents contain exactly one variable from each copy, so these coefficients construct the matrix. Real-valuedness gives symmetry of the associated Euclidean linear map and hence the Hermitian property through the existing inner-product and matrix theorems. Uniqueness uses equality of actual values alone. Zero and dimension zero remain included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("invariant-quadratic-nonnegative-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.invariant_quadratic_nonnegative_iff"),
                H("Nonnegative values and positive semidefiniteness"), StatementSource.FromAuthor(Disp(Coordinates(All("p", P, QuadraticConditions(F.Id("p"), PositiveIff(F.Id("p"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual real-valued homogeneous quadratic phase invariant, nonnegativity of the real part of every value is equivalent to Matrix.PosSemidef of its coefficient matrix. Reality makes the imaginary part zero. Complex.nonneg_iff then converts real nonnegativity into the complex order used by the matrix predicate. The proof applies the existing Hermitian dot-product characterization of positive semidefiniteness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-common-phase-polynomial-theorem"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/CommonPhasePolynomial.complete_common_phase_polynomial_theorem"),
                H("Complete polynomial statement"), StatementSource.FromAuthor(Disp(Complete())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All coordinate types in this statement are arbitrary finite types, including the empty type. Poly(iota) has arbitrary complex coefficients, finite support and degree. Holo and anti sum exponents over the two copies of the coordinate type. Balanced requires equal totals for every nonzero monomial coefficient. Invariant quantifies over every actual complex vector and every real phase angle. QuadraticAlgebra is generated by every z_i times conjugate(z_j); its generation assertion is proved by constructive monomial pairing. The statement retains the unique real-coordinate correspondence, actual evaluation, total and homogeneous degree correspondence, both invariant characterizations, the degree lower bound, degree-two attainment for any supplied coordinate, and the unique Hermitian and nonnegative/PSD conclusions for real-valued homogeneous quadratics. PairExponent(i,j) is single(inl i,1)+single(inr j,1), and entry(coefficientMatrix(p),j,i)=coeff(p,pairExponent(i,j)). Empty dimension gives constants and the unique empty matrix, with no assertion of a nonconstant invariant. StarDotMul(H,z) means star(z) dot (H times z). The statement concerns polynomial functions on the whole coordinate space and introduces no physical probability or quotient-topology assumption."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { content.Add(Comma); content.Add(Sp); }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Bang, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula And(params Formula[] parts)
    {
        var content = new List<Formula> { Open };
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) { content.Add(Sp); content.Add(Land); content.Add(Sp); }
            content.Add(parts[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula Coordinates(Formula body, bool finite = true) =>
        All("iota", F.Id("Type"), finite
            ? Seq(OpenBracket, Call("Fintype", F.Id("iota")), CloseBracket, Sp, body) : body);
    private static Formula P => Call("Poly", F.Id("iota"));
    private static Formula V => Rel(F.Id("iota"), To, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula M => Call("Matrix", F.Id("iota"), F.Id("iota"), Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Actual(Formula p, Formula z) => Call("actual", p, z);
    private static Formula Q(Formula h, Formula z) => Call("starDotMul", h, z);
    private static Formula Reality(Formula p) =>
        All("z", V, Rel(Call("im", Actual(p, F.Id("z"))), Eq, D(0)));
    private static Formula Homogeneous(Formula p) => Call("IsHomogeneous", p, D(2));
    private static Formula UniqueMatrix(Formula p) => Unique("H", M,
        And(Call("IsHermitian", F.Id("H")),
            All("z", V, Rel(Actual(p, F.Id("z")), Eq, Q(F.Id("H"), F.Id("z")))), Orientation(p)));
    private static Formula Positive(Formula p) => All("z", V,
        Rel(D(0), Leq, Call("re", Actual(p, F.Id("z")))));
    private static Formula PositiveIff(Formula p) =>
        Rel(Positive(p), Iff, Call("PosSemidef", Call("coefficientMatrix", p)));
    private static Formula QuadraticConditions(Formula p, Formula body) =>
        Rel(Call("Invariant", p), Implies,
            Rel(Homogeneous(p), Implies, Rel(Reality(p), Implies, body)));
    private static Formula Orientation(Formula p) => All("i", F.Id("iota"),
        All("j", F.Id("iota"), Rel(Call("entry", F.Id("H"), F.Id("j"), F.Id("i")),
            Eq, Call("coeff", p, Call("pairExponent", F.Id("i"), F.Id("j"))))));
    private static Formula Complete()
    {
        Formula p = F.Id("p");
        Formula nonconstant = Seq(Neg, Sp, Ex("c", Seq(Mathbb, Grp(F.Id("C"))), Rel(p, Eq, Call("C", F.Id("c")))));
        Formula lower = Rel(Call("Invariant", p), Implies,
            Rel(nonconstant, Implies, Rel(D(2), Leq, Call("totalDegree", p))));
        Formula attain = All("i", F.Id("iota"), And(
            Call("Invariant", Call("quadraticGenerator", F.Id("i"), F.Id("i"))),
            Rel(Call("totalDegree", Call("quadraticGenerator", F.Id("i"), F.Id("i"))), Eq, D(2))));
        return Coordinates(All("p", P, And(
            Unique("q", P, All("z", V, Rel(Actual(F.Id("q"), F.Id("z")), Eq,
                Call("eval", Call("cartesian", F.Id("z")), p)))),
            Rel(Call("totalDegree", Call("toCartesian", p)), Eq, Call("totalDegree", p)),
            All("n", Seq(Mathbb, Grp(F.Id("N"))), Rel(Call("IsHomogeneous", Call("toCartesian", p), F.Id("n")), Iff,
                Call("IsHomogeneous", p, F.Id("n")))),
            Rel(Call("Invariant", p), Iff, Call("Balanced", p)),
            Rel(Call("Invariant", p), Iff, Rel(p, InMacro, Call("quadraticAlgebra", F.Id("iota")))),
            Rel(Call("Invariant", p), Implies, Rel(Call("actual", p), InMacro,
                Call("actualQuadraticAlgebra", F.Id("iota")))),
            lower, attain,
            Rel(Homogeneous(p), Implies, Rel(Reality(p), Implies, Rel(Call("Invariant", p), Implies,
                Unique("H", M, And(Call("IsHermitian", F.Id("H")),
                    All("z", V, Rel(Actual(p, F.Id("z")), Eq, Q(F.Id("H"), F.Id("z")))),
                    Orientation(p), Rel(Positive(p), Iff, Call("PosSemidef", F.Id("H"))),
                    All("K", M, Rel(All("z", V,
                        Rel(Actual(p, F.Id("z")), Eq, Q(F.Id("K"), F.Id("z")))),
                        Implies, Rel(F.Id("K"), Eq, F.Id("H"))))))))))));
    }
}
