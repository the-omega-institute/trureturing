using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Solitons;

internal sealed class NambuKahanCremonaDecompositionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/FluidDynamics/graffeogubbiotti2024cremona");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The homogeneous KHK map of a positive definite quadratic Nambu pair with a simple pencil factors through the cubic Cremona map.",
        H("A Cremona decomposition for quadratic Nambu systems"),
        Blocks(
            Node("nambu-linear-part", "The polarised Nambu matrix", "nambuLinearPart",
                NambuLinearPartFormula(), AssessedProvenance.FromRepo(Source),
                "For real matrices A and B and a complex vector x, the jth column is "
                    + "the sum of the cross products of Ax with the jth column of B and "
                    + "of the jth column of A with Bx. The real entries are included in the "
                    + "complex numbers by algebraMap. Pi.single j 1 is the jth coordinate vector. "
                    + "Thus multiplication by a vector v gives Ax × Bv + Av × Bx. "
                    + "For symmetric A and B twice this expression is the symmetric polarisation of the "
                    + "Nambu vector field with Hamiltonians xᵀAx and xᵀBx. The Nambu system "
                    + "appears in Remark 7.7, TeX lines 3180–3195; the displayed matrix is its "
                    + "complex coordinate encoding."),
            Node("kahan-matrix", "The homogeneous KHK matrix", "kahanMatrix",
                KahanMatrixFormula(), AssessedProvenance.FromRepo(Source),
                "The first three coordinates of X form x and its last coordinate is X 3. "
                    + "The matrix is X 3 times the identity minus twice the real step h, "
                    + "included in the complex numbers, times the polarised Nambu matrix. "
                    + "For the quadratic vector field f(x) = 4 Ax × Bx, Definition 2.1 "
                    + "of the KHK step (TeX lines 634–656) gives x′ − x = "
                    + "2h(Ax × Bx′ + Ax′ × Bx). This matrix is the homogeneous form of "
                    + "the linear system for x′."),
            Node("kahan", "The homogeneous Nambu KHK lift", "kahan",
                KahanFormula(), AssessedProvenance.FromRepo(Source),
                "Apply the adjugate of the homogeneous KHK matrix to the first three "
                    + "coordinates, then append its determinant as the fourth coordinate. "
                    + "Fin.snoc performs this append. In the affine chart with X 3 = 1 "
                    + "and nonzero determinant, dividing by the last coordinate gives "
                    + "the KHK update. The polynomial lift is defined even when that "
                    + "determinant vanishes. It encodes the homogeneous Nambu KHK map "
                    + "introduced in Remark 7.7, TeX lines 3207–3208."),
            Node("cremona", "The standard cubic Cremona lift", "cremona",
                CremonaFormula(), AssessedProvenance.FromLiterature(Source),
                "Each coordinate is the product of the other three coordinates. "
                    + "On the projective torus this is coordinatewise inversion, the "
                    + "standard Cremona transformation in equation (C3), TeX lines 169–176, "
                    + "specialised to projective dimension three. The four entries use "
                    + "indices zero through three."),
            Node("claim", "Decomposition for every simple positive definite pencil", "claim",
                Equal(Seq(Operatorname, Grp(V("claim"))), Parenthesized(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                "For every pair of real positive definite matrices whose pencil B − tA "
                    + "has rank at least two for every real t, and every positive real h, "
                    + "two invertible complex four by four matrices factor the KHK lift "
                    + "through the cubic Cremona lift. Positive definiteness includes symmetry; "
                    + "the rank condition expresses distinct generalised eigenvalues. "
                    + "The identity holds for every complex homogeneous vector, including zero. "
                    + "This is the simple-pencil formulation of the conjecture in Remark 7.7 "
                    + "(TeX lines 3209–3214), extending the Euler-top factorisation of "
                    + "Lemma 2.6 (lines 1063–1101). Conjugation by a projectivity is absorbed "
                    + "into the two linear factors. Repeated eigenvalues, the eight-point "
                    + "base-locus criterion, and degree-growth classifications are outside "
                    + "the proposition."),
            Describe.Lean(
                DescribeId.Create("nambu-kahan-cremona-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The Nambu KHK lift factors through Cremona"),
                StatementSource.FromAuthor(Disp(ClaimProposition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Begin with an Euler vector field with complex coefficients a₁, a₂, a₃. "
                            + "Its Jacobian at y has zero diagonal and off-diagonal entries "
                            + "a₁y₂, a₁y₁ in row zero, a₂y₂, a₂y₀ in row one, and "
                            + "a₃y₁, a₃y₀ in row two. Denote this matrix by J and the lift "
                            + "obtained from X 3 times the identity minus (h/2)J by Φ. "
                            + "For square roots α² = a₁, β² = a₂, γ² = a₃, form a matrix C "
                            + "whose rows are (−βγh, −αγh, αβh, −2), "
                            + "(βγh, −αγh, −αβh, −2), (−βγh, αγh, −αβh, −2), "
                            + "and (βγh, αγh, αβh, −2). Let G have diagonal entries one "
                            + "and every off-diagonal entry minus one. Expanding the four "
                            + "coordinates and using the square-root identities proves "
                            + "CΦ(X) = (−1/8)G cremona(CX). Expanding determinants gives "
                            + "det C = 32α²β²γ²h³ and det G = −16, so G is invertible.")),
                    Paragraph(Text(
                        "Next normalise the real quadratic forms. Choose a positive definite "
                            + "symmetric square root L of A and put S = L⁻¹. Then SᵀAS = I. "
                            + "The real symmetric matrix SᵀBS has an orthogonal eigenvector matrix Q "
                            + "and real eigenvalues mu. With P = SQ, both P and its determinant "
                            + "are invertible, PᵀAP = I, and PᵀBP = diagonal mu. Multiplication "
                            + "by P and Pᵀ preserves rank, so diagonal(mu − t) has rank at least "
                            + "two for every real t. If two distinct indices had the same "
                            + "eigenvalue, taking t equal to it would leave at most one nonzero "
                            + "diagonal entry. The diagonal-rank formula would give rank at most "
                            + "one, a contradiction. Thus the three eigenvalues are distinct.")),
                    Paragraph(Text(
                        "Include P in the complex matrices and extend it by a final identity "
                            + "coordinate to an invertible four by four matrix R. For any complex "
                            + "three by three matrix D, direct expansion gives "
                            + "(Du) × (Dv) = adj(D)ᵀ(u × v). For invertible D the adjugate "
                            + "is det(D)D⁻¹; this also proves that adjugates commute with "
                            + "conjugation and yields (D⁻ᵀu) × (D⁻ᵀv) = det(D)⁻¹D(u × v). "
                            + "The column definition of the polarised Nambu matrix gives its "
                            + "action on every v as Ax × Bv + Av × Bx.")),
                    Paragraph(Text(
                        "Set a₁ = 4((mu 2 : ℂ) − (mu 1 : ℂ))/(det P : ℂ), "
                            + "a₂ = 4((mu 0 : ℂ) − (mu 2 : ℂ))/(det P : ℂ), and "
                            + "a₃ = 4((mu 1 : ℂ) − (mu 0 : ℂ))/(det P : ℂ). "
                            + "The two normalised-form identities express the transformed A "
                            + "and B through the inverse transpose of P and the diagonal matrix "
                            + "of mu. The cross-product identity then identifies the transformed "
                            + "polarised matrix with one quarter of J. Consequently the Nambu "
                            + "KHK matrix at RZ is conjugate by P to the Euler KHK matrix at Z: "
                            + "the factor 2h times one quarter becomes h/2. Adjugate conjugation "
                            + "and determinant invariance, together with the appended last "
                            + "coordinate, give kahan A B h (RZ) = RΦ(Z) exactly.")),
                    Paragraph(Text(
                        "Finally fix A, B and positive h satisfying the proposition. "
                            + "The distinct eigenvalues and nonzero determinant of P make all "
                            + "three coefficients a₁, a₂, a₃ nonzero. Algebraic closure of ℂ "
                            + "provides α, β, γ with the required squares. Include h in ℂ; "
                            + "it is nonzero because h is positive. The determinant formula "
                            + "therefore makes C invertible. Set U = CR⁻¹, l₁ = U and "
                            + "l₂ = (−1/8)U⁻¹G. Both determinants are nonzero: this follows "
                            + "from those of C, R and G and the nonzero scalar −1/8. "
                            + "For each X, substitute Z = R⁻¹X into the change-of-coordinates "
                            + "identity and the Euler identity. Cancelling R⁻¹R gives "
                            + "U kahan A B h X = (−1/8)G cremona(UX). Multiplication by U⁻¹ "
                            + "gives the asserted factorisation with l₁ and l₂. All identities "
                            + "are polynomial identities in X, so no exclusion of a zero "
                            + "coordinate or a singular KHK matrix is needed."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("graffeo-gubbiotti-2024-nambu-kahan-cremona-decomposition"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create("nambu-kahan-cremona-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula Vector(byte size) => new Formula.TypeArrow(Fin(size), Complexes());
    private static Formula Matrix(byte size, Formula scalars) => Call("Matrix", Fin(size), Fin(size), scalars);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula ExistsOf(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mul(Formula left, Formula right) => Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) =>
        At(Qualified("HSMul", "hSMul"), scalar, value);
    private static Formula MulVec(Formula matrix, Formula vector) =>
        At(Qualified("Matrix", "mulVec"), matrix, vector);
    private static Formula ComplexMatrix(Formula matrix) =>
        At(Qualified("Matrix", "map"), matrix, Call("algebraMap", Reals(), Complexes()));
    private static Formula FirstThree() => LambdaOf("i", Fin(3),
        At(V("X"), At(Qualified("Fin", "castSucc"), V("i"))));
    private static Formula KahanMatrix() => Call("kahanMatrix", V("A"), V("B"), V("h"), V("X"));
    private static Formula Parameters(Formula body) =>
        All(V("A"), Matrix(3, Reals()), All(V("B"), Matrix(3, Reals()), body));
    private static Formula StepParameters(Formula body) =>
        Parameters(All(V("h"), Reals(), All(V("X"), Vector(4), body)));

    private static Formula NambuLinearPartFormula()
    {
        Formula a = ComplexMatrix(V("A")), b = ComplexMatrix(V("B"));
        Formula basis = At(Qualified("Pi", "single"), V("j"), Typed(D(1), Complexes()));
        Formula entry = Add(
            At(Call("crossProduct", MulVec(a, V("x")), MulVec(b, basis)), V("i")),
            At(Call("crossProduct", MulVec(a, basis), MulVec(b, V("x"))), V("i")));
        return Parameters(All(V("x"), Vector(3),
            Equal(Call("nambuLinearPart", V("A"), V("B"), V("x")),
                LambdaOf("i", Fin(3), LambdaOf("j", Fin(3), entry)))));
    }

    private static Formula KahanMatrixFormula() => StepParameters(Equal(KahanMatrix(),
        Subtract(
            Smul(At(V("X"), Typed(D(3), Fin(4))), Typed(D(1), Matrix(3, Complexes()))),
            Smul(Mul(Typed(D(2), Complexes()), Typed(V("h"), Complexes())),
                Call("nambuLinearPart", V("A"), V("B"), FirstThree())))));

    private static Formula KahanFormula() => StepParameters(Equal(
        Call("kahan", V("A"), V("B"), V("h"), V("X")),
        At(Qualified("Fin", "snoc"),
            MulVec(At(Qualified("Matrix", "adjugate"), KahanMatrix()), FirstThree()),
            At(Qualified("Matrix", "det"), KahanMatrix()))));

    private static Formula Coordinate(byte i) => At(V("X"), Typed(D(i), Fin(4)));
    private static Formula Triple(byte i, byte j, byte k) => Mul(Mul(Coordinate(i), Coordinate(j)), Coordinate(k));
    private static Formula CremonaFormula() => All(V("X"), Vector(4), Equal(Call("cremona", V("X")),
        Seq(Bang, OpenBracket, Triple(1, 2, 3), Comma, Sp, Triple(0, 2, 3), Comma, Sp,
            Triple(0, 1, 3), Comma, Sp, Triple(0, 1, 2), CloseBracket)));

    private static Formula ClaimProposition()
    {
        Formula lOne = new Formula.Subscript(V("l"), D(1));
        Formula lTwo = new Formula.Subscript(V("l"), D(2));
        Formula rank = All(V("t"), Reals(), LE(D(2),
            At(Qualified("Matrix", "rank"), Subtract(V("B"), Smul(V("t"), V("A"))))));
        Formula factors = And(Call("IsUnit", At(Qualified("Matrix", "det"), lOne)),
            And(Call("IsUnit", At(Qualified("Matrix", "det"), lTwo)),
                All(V("X"), Vector(4), Equal(Call("kahan", V("A"), V("B"), V("h"), V("X")),
                    MulVec(lTwo, Call("cremona", MulVec(lOne, V("X"))))))));
        return Parameters(Implies(At(Qualified("Matrix", "PosDef"), V("A")),
            Implies(At(Qualified("Matrix", "PosDef"), V("B")),
                Implies(rank, All(V("h"), Reals(), Implies(Less(Typed(D(0), Reals()), V("h")),
                    ExistsOf(lOne, Matrix(4, Complexes()), ExistsOf(lTwo, Matrix(4, Complexes()), factors))))))));
    }
}
