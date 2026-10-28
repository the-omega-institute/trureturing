using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class MixedUnitaryPinchingCommutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/liutakagilloyd2019diagonaldiscord");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every non-isotropic mixed-unitary qubit channel fails to commute with marginal pinching on a two-qubit density matrix with nondegenerate input and output marginals.",
        H("Mixed-unitary channels and marginal pinching"),
        Blocks(
            Paragraph(Text(
                "QubitMatrix is the algebra of complex matrices with both indices in Fin 2. "
                + "A starred matrix denotes its conjugate transpose, and I denotes the identity of the indicated size.")),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-is-mixed-unitary"),
                DeclarationHandle.Create(Prefix + "IsMixedUnitary"),
                H("Finite mixtures of unitary conjugations"),
                StatementSource.FromAuthor(Disp(MixedUnitaryFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A mixed-unitary map is a finite convex combination of unitary conjugations. "
                    + "The real weights are nonnegative and sum to one; their inclusions into the complex numbers act by scalar multiplication. "
                    + "The equality holds for every complex qubit matrix, rather than only for density matrices. "
                    + "This is the linear extension of the mixed-unitary class in Section 3.2, "
                    + "revised_jphysa_clean.tex, line 325."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-is-isotropic"),
                DeclarationHandle.Create(Prefix + "IsIsotropic"),
                H("Unitary and antiunitary isotropic forms"),
                StatementSource.FromAuthor(Disp(IsotropicFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An isotropic map combines a unitary or antiunitary action with complete depolarization, "
                    + "using one real parameter between zero and one and one unitary matrix. "
                    + "On arbitrary complex matrices the depolarizing term is trace(a) times I/2. "
                    + "The antiunitary action on states extends complex linearly as u a-transpose u-star. "
                    + "These are the two alternatives in Section 3.2, revised_jphysa_clean.tex, lines 326-327; "
                    + "no positivity condition is imposed on the matrix argument a."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-local-map"),
                DeclarationHandle.Create(Prefix + "localMap"),
                H("Extension to the first qubit"),
                StatementSource.FromAuthor(Disp(LocalMapFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The two matrix indices are pairs, with the first coordinate belonging to A. "
                    + "Fixing the second coordinates selects a qubit block, to which the map is applied. "
                    + "For a linear map this is its tensor product with the identity on the second qubit. "
                    + "The block formula also defines a function for arbitrary maps, without requiring linearity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-is-nondegenerate"),
                DeclarationHandle.Create(Prefix + "IsNondegenerate"),
                H("A Hermitian qubit matrix with simple spectrum"),
                StatementSource.FromAuthor(Disp(NondegenerateFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The matrix must be Hermitian and its two real eigenvalues must be distinct. "
                    + "Injectivity of the eigenvalue function on Fin 2 expresses this distinction. "
                    + "This is the nondegeneracy assumption on the marginal in revised_jphysa_clean.tex, line 339."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-pinch-a"),
                DeclarationHandle.Create(Prefix + "pinchA"),
                H("Pinching in the first marginal's spectral basis"),
                StatementSource.FromAuthor(Disp(PinchingFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a Hermitian first marginal, choose its orthonormal eigenvector basis. "
                    + "Each outer product p projects onto one eigenvector; tensoring with the second identity "
                    + "and summing the corresponding unread measurements gives marginal pinching. "
                    + "This is the map defined in revised_jphysa_clean.tex, line 261. "
                    + "The choice is unambiguous on a nondegenerate marginal. "
                    + "The formula extends to degenerate Hermitian marginals using the chosen basis, "
                    + "and returns the original matrix when the marginal is not Hermitian."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixed-unitary-pinching-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Non-isotropic mixed-unitary channels do not commute with pinching"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The conclusion concerns the second sentence of the conjecture in revised_jphysa_clean.tex, line 463. "
                        + "For each non-isotropic mixed-unitary qubit map, it supplies a positive semidefinite two-qubit matrix "
                        + "of trace one, with both the input marginal and its image nondegenerate, on which the two orders of pinching "
                        + "and local evolution differ. It asserts neither the converse nor a classification of maps outside the mixed-unitary class.")),
                    Paragraph(Text(
                        "First, the convex combination gives a complex linear map preserving the identity, trace and Hermiticity. "
                        + "Write S(v) for the real Pauli combination v-dot-sigma. "
                        + "Define the real matrix T by T(i,j) = Re tr(sigma(i+1) phi(sigma(j+1)))/2. "
                        + "The Hermitian traceless Pauli expansion gives phi(S(v)) = S(Tv). "
                        + "The trace of S(v) is zero, "
                        + "S(v) squared is (v-dot-v)I, and the anticommutator of S(v) and S(w) is 2(v-dot-w)I. "
                        + "These identities also give S(v)S(w)S(v) = 2(v-dot-w)S(v) - (v-dot-v)S(w). "
                        + "Agreement on I and every S(v) determines a complex linear map on all qubit matrices.")),
                    Paragraph(Text(
                        "The convex combination also preserves positivity. Suppose T-transpose T = cI. "
                        + "The squared length of each column gives c at least zero. "
                        + "Apply positivity to the rank-one diagonal matrix with entries 1 and 0: "
                        + "its image has trace one and Bloch-vector length squared c, hence c is at most one. "
                        + "To lift an orthogonal transformation of real three-space, begin with a hyperplane reflection. "
                        + "For a nonzero normal v, the Hermitian unitary S(v)/length(v), together with the second Pauli matrix "
                        + "and matrix transpose, implements the reflection on Pauli combinations by the triple-product identity. "
                        + "A zero normal gives the identity. The Cartan-Dieudonne decomposition expresses every orthogonal "
                        + "transformation as a product of such reflections; composing their actions yields either unitary conjugation "
                        + "or unitary conjugation after transpose. When c = 0, T = 0 and agreement on the Pauli expansion identifies "
                        + "phi with complete depolarization. When c is positive, put s = sqrt(c) and O = T/s. "
                        + "Then O-transpose O = I and 0 < s <= 1. The lift and agreement on I and S(v) identify phi with the "
                        + "isotropic form of parameter gamma = 1 - s. Thus non-isotropy forces Q = T-transpose T to be nonscalar.")),
                    Paragraph(Text(
                        "A nonscalar Q supplies orthogonal real vectors whose images under T have nonzero inner product. "
                        + "If Q has a nonzero off-diagonal entry Q(i,j), use the coordinate vectors e_i and e_j. "
                        + "Otherwise some diagonal entry Q(i,i) differs from Q(0,0); use e_0 + e_i and e_0 - e_i. "
                        + "Their image inner product is Q(0,0) - Q(i,i). Normalize both vectors to obtain n and x with "
                        + "n-dot-n = x-dot-x = 1, n-dot-x = 0 and (Tn)-dot-(Tx) nonzero. "
                        + "In particular both n and Tn are nonzero.")),
                    Paragraph(Text(
                        "Next derive a pinching formula for any two-qubit matrix tau with marginal (I + S(v))/2 and v nonzero. "
                        + "Let p_0 and p_1 be the marginal's spectral projectors and lambda_0, lambda_1 its eigenvalues. "
                        + "The spectral expansion gives p_0 + p_1 = I. The trace and determinant give lambda_0 + lambda_1 = 1 "
                        + "and lambda_0 lambda_1 = (1 - v-dot-v)/4, so (lambda_0 - lambda_1) squared is v-dot-v. "
                        + "Consequently S(v) = (lambda_0 - lambda_1)(p_0 - p_1). Expanding the two lifted projectors "
                        + "in the unread measurement yields pinchA(tau) = [tau + (S(v) tensor I) tau (S(v) tensor I)/(v-dot-v)]/2.")),
                    Paragraph(Text(
                        "Now take rho = [I tensor I + (S(n) tensor I)/2 + (S(x) tensor Z)/4]/4. "
                        + "Here Z is the diagonal Pauli matrix with entries 1 and -1. "
                        + "Its first marginal is (I + S(n)/2)/2. To prove positivity directly, put K = S(n) tensor I, "
                        + "L = S(x) tensor Z and H = K/2 + L/4. The Pauli identities give K squared = L squared = I "
                        + "and KL = -LK. Thus H is Hermitian and H squared = 5I/16. "
                        + "The identity rho = (I + H)(I + H)-dagger/8 + 11I/128 expresses rho as a sum of positive semidefinite matrices. "
                        + "The Pauli traces give trace(rho) = 1.")),
                    Paragraph(Text(
                        "For arbitrary real a and b, let R(a,b) be the same displayed state expression with n and x replaced by a and b. "
                        + "Linearity and the Pauli representation show that local evolution takes R(a,b) to R(Ta,Tb). "
                        + "For a nonzero, the pinching formula takes R(a,b) to R(a,[(a-dot-b)/(a-dot-a)]a). "
                        + "Taking the partial trace commutes with local evolution, and the output marginal is (I + S(Tn)/2)/2. "
                        + "A qubit matrix (I + S(v))/2 with v nonzero has distinct eigenvalues: "
                        + "equal eigenvalues would make its spectral expansion scalar, whose Bloch vector vanishes, contradicting v nonzero. "
                        + "Apply this to v = n/2 and v = Tn/2 to obtain both required nondegeneracy conclusions.")),
                    Paragraph(Text(
                        "Finally substitute these state and pinching identities in the difference of the two orders. "
                        + "Since n-dot-x = 0, the difference is [(Tn)-dot-(Tx)]/[16((Tn)-dot-(Tn))] times S(Tn) tensor Z. "
                        + "The real quotient is included into the complex scalars. Its numerator is nonzero and its denominator is positive. "
                        + "The tensor factor is also nonzero: its second-qubit (0,0) block is S(Tn), and a vanishing S(Tn) "
                        + "would contradict S(Tn) squared = ((Tn)-dot-(Tn))I. Thus the difference cannot vanish, proving the inequality."))),
                DescribeRole.Theorem))));

    private static Formula MixedUnitaryFormula()
    {
        Formula nonnegative = All("j", FinOf(X("k")), LE(Typed(D(0), Reals), At(X("p"), X("j"))));
        Formula normalized = Equal(SumOver("j", FinOf(X("k")), At(X("p"), X("j"))), Typed(D(1), Reals));
        Formula unitary = All("j", FinOf(X("k")), Member(At(X("u"), X("j")), Unitaries));
        Formula action = All("a", Qubit, Equal(At(Varphi, X("a")),
            SumOver("j", FinOf(X("k")), Smul(OfReal(At(X("p"), X("j"))),
                Multiply(Multiply(At(X("u"), X("j")), X("a")),
                    At(Qualified("star"), At(X("u"), X("j"))))))));
        Formula body = Some("k", Naturals, Some("p", Arrow(FinOf(X("k")), Reals),
            Some("u", Arrow(FinOf(X("k")), Qubit), And(nonnegative, And(normalized, And(unitary, action))))));
        return All("φ", Channel, Equal(LocalCall("IsMixedUnitary", Varphi), Parenthesized(body)));
    }

    private static Formula IsotropicFormula()
    {
        Formula unitary = All("a", Qubit, Equal(At(Varphi, X("a")),
            IsotropicValue(X("a"))));
        Formula antiunitary = All("a", Qubit, Equal(At(Varphi, X("a")),
            IsotropicValue(At(Qualified("Matrix", "transpose"), X("a")))));
        Formula body = Some("γ", Reals, And(Member(GammaLower,
            At(Qualified("Set", "Icc"), Typed(D(0), Reals), Typed(D(1), Reals))),
            Some("u", Qubit, And(Member(X("u"), Unitaries), Or(unitary, antiunitary)))));
        return All("φ", Channel, Equal(LocalCall("IsIsotropic", Varphi), Parenthesized(body)));
    }

    private static Formula IsotropicValue(Formula a) => Add(
        Smul(OfReal(Subtract(Typed(D(1), Reals), GammaLower)),
            Multiply(Multiply(X("u"), a), At(Qualified("star"), X("u")))),
        Smul(OfReal(GammaLower), Smul(Divide(At(Qualified("Matrix", "trace"), X("a")),
            Typed(D(2), Complexes)), Typed(D(1), Qubit))));

    private static Formula LocalMapFormula()
    {
        Formula block = LambdaOf("i", FinOf(D(2)), LambdaOf("j", FinOf(D(2)),
            At(Rho, Pair(X("i"), Projection(X("a"), 2)), Pair(X("j"), Projection(X("c"), 2)))));
        return All("φ", Channel, All("ρ", Bipartite,
            Equal(Typed(LocalCall("localMap", Varphi, Rho), Bipartite),
                LambdaOf("a", PairIndex, LambdaOf("c", PairIndex,
                    At(Varphi, block, Projection(X("a"), 1), Projection(X("c"), 1)))))));
    }

    private static Formula NondegenerateFormula() => All("a", Qubit,
        Equal(LocalCall("IsNondegenerate", X("a")),
            Parenthesized(Some("h", At(Qualified("Matrix", "IsHermitian"), X("a")),
                At(Qualified("Function", "Injective"),
                    At(Qualified("Matrix", "IsHermitian", "eigenvalues"), X("h")))))));

    private static Formula PinchingFormula()
    {
        Formula condition = At(Qualified("Matrix", "IsHermitian"), Marginal(Rho));
        Formula basis = At(Qualified("Matrix", "IsHermitian", "eigenvectorBasis"), X("h"));
        Formula vector = At(Qualified("WithLp", "ofLp"), At(basis, X("i")));
        Formula projector = LambdaOf("a", FinOf(D(2)), LambdaOf("c", FinOf(D(2)),
            Multiply(At(vector, X("a")), At(Qualified("star"), At(vector, X("c"))))));
        Formula product = LambdaOf("x1", Complexes, LambdaOf("x2", Complexes,
            Multiply(X("x1"), X("x2"))));
        Formula projectors = LambdaOf("i", FinOf(D(2)),
            Seq(Qualified("let"), Sp, Typed(X("p"), Qubit), Sp, Eq, Sp, projector, Semi, Sp,
                At(Qualified("Matrix", "kroneckerMap"), product, X("p"), Typed(D(1), Qubit))));
        Formula yes = LambdaOf("h", condition,
            At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"), projectors, Rho));
        Formula no = At(Qualified("Function", "const"), new Formula.Not(Parenthesized(condition)), Rho);
        return All("ρ", Bipartite, Equal(Typed(LocalCall("pinchA", Rho), Bipartite),
            At(Qualified("dite"), condition, yes, no)));
    }

    private static Formula ResultFormula() => All("φ", Channel,
        Implies(LocalCall("IsMixedUnitary", Varphi),
            Implies(new Formula.Not(Parenthesized(LocalCall("IsIsotropic", Varphi))),
                Some("ρ", Bipartite,
                    And(At(Qualified("Matrix", "PosSemidef"), Rho),
                        And(Equal(At(Qualified("Matrix", "trace"), Rho), Typed(D(1), Complexes)),
                            And(LocalCall("IsNondegenerate", Marginal(Rho)),
                                And(LocalCall("IsNondegenerate", At(Varphi, Marginal(Rho))),
                                    NotEqual(LocalCall("pinchA", LocalCall("localMap", Varphi, Rho)),
                                        LocalCall("localMap", Varphi, LocalCall("pinchA", Rho)))))))))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Qubit => Qualified("D5", "S3", "Quantum", "FiniteDimensional", "QubitMatrix");
    private static Formula PairIndex => Seq(FinOf(D(2)), Sp, Times, Sp, FinOf(D(2)));
    private static Formula Bipartite => At(Qualified("Matrix"), Parenthesized(PairIndex),
        Parenthesized(PairIndex), Complexes);
    private static Formula Channel => Arrow(Qubit, Qubit);
    private static Formula Unitaries => At(Qualified("Matrix", "unitaryGroup"), FinOf(D(2)), Complexes);
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Marginal(Formula a) => At(Qualified("D5", "S3", "Quantum", "Information",
        "PartialTraceMutualInformation", "partialTraceRight"), a);
    private static Formula LocalCall(string name, params Formula[] args) => At(Qualified(
        "D5", "S3", "Quantum", "Information", "MixedUnitaryPinchingCommutation", name), args);
    private static Formula OfReal(Formula a) => Typed(At(Qualified("Complex", "ofReal"), a), Complexes);
    private static Formula Projection(Formula a, byte coordinate) => Seq(Parenthesized(a), Dot, D(coordinate));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula X(string name) => name switch
    {
        "φ" => Varphi,
        "γ" => GammaLower,
        "ρ" => Rho,
        _ => F.Id(name),
    };
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
