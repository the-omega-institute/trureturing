using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class CHSHWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A normalized Bell state and fixed Pauli observables attain the positive Tsirelson value.",
        H("A Tight CHSH Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-sqrt-two-nonzero"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_ne_zero"),
                H("The square root normalization is nonzero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Parenthesized(Seq(Sqrt, Grp(D(2)), Sp, Colon, Sp,
                        Mathbb, Grp(F.Id("C")))), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive real square root of two remains nonzero in the complex numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-sqrt-two-inverse-product"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_inv_mul_self"),
                H("The inverse square root normalization"),
                StatementSource.FromAuthor(Disp(InverseSquareRootFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the complex numbers, the product of two inverses of the positive real "
                        + "square root of two is the inverse of two. This is the normalization "
                        + "factor for the Bell density matrix."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classical comparison uses four measurable sign-valued random variables on one probability space whose law is independent of the settings. The commutative CHSH inequality bounds the absolute value pointwise by two. Integrating with respect to that same probability law gives the bound for the four correlations; finite support is not required. The Bell witness uses the Pauli Z and X observables and their normalized sum and difference to attain twice the square root of two.")),
            Paragraph(Text("For finite local positive operator-valued measurements, summing the joint trace probabilities over the second outcome replaces its effects by the identity. The first marginal therefore depends only on the first effect and the common density matrix, independently of the second setting. The argument uses normalization of each local measurement and a shared quantum state, and does not require a shared classical table of answers for all incompatible settings.")),

            Describe.Lean(
                DescribeId.Create("the-bell-density-is-a-normalized-positive-state"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state"),
                H("The Bell density is a normalized positive state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("PosSemidef")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("tr")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Close, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized Bell vector defines a rank-one positive semidefinite "
                        + "density matrix. Its trace is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bobs-fixed-observables-are-self-adjoint-involutions"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid"),
                H("Bob's fixed observables are self-adjoint involutions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), InMacro, OpenBrace, D(0), Comma, D(1), CloseBrace,
                    Comma, Esc, F.Id("B"), Underscore, F.Id("j"), Caret, Grp(Star),
                    Eq, F.Id("B"), Underscore, F.Id("j"), Sp, Land, Sp,
                    F.Id("B"), Underscore, F.Id("j"), Caret, Grp(D(2)), Eq, F.Id("I")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Bob's sum and difference of the Pauli Z and X matrices, each divided "
                        + "by square root two, are self-adjoint and square to the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-kronecker-operator-equals-the-lifted-chsh-combination"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh"),
                H("The Kronecker operator equals the lifted CHSH combination"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Eq,
                    Lifted("A", 0), Lifted("B", 0), Plus,
                    Lifted("A", 0), Lifted("B", 1), Plus,
                    Lifted("A", 1), Lifted("B", 0), Minus,
                    Lifted("A", 1), Lifted("B", 1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lift Alice's observables by tensoring on the right with the identity, "
                        + "and Bob's by tensoring on the left. The original sum of Kronecker "
                        + "products is exactly the CHSH combination of these lifted matrices; "
                        + "the superscript L denotes this lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-lifted-observables-satisfy-the-chsh-tuple-conditions"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple"),
                H("The lifted observables satisfy the CHSH tuple conditions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsCHSHTuple")), Open,
                    Lifted("A", 0), Comma, Lifted("A", 1), Comma,
                    Lifted("B", 0), Comma, Lifted("B", 1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four lifted observables are self-adjoint involutions in the "
                        + "two-qubit matrix algebra. Each lifted Alice observable commutes "
                        + "with each lifted Bob observable, as required by IsCHSHTuple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-bell-witness-attains-the-positive-tsirelson-value"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value"),
                H("The Bell witness attains the positive Tsirelson value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("tr")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Sp, F.Id("S"), Close,
                    Eq, D(2), Sqrt, Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A0 be the Pauli Z matrix and A1 the Pauli X matrix. Let B0 be " +
                        "the sum of Pauli Z and Pauli X divided by square root two, and let " +
                        "B1 be their difference divided by square root two. The named matrix S " +
                        "is the CHSH combination of the four corresponding Kronecker products. " +
                        "The state rhoBell is the rank-one density matrix obtained by flattening " +
                        "the existing bellCoefficients matrix and normalizing it by square root two.")),
                    Paragraph(Text(
                        "The checked trace is exactly positive two times square root two. The " +
                        "companion Lean certificate bell_density_is_state proves that rhoBell is " +
                        "positive semidefinite with trace one, while bob_observables_are_valid " +
                        "proves that B0 and B1 are self-adjoint involutions. Thus the equality is " +
                        "a qualified state-observable witness, not an unnormalized matrix identity.")),
                    Paragraph(Text(
                        "Mathlib's tsirelson_inequality is the upstream source for the general CHSH " +
                        "upper bound. This declaration establishes only its explicit finite-dimensional " +
                        "tightness witness: it introduces no operator norm, eigenvalue classification, " +
                        "spectral order, C-star matrix instance, or second proof of the upper bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("A two-axis application uses the same Bell projector and computational reference. Let n and m be real unit Bloch vectors, c their inner product, d its absolute value, and assume d is strictly less than one. For every positive complex four-by-four matrix rho of trace one, put q = Re tr(rho W) and f = Re tr(rho Phi), where Phi is bellDensity. The transpose below is in the basis defining Phi. All expectations use this one density matrix; independently chosen conditional sources do not satisfy this premise.")),
            new DocumentBlock.DisplayFormula(Disp(TwoAxisDefinitions())),
            Paragraph(Text("Choose s = 1 when c is nonnegative and s = -1 otherwise, and put k = n cross m. For a real vector a, O(a) is the outer product of vec(B(a)) with its conjugate. The existing B_formula_core fixes every matrix entry. Pauli multiplication gives B(v)B(a)B(v) = B(2 inner(v,a) v - norm(v)^2 a); Matrix.kronecker_mulVec_vec transfers this equality to the original tensor space. Expanding the same entries, using only the two unit-norm identities, gives the following slack identity. In the negative-c case replace m by -m: its correlation matrix and O(k) are unchanged. No rotation or replacement of the Bell reference is required.")),
            new DocumentBlock.DisplayFormula(Disp(TwoAxisSlack())),
            Paragraph(Text("Both outer products are positive by Matrix.posSemidef_vecMulVec_self_star. Since d is nonnegative and 1-d is positive, PosSemidef.add and PosSemidef.smul make the slack positive. Apply RHLinalg.trace_mul_nonneg_of_posSemidef to this slack and the actual rho. Trace linearity and trace rho = 1 give q <= 2d + 2(1-d)f. Applying the same trace theorem to rho and Phi gives f >= 0. Division by the positive number 2(1-d) yields the full lower envelope.")),
            new DocumentBlock.DisplayFormula(Disp(TwoAxisEnvelope())),
            Paragraph(Text("The feasible interval is exactly [-2,2]. For a unit axis, C is a Hermitian involution, so I+C and I-C are positive: each is half the product of I+C or I-C with its conjugate transpose. Taking their expectations in rho gives each single-axis correlation in [-1,1], hence q in [-2,2]. The states below realize every point of this interval, so this condition is also sufficient.")),
            Paragraph(Text("The upper Bell-orthogonal endpoint is sigmaPlus = O(n+s m)/(4(1+d)). Its denominator is the squared length of vec(B(n+s m)); hence it is positive with trace one. Tracelessness of B makes its Bell overlap zero, and the Pauli reflection formula gives W sigmaPlus = 2d sigmaPlus. The lower endpoint is sigmaMinus = O(k)/(2(1-c^2)). The cross-product norm identity gives trace one and positivity, while orthogonality of k to both axes gives W sigmaMinus = -2 sigmaMinus and zero Bell overlap. These formulas include c = 0 and either sign of c; the strict nonparallel condition keeps both denominators positive.")),
            Paragraph(Text("For 2d <= q <= 2, use rho = t Phi + (1-t) sigmaPlus with t = (q-2d)/(2(1-d)). The weights lie in [0,1], q is the prescribed expectation, and f = t. For -2 <= q <= 2d, use rho = t sigmaPlus + (1-t) sigmaMinus with t = (q+2)/(2+2d); then the expectation is q and f = 0. Positivity and trace one follow from the same convex-sum APIs. Thus the lower envelope is attained for every feasible q, including its endpoints, and is optimal when only q is retained.")),
            Paragraph(Text("For separable mixed states reuse the Bloch product-state estimate followed by convexity: q <= 1+d. An actual maximizing separable state is gamma-transpose tensor gamma, where u = (n+s m)/sqrt(2(1+d)) and gamma = (I+B(u))/2. The norm identity makes u unit, scalarB_posSemidef_iff gives positivity of gamma, and tracelessness of B gives trace one. Transpose and Kronecker positivity give an actual product density. Its expectation is inner(n,u)^2 + inner(m,u)^2 = 1+d. Therefore epsilon = 2-q < 1-d excludes separability. This comparison uses the original transpose convention on the first factor.")),
            Paragraph(Text("This is application exposition of finite Pauli algebra, outer-product positivity, trace positivity and convex mixtures; it supplies no additional named Lean theorem. The kernel statements cited by the Describe nodes above retain their own scope. The complete arbitrary-axis statement and its calibration clauses are not asserted to have a frozen covering declaration. Trusted effects and eta parameters, the raw-correlator-to-calibrated-correlator relation, estimated-error bounds and their 1/eta amplification, and transverse reconstruction with 1/sqrt(1-c^2) amplification require separate verification. The feasible-state construction supplies no preparation procedure, no menu classification or common-source theorem, and no optimality claim when further conditional tomography is used.")))));

    private static Formula TwoAxisDefinitions() => Seq(
        F.Id("C"), Underscore, F.Id("v"), Eq,
        new Formula.FunctionCall(FormulaIdentifier.Create("kronecker"), [
            new Formula.FunctionCall(FormulaIdentifier.Create("transpose"), [
                new Formula.FunctionCall(FormulaIdentifier.Create("B"), [F.Id("v")])]),
            new Formula.FunctionCall(FormulaIdentifier.Create("B"), [F.Id("v")])]),
        Comma, Sp, F.Id("W"), Eq, F.Id("C"), Underscore, F.Id("n"), Plus,
        F.Id("C"), Underscore, F.Id("m"));

    private static Formula TwoAxisSlack() => Seq(
        Open, D(1), Minus, F.Id("d"), Close,
        Open, D(2), F.Id("d"), F.Id("I"), Plus,
        D(2), Open, D(1), Minus, F.Id("d"), Close, Phi, Minus, F.Id("W"), Close,
        Eq, F.Id("d"), F.Id("O"), Open, F.Id("n"), Minus, F.Id("s"), F.Id("m"), Close,
        Plus, F.Id("O"), Open, F.Id("k"), Close);

    private static Formula TwoAxisEnvelope() => Seq(
        F.Id("f"), Geq, Operatorname, Grp(F.Id("max")),
        OpenBrace, D(0), Comma, D(1), Minus,
        new Formula.Fraction(Seq(D(2), Minus, F.Id("q")),
            Seq(D(2), Open, D(1), Minus, F.Id("d"), Close)), CloseBrace);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula InverseSquareRootFormula()
    {
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula root = Parenthesized(Seq(Sqrt, Grp(D(2)), Sp, Colon, Sp, complexes));
        Formula inverse = new Formula.Power(root, new Formula.Negate(D(1)));
        Formula two = Parenthesized(Seq(D(2), Sp, Colon, Sp, complexes));
        return new Formula.Relation(
            new Formula.Binary(Parenthesized(inverse), FormulaBinaryOperator.Multiply, Parenthesized(inverse)),
            FormulaRelationOperator.Equal, new Formula.Power(two, new Formula.Negate(D(1))));
    }

    private static Formula Lifted(string observable, byte setting) => Seq(
        F.Id(observable), Underscore, D(setting), Caret, Grp(F.Id("L")));
}
