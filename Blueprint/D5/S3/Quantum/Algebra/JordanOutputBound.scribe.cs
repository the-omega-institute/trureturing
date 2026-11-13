using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class JordanOutputBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rows of a recovered Jordan relation satisfy the square-root-three estimate, and normalized original polynomials have single actual-output remainders.",
        H("Actual-output estimates on an incomplete original carrier"),
        Blocks(
            Paragraph(Text("Let E be any real normed vector space, including the zero space, with no completeness or dimension assumption. Let S:E x E -> E be real bilinear. RecoveryStage(S,D) below means exactly the following conditions, on all original vectors: S is symmetric; S(S(x,y),S(x,x))=S(x,S(y,S(x,x))); norm(S(x,y))<=norm(x)norm(y); norm(S(x,x))=norm(x)^2; D(a,b)=-D(b,a); and D(D(a,b),c)=S(b,S(a,c))-S(a,S(b,c)). It also includes the original associator equation S(S(a,b),c)-S(a,S(b,c))=D(D(a,b),c)-D(a,D(b,c)). The first four are intermediate conclusions about the same S, rather than newly asserted consequences of raw small-window data in this module.")),
            Paragraph(Text("The actual output set A(D) is precisely {D(r,s):r,s in E}. No span, closure, output coverage, norming family, new completion, or enlarged output set is used. Norms are those of E. Applying this supplier to Unit Theorem 15.2 still requires the faithful original order-norm/JB bridge and the finite actual-output algebraic recovery from the common original certificate. Those bridges and the full bound 2 sqrt(3), Abel remainder elimination and unique extension remain open here.")),
            Describe.Lean(
                DescribeId.Create("actual-output-square-root-three"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/JordanOutputBound.actual_output_bound"),
                H("Only an actual output row needs Leibniz"),
                StatementSource.FromAuthor(F.Disp(OutputStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In this theorem D is only a total function E x E -> E: it is not assumed linear, continuous, bounded or Leibniz. For q=D(r,s), the actual row is exactly the linear commutator S(s,S(r,-))-S(r,S(s,-)). Mathlib's linearized Jordan identity, applied twice on the same carrier, proves its Leibniz rule. No special associative representation is introduced.")),
                    Paragraph(Text("Skewness gives D(a,a)=0. The actual row equation at (a,a,b) gives D(0,b)=0. The original associator at (a,a,b) then gives D(a,D(a,b))=S(a,S(a,b))-S(S(a,a),b), with exactly this sign and order. Thus the square of the actual row delta_q is H_q. Applying its proved Leibniz rule twice to S(b,b) yields H_q(S(b,b))=S(H_q(b),b)+S(b,H_q(b))+2 S(delta_q(b),delta_q(b)). Product norm domination and the square norm identity give 2 norm(delta_q(b))^2<=6 norm(q)^2 norm(b)^2. Taking the nonnegative square root gives the displayed constant; skewness gives the other slot. General rows are not declared derivations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-original-polynomial-remainder"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/JordanOutputBound.polynomial_actual_output_control"),
                H("The removed part is one original nested output"),
                StatementSource.FromAuthor(F.Disp(PolynomialStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This second supplier additionally takes D real bilinear as an explicit recovery-stage input. It does not derive that input from the original common finite certificates, and it does not assume continuity or a bound for D. Define H on original E by H(x)=S(a,S(a,x))-S(S(a,a),x). For every real polynomial q with coefficient q(0)=1, put Q=q(H), evaluated in the associative algebra of algebraic linear endomorphisms of E. Associativity of this operator algebra imposes no associativity on S.")),
                    Paragraph(Text("Polynomial.X_dvd_iff supplies r with 1-q=Xr. The original associator identity identifies H with D(a,-) squared, so that D(a,-) commutes with H and with q(H) by the pinned adjoin/centralizer supplier. Consequently b-Qb=D(a,D(a,r(H)b)) is one actual original output and D(a,Qb)=Q(D(a,b)). Apply the previous actual-output estimate to b-Qb in the second slot. All polynomial values remain in E; no completed-domain D(a,R_lambda b) is formed.")),
                    Paragraph(Text("There is no polynomial approximation, semigroup construction, inverse-root calculus, Abel integral, limit interchange, weak-star argument or finite-certificate estimate in these statements. They supply the original finite-polynomial step needed before those limits. Zero vectors, zero actual outputs and the zero-space case are included through the exact range membership and the universal normed-space scope. These are source-derived prerequisites of Unit 15.2 equations (15.3), (15.4), (15.7) and (15.8), not a proof of full Theorem 15.2 or of its later physical or algebraic consequences."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classical-seam application uses precisely the carrier A of continuous two-by-two complex matrix fields on the closed real interval [-1,1] whose value at zero is scalar. Matrices carry the L2 operator norm and A carries its inherited supremum norm, pointwise addition, complex scalar action, adjoint and constant identity. The scalar matrices form the bottom complex star subalgebra of M2(C); its finite-dimensional underlying submodule is closed. Evaluation at zero is continuous, so its inverse image is closed in C([-1,1],M2(C)). The continuous-map and closed-star-subalgebra C* instances therefore supply the original complete normed carrier. This is the literal scalar-at-zero condition, rather than a direct sum of two independent matrix algebras.")),
            Paragraph(Text("Choose two Booleans em and ep, with true corresponding to epsilon=+1 and false to epsilon=-1. At each negative parameter use em, and at each nonnegative parameter use ep. For a true choice the product is f(t)g(t); for a false choice it is g(t)f(t). At zero these formulas agree because both values are scalar, and their value is the common scalar product. Continuous.piecewise applies to the two globally continuous branch products: the frontier of the negative half of the interval is contained in the zero fiber, by Continuous.frontier_preimage_subset and frontier_Iio. Thus each of the four choices gives a continuous field in the same A. Expanding the two cases gives equation (84.1), with Jordan product one half of fg+gf and commutator fg-gf.")),
            Paragraph(Text("All ring laws are the ordinary matrix ring laws on each branch; in the reverse branch associativity reverses all three factors. The inherited powers remain valid because a matrix commutes with each of its own powers. The unit, addition, scalar action and adjoint remain the original operations. Pointwise norm submultiplicativity and ContinuousMap.norm_le give the product bound in the original supremum norm. On either branch the pointwise norm of the new product of star(f) and f is the norm of f(t) squared, using CStarRing.norm_star_mul_self or CStarRing.norm_self_mul_star. ContinuousMap.norm_eq_iSup_norm then identifies its norm with that of the original star(f)f, giving the C* identity in the same norm. Closedness supplies completeness for this unchanged metric. These laws assemble an actual unital CStarAlgebra structure for each Boolean pair on A.")),
            Paragraph(Text("For every f in A, its new square equals its original square. For every f,g, the new symmetrized product equals the original symmetrized product. The stars and selfadjoint elements also coincide. Apply CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self to the canonical spectral order of each C* structure: its positive cone is exactly the set of squares of selfadjoint elements. The identical square operation therefore gives the identical positive cone for all four choices. Positivity, completeness and the algebra laws concern these same fields and the same norm simultaneously.")),
            Paragraph(Text("The original polynomial domain is A0={c I+t P(t): c in C, P in M2(C[t])}, as a subset of this A; evaluation of P is entrywise at the same real t embedded in C. Its real domain E consists of the selfadjoint members of A0. If f=c I+t P(t) and g=d I+t Q(t), the ordinary product is cd I+t R(t), where R=c Q+d P+X P Q is again the same matrix-polynomial type. The reverse product has the corresponding reversed formula. Subtraction and complex scalar multiplication also preserve this literal domain. Hence both uniform Boolean pairs preserve A0.")),
            Paragraph(Text("Use the existing Pauli matrices sigma_x=qubitX, sigma_z=qubitZ and sigma_y=i sigma_x sigma_z. The fields a(t)=t sigma_x and b(t)=t sigma_y are selfadjoint members of the stated A0, including their zero value at the seam. The response with the source sign convention is D_e(a,b)=(i/2)(a star_e b-b star_e a)=-epsilon(t)t^2 sigma_z. For a mixed pair, membership of this actual response in A0 would make its (0,0) entry the single polynomial p=C(c)+X P00. On the positive open interval p agrees with q=-C(epsilon_plus)X^2. Polynomial.eq_of_infinite_eval_eq, applied to the infinite complex image of that real interval, forces p=q. Evaluation at -1 then forces epsilon_minus=epsilon_plus, a contradiction. Thus the response is outside A0 and outside E. If a mixed product preserved A0, applying it to these two original inputs in both orders and using the proved subtraction and scalar closure would put that response in A0. Consequently among these four products preservation of A0 holds exactly when the two signs agree. Evaluation of the response at -1 and 1 recovers both signs, so the four products are distinct.")),
            Paragraph(Text("For density, let T(t)=t in C([-1,1],C), and let P be the complex unital algebra generated by T. Since T is selfadjoint, this is also its generated star algebra. T separates the points of the compact interval, so the complex Stone-Weierstrass theorem gives closure(P)=C([-1,1],C). Evaluation at zero is a continuous complex algebra homomorphism. ContinuousMap.AlgHom.closure_ker_inter therefore gives closure(P intersect ker(eval_0))=ker(eval_0). Algebra.adjoin_singleton_eq_range_aeval identifies P with polynomial evaluations, and Polynomial.X_dvd_iff identifies its zero-at-zero members with t C[t]. The corresponding real scalar kernel description and zero-function density are supplied by ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id and ContinuousMapZero.adjoin_id_dense on the same interval.")),
            Paragraph(Text("If f(0)=c I, each entry of f-c I belongs to that scalar evaluation kernel. Multiplication by each of the four constant matrix units is continuous into A for the original L2 operator supremum norm. The kernel density thus puts every entry field in the closure of the literal A0. Summing the four matrix-unit fields and adding c I reconstructs f, proving A0 dense in this A. Coefficient conjugation with matrix transposition preserves A0. The continuous real-linear selfadjoint projection f -> (f+star(f))/2 consequently maps A0 into E and has dense image in the selfadjoint part of A. The inclusion of E is isometric for the inherited norm, and the selfadjoint part is closed and complete. LinearEquiv.extendOfIsometry, applied to the identity on E and the two actual dense isometric embeddings, supplies the completion equivalence. Hence the real normed completion of the literal E is real-linearly isometric to the selfadjoint part of this same A, with the equivalence agreeing with the original inclusion on E.")),
            Paragraph(Text("For any of the four products, equality of f star_e g and g star_e f at a point is equivalent to ordinary matrix commutation there: reversing both orders changes only the direction of that equality. At t different from zero, test with the actual field g(s)=s B for arbitrary B in M2(C). This field belongs to A and cancellation of the nonzero scalar t shows that a central f(t) commutes with every B. At zero scalarity is already the defining condition of A. Matrix.center_eq_range gives scalarity at every point. The scalar coefficient h(t)=f(t)00 is continuous, so f=h I with h in C([-1,1],C). Conversely every such scalar field commutes under every branch. Thus all four products have exactly the common center C([-1,1],C) I on this carrier.")),
            Paragraph(Text("A central idempotent is therefore h I, with h(t)^2=h(t), so h(t) belongs to {0,1}. The interval is connected and this two-point set is discrete. IsPreconnected.constant_of_mapsTo forces h to be constant. Thus every central idempotent, and in particular every central projection, is zero or the identity; both are central projections for each product. The independent sign choices on the two open halves consequently do not give a central direct-sum splitting of A.")),
            Paragraph(Text("These conclusions apply the existing matrix, continuous-map, Stone-Weierstrass, completion, connectedness, spectral-square and polynomial-identity suppliers to Section 84.3 of AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. They concern exactly the four displayed products on the original normed carrier and the stated polynomial domain. They make no classification of arbitrary response laws and no claim about a physical realization.")))));

    private static Formula E => Id("E");
    private static Formula V(string name) => Id(name);
    private static Formula Norm(Formula x) => Call("norm", x);
    private static Formula D(Formula x, Formula y) => Call("D", x, y);
    private static Formula Q(Formula x) => Call("Q", x);
    private static Formula Bound(Formula x, Formula y) =>
        Multiply(Multiply(Call("sqrt", Num(3)), Norm(x)), Norm(y));
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Scope(Formula dtype, Formula body) =>
        All("E", Id("RealNormedSpaces"), All("S", Call("RealBilinearMaps", E),
            All("D", dtype, Imp(Call("RecoveryStage", V("S"), V("D")), body))));
    private static Formula OutputStatement() => Scope(Call("TotalBinaryMaps", E),
        All("q", Call("ActualOutputs", V("D")), All("b", E,
            And(Le(Norm(D(V("q"), V("b"))), Bound(V("q"), V("b"))),
                Le(Norm(D(V("b"), V("q"))), Bound(V("q"), V("b")))))));
    private static Formula PolynomialStatement()
    {
        var a = V("a"); var b = V("b"); var q = V("q"); var r = V("r");
        var rem = Subtract(b, Q(b));
        var conclusions = And(Equal(Subtract(Num(1), q), Multiply(V("X"), r)),
            And(Equal(rem, D(a, D(a, Call("rH", b)))),
                And(Equal(D(a, Q(b)), Q(D(a, b))),
                    And(Call("mem", rem, Call("ActualOutputs", V("D"))),
                        Le(Norm(Subtract(D(a, b), Q(D(a, b)))), Bound(a, rem))))));
        return Scope(Call("RealBilinearMaps", E), All("a", E, All("b", E,
            All("q", Id("RealPolynomials"), Imp(Equal(Call("coeff", q, Num(0)), Num(1)),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("r"),
                    Id("RealPolynomials"), conclusions))))));
    }
}
