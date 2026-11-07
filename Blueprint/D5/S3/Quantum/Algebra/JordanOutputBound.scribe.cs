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
                    Paragraph(Text("There is no polynomial approximation, semigroup construction, inverse-root calculus, Abel integral, limit interchange, weak-star argument or finite-certificate estimate in these statements. They supply the original finite-polynomial step needed before those limits. Empty or degenerate output sets are handled through the exact range membership and the universal zero-space scope. These are source-derived prerequisites of Unit 15.2 equations (15.3), (15.4), (15.7) and (15.8), not a proof of full Theorem 15.2 or of its later physical or algebraic consequences."))),
                DescribeRole.Theorem))));

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
