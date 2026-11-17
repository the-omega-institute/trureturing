using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class JBPositiveShiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive shifts of squares in a complete real JB algebra have inverses in the original singly generated algebra, with inverse norm at most the reciprocal shift and bijective quadratic representations on the whole ambient space.",
        H("Positive square shifts in the original JB norm"),
        Blocks(
            Paragraph(Text("Let X be a real normed vector space, S its specified real bilinear product, and u its specified unit. Data(X,S,u) means precisely symmetry, the unit law, the Jordan identity, norm(S(x,y))<=norm(x)norm(y), norm(S(x,x))=norm(x)^2, and norm(S(x,x))<=norm(S(x,x)+S(y,y)). Write C(a) for the norm-closed real span of the natural powers of a, with zeroth power u. Every norm and closure is the original one. Write U(a,v)=2 S(a,S(a,v))-S(S(a,a),v), and U(a) for this map on all of X.")),
            Describe.Lean(DescribeId.Create("ambient-fundamental-identity"),
                DeclarationHandle.Create("D5/S3/Topology/JBPositiveShift.fundamental_identity"),
                H("The ambient fundamental identity"), StatementSource.FromAuthor(F.Disp(Fundamental())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The polarized Jordan commutator identity is applied to products of a, b and v and inside multiplication contexts. Its real linear consequences give U(U(a,b),v)=U(a,U(b,U(a,v))). This algebraic identity uses no completeness, dimension, positivity or special representation hypothesis. Evaluating it at the unit gives the square transport identity S(U(c,a),U(c,a))=U(c,U(a,S(c,c))); it does not assert that U(c) preserves squares.")))),
            Describe.Lean(DescribeId.Create("original-norm-generated-inverse"),
                DeclarationHandle.Create("D5/S3/Topology/JBPositiveShift.positive_shift_generated_inverse"),
                H("Generated inverse with the original norm bound"), StatementSource.FromAuthor(F.Disp(GeneratedInverse())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume X complete. For x in C(z), associativity gives S(S(z,x),S(z,x))=S(S(S(z,z),x),x). Apply square monotonicity to sqrt(t)x and S(z,x), and then product norm domination. Cancel norm(x), treating x=0 separately, to obtain t norm(x)<=norm(S(S(z,z)+t u,x)). Powers of S(z,z) belong to C(z), so this also holds on C(S(z,z)).")),
                    Paragraph(Text("On the complete closed subspace C(S(z,z)), let B be left multiplication by S(z,z). For a unit w=B+sI, the lower bound gives norm(w inverse)<=1/s. A Neumann series makes B+sI invertible when s>norm(B). Fix t>0 and choose a natural n with t+n t>norm(B). At each of the finitely many downward steps from t+(k+1)t to t+k t, norm(t w inverse)<1; multiplying w by the corresponding Neumann unit gives the next inverse. Natural-number induction reaches B+tI. Its inverse applied to u supplies b in C(S(z,z)). The lower bound and norm(u)<=1 give norm(b)<=1/t, also when X is the zero space.")))),
            Describe.Lean(DescribeId.Create("ambient-positive-shift-inverse"),
                DeclarationHandle.Create("D5/S3/Topology/JBPositiveShift.positive_shift_quadratic_bijective"),
                H("An actual inverse on the whole ambient carrier"), StatementSource.FromAuthor(F.Disp(AmbientInverse())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Put a=S(z,z)+t u and take the generated inverse b just constructed. Both a and b lie in the associative algebra C(z), so U(a,S(b,b))=u. The ambient fundamental identity then gives U(a) U(S(b,b)) U(a)=I on every vector in X. This identity gives both injectivity and surjectivity of U(a), without a Peirce decomposition or a change of carrier.")))),
            Paragraph(Text("These are classical Jordan and Banach algebra consequences; no literature novelty is claimed. The generated inverse theorem proves the square-to-positive-shift direction and its reciprocal norm bound. It does not prove the converse characterization of squares by positive shifts, positivity of every quadratic representation, square-cone closedness, the positive interior/bijectivity criterion, a boundary kernel vector, the uniform bound in terms of an unshifted inverse, or the response support and closure statements of the original application. In particular, no quotient response, continuity of the response, special C* representation, or physical preparation follows.")))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(V(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Ex(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula P(Formula x, Formula y) => Call("S", x, y);
    private static Formula Q(Formula x, Formula y) => Call("U", x, y);
    private static Formula Square => P(V("z"), V("z"));
    private static Formula Shift => Add(Square, Call("scale", V("t"), V("u")));
    private static Formula Scope(Formula body) => All("X", V("RealNormedSpaces"),
        All("S", Call("RealBilinearMaps", V("X")), All("u", V("X"),
            Imp(Call("Data", V("X"), V("S"), V("u")), body))));
    private static Formula Complete(Formula body) => Imp(Call("Complete", V("X")), body);
    private static Formula PositiveShift(Formula body) => All("z", V("X"), All("t", V("Reals"),
        Imp(Lt(F.D(0), V("t")), body)));
    private static Formula Fundamental() => Scope(All("a", V("X"), All("b", V("X"), All("v", V("X"),
        Eq(Q(Q(V("a"), V("b")), V("v")), Q(V("a"), Q(V("b"), Q(V("a"), V("v")))))))));
    private static Formula GeneratedInverse() => Scope(Complete(PositiveShift(Ex("b", V("X"),
        And(Call("mem", V("b"), Call("C", Square)), And(Eq(P(Shift, V("b")), V("u")),
            Le(Call("norm", V("b")), Call("inverse", V("t")))))))));
    private static Formula AmbientInverse() => Scope(Complete(PositiveShift(Call("Bijective", Call("U", Shift)))));
}
