using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class FibonacciPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integer carry histories separate Fibonacci composition labels, and every moving time in a full prefix has an operational matrix characterization.",
        H("Fibonacci Full-Prefix Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-prefix-transport"),
            DeclarationHandle.Create("D5/S3/Quantum/Transport/FibonacciPrefix.fibonacci_prefix_transport"),
            H("Integer evolution and full-prefix diagonal collapse"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here A(d)=ZMod(d)×ZMod(d), H(e)=ZMod(e)×ZMod(e), and Mat(d) is the full complex matrix algebra on A(d). All d,e≥2 are allowed, including d=e=2. "
                    + "The fixed constant phi is Real.goldenRatio=(1+sqrt(5))/2. The integer golden generator phiZ in L's evolution maps to this real constant under the existing embedding.")),
                Paragraph(Text(
                    "F(d,t) is lowTrajectory d t, the t-fold iteration of (a0,a1)↦(a1,a0+a1) modulo d. "
                    + "The actual carry k(d,a,j) is the sum of the canonical representatives of F(d,j)(a), divided by d with natural integer division. "
                    + "s(d,N,a)=carryPrefix d N a retains every position j<N. L(d,j,a)=integerTrajectory d j a is the golden integer whose coordinates are those two canonical representatives.")),
                Paragraph(Text(
                    "The high-fibre permutation q(d,e,a,0) is identity; its next step sends (h0,h1) to (h1,h0+h1+k(d,a,t)) modulo e. "
                    + "J(d,e,t)=jointTrajectory d e t sends (a,h) to (F(d,t)(a),q(d,e,a,t)(h)). "
                    + "The shared CarryTransport source defines fibonacci, carry, digit, digitJoin and transport; the theorem identifies F(d,1) with fibonacci d and J(d,e,1) with transport d e. "
                    + "Its actual matrices are lowUnitary d=permMatrixHom(fibonacci d) and jointUnitary d e=permMatrixHom(transport d e), with the displayed adjoint-left/right factors giving the column-ket convention. "
                    + "R(d,e,t,B)=movingPullback d e t B is defined by the reindex algebra homomorphisms for the moving low observation and the joint pullback.")),
                Paragraph(Text(
                    "S(d,e,N)=prefixAlgebra d e N is the intersection, over every positive time t≤N, of the comap of the lowTensor range under R(d,e,t). "
                    + "The shared lowTensor hom is B↦B tensor high identity, so membership has its literal operational meaning. "
                    + "Delta(d)=diagonalAlgebra d is independently the range of Matrix.diagonalAlgHom. The displayed tensor is the Kronecker matrix representation.")),
                Paragraph(Text(
                    "Equal N-prefixes give the integer difference evolution for every j≤N. A distinct collision at N≥1 obeys phi^N≤phi^3(d−1)^2. "
                    + "Every positive permutation period P with F(d,P)=identity already gives injectivity of s(d,P). The strict real logarithmic criterion also gives injectivity, and equality of the entire infinite carry history forces equality of the labels.")),
                Paragraph(Text(
                    "n(d)=prefixThreshold d is natural floor(3+2 log_phi(d−1))+1. The theorem proves that its integer cast equals the ordinary integer floor expression plus one. "
                    + "Every N≥n(d) gives injectivity, and n(2)=4 is an exact symbolic result. The nonnegative logarithm and the golden constants are proved inside the theorem.")),
                Paragraph(Text(
                    "For every natural t and every unrestricted complex low matrix B, R is exactly (U^t)†((V^t B (V^t)†) tensor I)U^t. "
                    + "For every N, membership in S is equivalent to vanishing entries between unequal actual prefixes. Every admitted pullback at each 1≤t≤N equals B tensor I. "
                    + "The sequence S is antitone, its intersection over positive N is Delta, every positive low permutation period gives S_P=Delta, and S_N=Delta for every N≥n(d).")),
                Paragraph(Text(
                    "The estimate is independent of e≥2, sufficient rather than optimal, and asserts no coherence at every shorter prefix. It applies to the moving full-prefix algebra, not a single-endpoint algebra. "
                    + "The iterated low and joint permutations have the specified source carry action. Under the canonical digit split x=a+d h, the shared source theorem supplies transport d e (a,h)=(fibonacci d a,(h1,h0+h1+carry d a)); the proved identifications above therefore connect the operational E trajectory to the actual digit-split source for every d,e≥2, including the non-coprime case."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula V(string name) => F.Id(name);
    private static Formula For(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Pow(Formula a, Formula n) => new Formula.Power(a, n);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Both(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.AddRange([Open, clauses[i], Close]);
        }
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula nat = Seq(Mathbb, Grp(V("N")));
        Formula integer = Seq(Mathbb, Grp(V("Z")));
        Formula d = V("d"), e = V("e"), n = V("N"), j = V("j"), p = V("P"), t = V("t");
        Formula a = V("a"), b = V("b"), matrix = V("B");
        Formula labels = Call("A", d), matrices = Call("Mat", d);
        Formula s(Formula count, Formula label) => Call("s", d, count, label);
        Formula l(Formula time, Formula label) => Call("L", d, time, label);
        Formula algebra(Formula count) => Call("S", d, e, count);
        Formula injective(Formula count) => Call("Injective", Call("s", d, count));
        Formula bound = Seq(D(3), Sp, Plus, Sp, D(2), Sp, Times, Sp,
            Call("logb", Varphi, Seq(d, Sp, Minus, Sp, D(1))));
        Formula prefixEq = Eqn(s(n, a), s(n, b));
        Formula allLabels(Formula body) => For("a", labels, For("b", labels, body));
        Formula diagonal = Call("Delta", d);
        Formula u = Call("jointUnitary", d, e), v = Call("lowUnitary", d);
        Formula up = Pow(u, t), vp = Pow(v, t);
        Formula pullback = Call("R", d, e, t, matrix);
        Formula low = Call("lowTensor", d, e, matrix);
        Formula period = For("a", labels, Eqn(Call("F", d, p, a), a));
        Formula inAlgebra = Seq(matrix, Sp, InMacro, Sp, algebra(n));
        Formula collision = For("N", nat, allLabels(Imp(
            Seq(D(1), Sp, Le, Sp, n),
            Imp(Seq(a, Sp, Neq, Sp, b),
                Imp(prefixEq,
                    Seq(Pow(Varphi, n), Sp, Le, Sp, Pow(Varphi, D(3)), Sp, Times, Sp,
                        Pow(Parenthesized(Seq(d, Sp, Minus, Sp, D(1))), D(2))))))));
        Formula evolution = For("N", nat, allLabels(Imp(prefixEq, For("j", nat,
            Imp(Seq(j, Sp, Le, Sp, n), Eqn(Seq(l(j,a), Sp, Minus, Sp, l(j,b)),
                Seq(Pow(Call("phiZ"),j), Sp, Times, Sp, Open,
                    l(D(0),a), Sp, Minus, Sp, l(D(0),b), Close)))))));
        Formula periodInjection = For("P", nat,
            Imp(Seq(D(1), Sp, Le, Sp, p),
                Imp(Parenthesized(period), injective(p))));
        Formula strictInjection = For("N", nat, Imp(Seq(bound, Sp, Lt, Sp, n), injective(n)));
        Formula histories = allLabels(Imp(Parenthesized(For("j", nat,
            Eqn(Call("k",d,a,j), Call("k",d,b,j)))), Eqn(a,b)));
        Formula castThreshold = Eqn(Call("cast", Call("n",d), integer),
            Seq(Lfloor, bound, Rfloor, Sp, Plus, Sp, D(1)));
        Formula thresholdInjection = For("N", nat,
            Imp(Seq(Call("n",d), Sp, Le, Sp, n), injective(n)));
        Formula representation = For("t", nat, For("B", matrices, Eqn(pullback,
            Seq(Call("adjoint",up), Sp, Times, Sp,
                Call("tensor", Seq(vp, Sp, Times, Sp, matrix, Sp, Times, Sp,
                    Call("adjoint",vp)), Call("I",e)), Sp, Times, Sp, up))));
        Formula support = For("N", nat, For("B", matrices, Seq(inAlgebra, Sp, Leftrightarrow, Sp,
            allLabels(Imp(Seq(s(n,a), Sp, Neq, Sp, s(n,b)), Eqn(Call("entry",matrix,a,b), D(0)))))));
        Formula exactPullbacks = For("N", nat, For("B", matrices, Imp(inAlgebra,
            For("t", nat, Imp(Seq(D(1), Sp, Le, Sp, t),
                Imp(Seq(t, Sp, Le, Sp, n), Eqn(pullback,low)))))));
        Formula periodCollapse = For("P", nat,
            Imp(Seq(D(1), Sp, Le, Sp, p),
                Imp(Parenthesized(period), Eqn(algebra(p),diagonal))));
        Formula thresholdCollapse = For("N", nat,
            Imp(Seq(Call("n",d), Sp, Le, Sp, n), Eqn(algebra(n),diagonal)));
        return Disp(For("d", nat, For("e", nat, Seq(
            OpenBracket, Call("NeZero",d), CloseBracket, Sp,
            OpenBracket, Call("NeZero",e), CloseBracket, Sp,
            Imp(Seq(D(2), Sp, Le, Sp, d),
                Imp(Seq(D(2), Sp, Le, Sp, e), Both(
                    evolution, collision, periodInjection, strictInjection, histories,
                    castThreshold, thresholdInjection, Eqn(Call("n",D(2)),D(4)),
                    representation, support, exactPullbacks, Call("Antitone",Call("S",d,e)),
                    Eqn(Call("positivePrefixIntersection",d,e),diagonal),
                    periodCollapse, thresholdCollapse)))))));
    }
}
