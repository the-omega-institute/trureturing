using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class ProjectedUnitaryLiftingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ContinuousObservables/ProjectedUnitaryLifting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial identities for scalar reflection words lift to arbitrary projected unitaries.",
        H("Projected unitary polynomial lifting"),
        Blocks(
            Paragraph(Text("Let H be any finite-dimensional complex inner product space, including dimension zero. An encoding E consists only of a unitary U and two arbitrary orthogonal projections Pi and Pt on H. They need not have equal rank. Set A=Pt U Pi and G=A* A, where star means adjoint. The internal positive-idempotent predicate for projections is equivalent to self-adjoint idempotence; ofRaw constructs E directly from these equations. All products act from the right.")),
            Paragraph(Text("Write e(theta)=exp(i theta), F(J,theta)=e(theta)J+e(-theta)(1-J), and V(E,[])=1. For theta::Theta, V is F(Pt,theta) U V(E,Theta) when the tail length is even and F(Pi,theta) U* V(E,Theta) otherwise. Put s(x)=sqrt(1-x squared), D(theta)=diag(e(theta),e(-theta)), R(x)=[[x,s(x)],[s(x),-x]], and S(Psi,x)=the list-ordered product of D(theta)R(x), with empty product 1. These are phaseOp, altSeq, Rref, phaseZ and seqR in Lean.")),
            Describe.Lean(
                DescribeId.Create("arbitrary-singular-pair-alternating-action"),
                DeclarationHandle.Create(Owner + "altSeq_apply_singular"),
                H("Action on an arbitrary singular pair"),
                StatementSource.FromAuthor(Disp(SingularStatement())),
                AssessedProvenance.FromLiterature("gilyensulowwiebe2019qsvt"),
                Blocks(Paragraph(Text("Here Pair(E,v,sigma) means exactly Pi v=v, 0<=sigma<=1 and A* A v=sigma squared v. No normalization is required, and v=0 is allowed. Set l=0 when sigma=0 and l=A v/sigma otherwise; set lt=(1-Pt)U v/s(sigma) and rp=(1-Pi)U* l/s(sigma), using the complex inverse with inverse(0)=0. If the list length is even, b=v and c=rp; otherwise b=l and c=lt. The formula gives the entire vector, including its component outside the projected output.")),
                    Paragraph(Text("The defining equations imply Uv=sigma l+s lt, U* l=sigma v+s rp, U rp=s l-sigma lt and U* lt=s v-sigma rp. For sigma<1 these follow by cancellation of s and unitarity. At sigma=1, equality of the projected and full norms forces the complementary vector to vanish by Pythagoras. At sigma=0, l=rp=0 and lt=Uv. Projector phases multiply the range vector by e(theta) and the complementary vector by e(-theta). Induction on the phase list now follows the two entries of the scalar reflection recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-scalar-premise-compressed-operator-lifting"),
                DeclarationHandle.Create(Owner + "polynomial_lifting"),
                H("The scalar 00 identity determines the compressed operator"),
                StatementSource.FromAuthor(Disp(LiftingStatement())),
                AssessedProvenance.FromLiterature("gilyensulowwiebe2019qsvt"),
                Blocks(Paragraph(Text("The scalar premise is required for every real x in [0,1], for an arbitrary complex polynomial R. Evaluation R(G) is Polynomial.aeval. The Gram operator restricts to the input range; its symmetric spectral theorem supplies a complete orthonormal basis there, with eigenvalues sigma squared in [0,1]. The singular-pair action on each basis vector and polynomial evaluation at its eigenvalue give the two equalities. Both sides vanish on the input complement; in the odd case this uses commutation of Pi with G and every polynomial in G.")),
                    Paragraph(Text("The input basis includes every zero eigenvalue, even when the output projection has smaller rank. Consequently the even action on an input vector in ker(A) is R(0) times that vector. The empty list is included and gives the input projection for R=1. No full-rank assumption, rank equality, nonzero singular-value assumption or Hermitian restriction on A occurs. The scalar premise can constrain only values on the singular spectrum, but the theorem assumes the stated identity on the whole interval.")),
                    Paragraph(Text("These are compressed operator identities. They do not identify a projected block with a deterministic output channel, synthesize a real-part ancilla circuit, prove exact query accounting, or establish a physical adjoint by negating phases. The phase gate itself need not have determinant one."))),
                DescribeRole.Theorem),
            Paragraph(Text("The structural proofs are reused from shosonoda, auto-res/lean-qsvt, immutable revision 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/SVT/SVD.lean, TwoFrame.lean and SingularPair.lean, with the required original Operator/Basic.lean, Encoding/Projected.lean, QSP/Conventions.lean, SVT/PhaseOp.lean, AltSeq.lean, EigenBasis.lean, SVTransform.lean and TwoVector.lean declarations. The mathematical source is Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Definitions 15–16 and Theorem 17, printed pages 17–19. Copyright (c) 2026 shosonoda and copied Copyright (c) 2025 Hayata Yamasaki are retained under Apache-2.0; the full license is docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. This application makes no mathematical novelty claim.")))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula Par(Formula p) => Seq(Open, p, Close);
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(v), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(v), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((c, i) =>
        i == 0 ? new Formula[] { Par(c) } : new Formula[] { Sp, Land, Sp, Par(c) }).ToArray());
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Rel(Par(a), Rightarrow, b);
    private static Formula Sq(Formula a) => Seq(Par(a), Caret, Grp(D(2)));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula CPoly() => Seq(Mathbb, Grp(V("C")), OpenBracket, V("X"), CloseBracket);
    private static Formula RPoly() => Seq(Mathbb, Grp(V("R")), OpenBracket, V("X"), CloseBracket);
    private static Formula Len() => Call("length", V("Psi"));

    private static Formula Enc() => Call("Encoding", V("H"));
    private static Formula Word() => Call("V", V("E"), V("Psi"));
    private static Formula SingularStatement() => All("H", Call("FiniteComplexHilbertSpace"),
        All("E", Enc(), All("v", V("H"), All("sigma", Real(), All("Psi", Call("List", Real()),
            Imp(Call("Pair", V("E"), V("v"), V("sigma")),
                Rel(Call("apply", Word(), V("v")), Eq,
                    Seq(Call("entry", Call("S", V("Psi"), V("sigma")), D(0), D(0)), V("b"), Plus,
                        Call("entry", Call("S", V("Psi"), V("sigma")), D(1), D(0)), V("c")))))))));
    private static Formula LiftingStatement()
    {
        var scalar = All("x", V("I"), Rel(Call("entry", Call("S", V("Psi"), V("x")), D(0), D(0)), Eq,
            Call("cases", Call("Even", Len()), Call("eval", V("R"), Sq(V("x"))),
                Seq(V("x"), Call("eval", V("R"), Sq(V("x")))))));
        var even = Imp(Call("Even", Len()), Rel(Seq(V("Pi"), Word(), V("Pi")), Eq,
            Seq(V("Pi"), Call("eval", V("R"), V("G")), V("Pi"))));
        var odd = Imp(Call("Odd", Len()), Rel(Seq(V("Pt"), Word(), V("Pi")), Eq,
            Seq(V("A"), Call("eval", V("R"), V("G")))));
        return All("H", Call("FiniteComplexHilbertSpace"), All("E", Enc(),
            All("Psi", Call("List", Real()), All("R", CPoly(), Imp(scalar, And(even, odd))))));
    }
}
