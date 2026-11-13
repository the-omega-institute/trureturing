using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class PhaseSynthesisLiftingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ContinuousObservables/PhaseSynthesisLifting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same signed-circle completion and native phases determine the compressed operator of a raw projected unitary.",
        H("Native phases on a projected unitary"),
        Blocks(
            Paragraph(Text("Fix an arbitrary finite-dimensional complex Hilbert space H, a raw endomorphism U with U*U=UU*=1, and arbitrary self-adjoint idempotents Pi and Pt. Set E=ofRaw(U,Pi,Pt), A=Pt U Pi and G=A*A. The definitions of F, V, D, R and S are those of ProjectedUnitaryLifting: V is the alternating operator word, while S is the ordered scalar reflection product.")),
            Describe.Lean(
                DescribeId.Create("same-native-phase-tuple-projected-unitary-consumer"),
                DeclarationHandle.Create(Owner + "native_phase_lifting"),
                H("One phase tuple supplies both the circle field and the projected polynomial"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, d(q)=natDegree(q), c is coefficientwise complexification, par(q,k) means vanishing coefficients of opposite parity, I=[-1,1], J=[0,1] and T=AddCircle(1). The hypotheses are k>0, d(p)<=k, par(c(p),k) and |p(x)|<=1 for every x in I. Ufield is a continuous 2 by 2 complex matrix field on T. Write z(t)=windingPhase(t), x=Re(z) and y=Im(z), retaining the sign of y. The completion F(p,B,C)(t) has entries p(x)+iB(x), iyC(x), iyC(x), p(x)-iB(x). The displayed star, determinant and real-readout constraints all concern this same field.")),
                    Paragraph(Text("The pair q(phi0,Phi)=qspPolyW(phi0,Phi) is the native left fold of stepW, starting at (exp(i phi0),0). Its matrix word Wword is D(phi0) followed by W(x)D(phi) in list order, where W(x)=[[x,i sqrt(1-x squared)],[i sqrt(1-x squared),x]]. The witnesses B,C,Ufield,phi0,Phi are obtained together from PhaseSynthesis.exists_phase_factorization. They are retained without a second completion or a new phase choice. The bound in absolute value supplies that theorem's squared bound.")),
                    Paragraph(Text("The nonempty list Phi has length k. Define Psi=cor8Phases(phi0,Phi): its first phase is phi0+last(Phi)+(k-1)pi/2, and its remaining phases are dropLast(Phi), each reduced by pi/2. Its length is exactly k. The source conversion proves Wword(phi0,Phi,x)=i to the k times S(shift(phi0,Phi),x)D(last(Phi)-pi/4), with shift=(phi0-pi/4)::map(phi-pi/2,dropLast(Phi)). Absorbing the two diagonal contributions and i to the k into the first phase identifies exactly the 00 entry with S(Psi,x). The full matrix retains its stated diagonal factor; equality of 00 entries is not an equality of the two complete words.")),
                    Paragraph(Text("Put P=c(p)+i c(B). Native multiplication gives the first row of Wword as P(x), iQ(x)sqrt(1-x squared), with Q=c(C), by induction on the native pair recursion. Hence S(Psi,x) has 00 entry P(x) on J. Define evenRoot(P)=contract(2,P) and oddRoot(P)=contract(2,divX(P)). Coefficient parity gives P(x)=evenRoot(P)(x squared) for even k, and P(x)=x oddRoot(P)(x squared) for odd k. The exact scalar-premise lifting theorem therefore applies to E with these roots. Its even output is Pi V Pi and its odd output is Pt V Pi, both on the original raw U and projections.")),
                    Paragraph(Text("All zero-dimensional spaces, zero-rank projections and singular values zero and one remain included. An even zero singular component is P(0)Pi. The restriction k>0 serves only the nonempty conversion; the general lifting theorem includes the empty list. This result implements the complex polynomial P=p+iB in the compressed block. A circuit realizing the unscaled real polynomial p with one ancilla, exact calls to the original U or U*, and a separate zero-call constant phase is a further construction. Neither real-part extraction, exact resource accounting, physical adjoint by phase negation nor deterministic output semantics follows from these block identities."))),
                DescribeRole.Theorem),
            Paragraph(Text("Conversion proof bodies are reused from Copyright (c) 2026 shosonoda, auto-res/lean-qsvt@42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/QSP/Conversion.lean, Wrot_eq_Rref, phaseZ_mul_Wrot_mul_phaseZ, seqW_cons, seqW_append_singleton, seqW_eq_seqR and seqW_apply_zero_zero_eq. The scalar multiplication uses the existing native PhaseSynthesis.mul_signal_phase. The literature is Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3, Corollary 8, Definitions 15–16 and Theorem 17. Apache-2.0 is preserved in docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. The combination is a receiving application of established results and makes no mathematical novelty claim.")))));
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
    private static Formula Sq(Formula a) => Seq(Par(a), Caret, Grp(D(2)));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula RPoly() => Seq(Mathbb, Grp(V("R")), OpenBracket, V("X"), CloseBracket);
    private static Formula Pred() => Seq(V("k"), Minus, D(1));
    private static Formula Imp(Formula a, Formula b) => Rel(Par(a), Rightarrow, b);
    private static Formula ScalarData(Formula a) => And(
        Rel(a, Eq, Seq(Sq(V("B")), Plus, Par(Seq(D(1), Minus, Sq(V("X")))), Sq(V("C")))),
        Rel(Call("d", V("B")), Leq, V("k")),
        Rel(Call("d", V("C")), Leq, Pred()),
        Imp(Rel(V("k"), Eq, D(0)), Rel(V("C"), Eq, D(0))),
        Call("par", Call("c", V("B")), V("k")), Call("par", Call("c", V("C")), Pred()));
    private static Formula CPoly() => Seq(Mathbb, Grp(V("C")), OpenBracket, V("X"), CloseBracket);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Pair() => Call("pair", V("P"), V("Q"));
    private static Formula NormIdentity() => Rel(
        Seq(V("P"), Call("conj", V("P")), Plus, Par(Seq(D(1), Minus, Sq(V("X")))), V("Q"), Call("conj", V("Q"))), Eq, D(1));

    private static Formula Statement()
    {
        var hypothesis = And(Call("rawUnitaryProjections", V("U"), V("Pi"), V("Pt")),
            Rel(D(0), Lt, V("k")), Rel(Call("d", V("p")), Leq, V("k")),
            Call("par", Call("c", V("p")), V("k")),
            All("x", V("I"), Rel(Call("abs", Call("p", V("x"))), Leq, D(1))));
        var original = And(ScalarData(Seq(D(1), Minus, Sq(V("p")))),
            Rel(V("Ufield"), Eq, Call("F", V("p"), V("B"), V("C"))),
            Rel(Seq(Call("star", V("Ufield")), V("Ufield")), Eq, D(1)),
            Rel(Seq(V("Ufield"), Call("star", V("Ufield"))), Eq, D(1)),
            All("t", V("T"), Rel(Call("det", Call("Ufield", V("t"))), Eq, D(1))),
            All("t", V("T"), Rel(Call("Re", Call("entry", Call("Ufield", V("t")), D(0), D(0))), Eq,
                Call("p", Call("Re", Call("z", V("t")))))),
            Rel(Call("length", V("Phi")), Eq, V("k")), Call("nonempty", V("Phi")),
            Rel(Call("q", V("phi0"), V("Phi")), Eq, Call("pair", V("P"), Call("c", V("C")))),
            Rel(Call("phaseProduct", V("phi0"), V("Phi")), Eq, V("Ufield")));
        var transformed = And(Rel(Call("length", V("Psi")), Eq, V("k")),
            All("x", V("J"), Rel(Call("entry", Call("S", V("Psi"), V("x")), D(0), D(0)), Eq,
                Call("eval", V("P"), V("x")))),
            Imp(Call("Even", V("k")), Rel(Seq(V("Pi"), Call("V", V("E"), V("Psi")), V("Pi")), Eq,
                Seq(V("Pi"), Call("eval", Call("evenRoot", V("P")), V("G")), V("Pi")))),
            Imp(Call("Odd", V("k")), Rel(Seq(V("Pt"), Call("V", V("E"), V("Psi")), V("Pi")), Eq,
                Seq(V("A"), Call("eval", Call("oddRoot", V("P")), V("G"))))));
        var conclusion = Ex("B", RPoly(), Ex("C", RPoly(), Ex("Ufield", Call("CircleMatrixField"),
            Ex("phi0", Real(), Ex("Phi", Call("List", Real()), And(original, transformed))))));
        return All("H", Call("FiniteComplexHilbertSpace"), All("U", Call("End", V("H")),
            All("Pi", Call("End", V("H")), All("Pt", Call("End", V("H")), All("k", Nat(),
                All("p", RPoly(), Imp(hypothesis, conclusion)))))));
    }
}
