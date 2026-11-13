using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class PhaseSynthesisDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ContinuousObservables/PhaseSynthesis.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial QSP synthesis factors continuous matrix completions on the full signed phase circle.",
        H("Polynomial phases and signed circle factorization"),
        Blocks(
            Paragraph(Text("Let d be Polynomial.natDegree, let P* be the polynomial obtained by conjugating every coefficient, and let par(P,k) mean that every coefficient of parity opposite to k vanishes. Natural subtraction k−1 is truncated. Set e(φ)=exp(iφ), and define step(φ;(R,S))=(e(φ)[XR+(X²−1)S],e(−φ)[XS+R]). Multiplication by e(φ) here means multiplication by its constant polynomial. The pair q(φ₀,Φ)=qspPolyW(φ₀,Φ) is the left fold of this step over the real list Φ, starting from (e(φ₀),0). The initial phase is separate from the list.")),
            Describe.Lean(
                DescribeId.Create("exact-budget-polynomial-qsp-phase-synthesis"),
                DeclarationHandle.Create(Owner + "exists_phases"),
                H("Every admissible pair has exactly k signal steps"),
                StatementSource.FromAuthor(Disp(PairStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ContinuousObservables/gilyensulowwiebe2019qsvt")),
                Blocks(
                    Paragraph(Text("The identity is an equality in C[X]. One initial real phase and one real list work for the whole polynomial pair. The conclusion includes length exactly k, rather than a degree-dependent upper bound. When k=0, Q=0 is explicit and P can be any unimodular constant.")),
                    Paragraph(Text("The induction lowers the budget k, including when the actual top coefficients vanish. At k=n+1, the coefficient of X^(2n+2) in the norm identity gives p_(n+1) times its conjugate equal to q_n times its conjugate. If q_n=0, both coefficients vanish and φ=0 works. Otherwise p_(n+1)/q_n has modulus one; a half argument supplies e(−φ)p_(n+1)=e(φ)q_n.")),
                    Paragraph(Text("Define the inverse pair R=e(−φ)XP+e(φ)(1−X²)Q and S=e(φ)XQ−e(−φ)P. The forward step returns (P,Q) and the norm identity is preserved. The chosen phase kills the highest coefficient of each component, while opposite parity kills the next coefficient. Thus d(R)≤n and d(S)≤n−1, with S=0 at n=0. The recursive phase list is extended on the right by φ. This is the original degree-lowering proof, including its zero-top-coefficient branch."))),
                DescribeRole.Theorem),
            Paragraph(Text("For T=AddCircle(1), z=windingPhase(t), x=Re(z) and y=Im(z), write A₂=C(T,Matrix(ZMod 2,ZMod 2,C)). The native signal W is phaseCompletion(X,0,1), so W(t)=[[x,iy],[iy,x]]. Let D(φ) be the constant diagonal field diag(e(φ),e(−φ)). The field product V(φ₀,Φ)=phaseProduct(φ₀,Φ) is the left fold U↦U·W·D(φ) starting from D(φ₀). It therefore equals D(φ₀) followed in list order by the factors W·D(φ).")),
            Describe.Lean(
                DescribeId.Create("same-sos-factors-full-signed-circle-phase-product"),
                DeclarationHandle.Create(Owner + "exists_phase_factorization"),
                H("The same sum-of-squares factors give the entire matrix field"),
                StatementSource.FromAuthor(Disp(FieldStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here c is coefficientwise complexification from R[X] to C[X], I=[−1,1], and F(p,B,C)=phaseCompletion(p,B,C). Its four entries at t are p(x)+iB(x), iyC(x), iyC(x), p(x)−iB(x). The witnesses B,C and U are obtained once from exists_phase_unitary_completion; all scalar bounds, parities, the k=0 endpoint, both star products, determinant and real readout are retained for those same witnesses.")),
                    Paragraph(Text("Set P=c(p)+i·c(B), Q=c(C). Their polynomial norm identity is the complexification of 1−p²=B²+(1−X²)C². The exact pair theorem yields φ₀,Φ. At any real x,y satisfying x²+y²=1, form E(P,Q)=[[P(x),iyQ(x)],[iyQ*(x),P*(x)]]. Direct multiplication gives E(R,S)·W·D(φ)=E(step(φ;(R,S))). Induction on the list identifies the native product with E(q(φ₀,Φ)). Since real polynomial coefficients are fixed by conjugation, E(P,Q)=F(p,B,C). Equality of all four entries gives equality in A₂.")),
                    Paragraph(Text("The signed coordinate y is essential: x²+y²=1 holds on the entire winding circle, and no step replaces y by its absolute value or by a nonnegative square root. Polynomial evaluation and the coordinate functions are continuous; the constant diagonal fields and their finite products are continuous as elements of the existing observable algebra. For p=X, the factors B=0,C=1 give the signal itself, realized by initial phase zero and the one-element list [0]. The theorem includes constant and lower-degree inputs through the exact budget induction.")),
                    Paragraph(Text("This is an existence theorem for phase lists and a full signed-circle field factorization. It does not assert an effective root algorithm, numerical stability, a query-complexity theorem, block encoding, physical realization, full QSVT or a reflection-convention equivalence."))),
                DescribeRole.Theorem),
            Paragraph(Text("Copyright (c) 2026 shosonoda. All rights reserved. The polynomial synthesis proof is reused from auto-res/lean-qsvt, commit 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/QSP/Existence.lean through exists_phases, with its consumed helpers from QSP/PolyW.lean, QSP/Poly.lean and Polynomial/Parity.lean. Apache-2.0 is preserved in docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. Namespaces, imports and visibility are adapted to the receiver's existing SOS definitions. The source bodies implement Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3, equations (4)–(8), printed pages 8–9. The continuous signed-circle application combines that established result with the interval SOS theorem and carries no originality claim for either theorem.")))));

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
    private static Formula PairStatement()
    {
        var hypotheses = And(Rel(Call("d", V("P")), Leq, V("k")),
            Rel(Call("d", V("Q")), Leq, Pred()),
            Imp(Rel(V("k"), Eq, D(0)), Rel(V("Q"), Eq, D(0))),
            Call("par", V("P"), V("k")), Call("par", V("Q"), Pred()), NormIdentity());
        var conclusion = And(Rel(Call("length", V("Phi")), Eq, V("k")),
            Rel(Call("q", V("phi0"), V("Phi")), Eq, Pair()));
        return All("k", Nat(), All("P", CPoly(), All("Q", CPoly(), Imp(hypotheses,
            Ex("phi0", Real(), Ex("Phi", Call("List", Real()), conclusion))))));
    }
    private static Formula FieldStatement()
    {
        var hypotheses = And(Rel(Call("d", V("p")), Leq, V("k")),
            Call("par", Call("c", V("p")), V("k")),
            All("x", V("I"), Rel(Sq(Call("p", V("x"))), Leq, D(1))));
        var conclusion = And(ScalarData(Seq(D(1), Minus, Sq(V("p")))),
            Rel(V("U"), Eq, Call("F", V("p"), V("B"), V("C"))),
            Rel(Seq(Call("star", V("U")), V("U")), Eq, D(1)),
            Rel(Seq(V("U"), Call("star", V("U"))), Eq, D(1)),
            All("t", V("T"), Rel(Call("det", Call("U", V("t"))), Eq, D(1))),
            All("t", V("T"), Rel(Call("Re", Call("entry", Call("U", V("t")), D(0), D(0))), Eq,
                Call("p", Call("Re", Call("z", V("t")))))),
            Rel(Call("length", V("Phi")), Eq, V("k")),
            Rel(Call("q", V("phi0"), V("Phi")), Eq, Call("pair",
                Seq(Call("c", V("p")), Plus, V("i"), Call("c", V("B"))), Call("c", V("C")))),
            Rel(Call("V", V("phi0"), V("Phi")), Eq, V("U")));
        var witnesses = Ex("B", RPoly(), Ex("C", RPoly(), Ex("U", Seq(V("A"), Underscore, Grp(D(2))),
            Ex("phi0", Real(), Ex("Phi", Call("List", Real()), conclusion)))));
        return All("k", Nat(), All("p", RPoly(), Imp(hypotheses, witnesses)));
    }
}
