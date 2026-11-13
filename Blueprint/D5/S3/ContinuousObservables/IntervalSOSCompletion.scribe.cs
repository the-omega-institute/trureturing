using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class IntervalSOSCompletionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ContinuousObservables/IntervalSOSCompletion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity-controlled interval sums of squares construct continuous determinant-one unitary fields on the native phase circle.",
        H("Interval sums of squares and a signed circle completion"),
        Blocks(
            Paragraph(Text("Write T=AddCircle(1), z=windingPhase:T→C and A₂=C(T,Matrix(ZMod 2,ZMod 2,C)), the existing CyclicObservable 2 algebra. Write R[X] for real polynomials, c(P) for complexification and d(P) for Polynomial.natDegree. Every subtraction k−1 of natural degrees is truncated. Even(c(A)) means that all odd coefficients vanish. par(P,k) means HasParity(c(P),k): coefficients of parity opposite to k vanish. These coefficient definitions include the zero polynomial.")),
            Describe.Lean(
                DescribeId.Create("even-interval-nonnegative-polynomial-weighted-sos"),
                DeclarationHandle.Create(Owner + "exists_sumsq_decomposition"),
                H("The complete scalar endpoint"),
                StatementSource.FromAuthor(Disp(ScalarStatement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ContinuousObservables/gilyensulowwiebe2019qsvt")),
                Blocks(
                    Paragraph(Text("Here I is the closed real interval [−1,1], and X is the polynomial indeterminate. The identity is global in R[X], although nonnegativity is assumed only on I. The zero polynomial and k=0 are included; the latter has C=0 explicitly, so the natural-degree convention loses no endpoint condition.")),
                    Paragraph(Text("The original construction removes one elementary factor from A at a time. A nonreal squared root gives a real conjugate quartic with a degree-two SOS representation. A real squared root outside (0,1) gives a signed quadratic with a degree-one representation, including zero and both endpoints. An interior real root is at least double, since a simple root would force a sign change. This supplies a square factor.")),
                    Paragraph(Text("Divisibility descends from the complexification to real coefficients. The cofactor is even and nonnegative away from the finite zero set of the removed factor. One-sided continuity extends this inequality over the entire closed interval. Each removal reduces the degree by twice a positive natural number; strong induction reconstructs A. The product step uses (B₁²+wC₁²)(B₂²+wC₂²)=(B₁B₂−wC₁C₂)²+w(B₁C₂+B₂C₁)², with w=1−X². Multiplication by the identity X²+(1−X²)=1 adjusts the parity budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-real-parity-polynomial-native-unitary-completion"),
                DeclarationHandle.Create(Owner + "exists_phase_unitary_completion"),
                H("A continuous field with both star products and determinant one"),
                StatementSource.FromAuthor(Disp(FieldStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The symbol F(p,B,C) denotes phaseCompletion. At t in T set x=Re(z(t)) and y=Im(z(t)). Its entries are F₀₀=p(x)+iB(x), F₀₁=F₁₀=iyC(x), F₁₁=p(x)−iB(x). Thus the field uses the existing windingPhase in its actual entries and has rows and columns indexed by ZMod 2. The existential statement retains all degree, parity and zero-degree conditions of the scalar theorem, as well as the actual field formula.")),
                    Paragraph(Text("The bound on p makes A=1−p² nonnegative on I; its degree is at most 2k and it is even because p has parity k. The scalar endpoint gives B,C. Since |z|=1, x²+y²=1 and x belongs to I. Evaluation gives p(x)²+B(x)²+y²C(x)²=1. Polynomial evaluation and the real and imaginary coordinate maps are continuous, so every matrix entry is continuous, including both interval endpoints and the circle seam. Matrix multiplication and conjugation now give both star products and determinant one; the upper-left real part is p(x).")),
                    Paragraph(Text("This is the signed-circle convention. On the upper semicircle y=√(1−x²), so its matrix agrees with Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3 equation (3). On the lower semicircle the off-diagonal sign differs from the square-root pullback. There is no phase factorization, algorithmic root-finding or query bound, block encoding, physical implementation or full QSVT claim. The elementary matrix normalization is an application; the substantial proof content is the original root, double-root, cofactor and induction construction."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source custody: Copyright (c) 2026 shosonoda. All rights reserved. The selected original statement/proof bodies are from auto-res/lean-qsvt at commit 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/Polynomial/Parity.lean, Polynomial/SqrtPart.lean, QSP/Poly.lean, QSP/PolyW.lean and QSP/Complementary.lean. They are licensed under Apache-2.0; the full text is docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. The assembly adapts namespaces, helper visibility, imports and exposition, and adds the native field application. The mathematical source is Lemma 6 of Gilyen–Su–Low–Wiebe, DOI 10.1145/3313276.3316366, with the verified arXiv v1 locator in the Library note. This is source reuse, not an originality claim. An equivalent result in the receiver's pinned Mathlib should replace the transplant when available.")))));

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
    private static Formula Poly() => Seq(Mathbb, Grp(V("R")), OpenBracket, V("X"), CloseBracket);
    private static Formula Pred() => Seq(V("k"), Minus, D(1));
    private static Formula Imp(Formula a, Formula b) => Rel(Par(a), Rightarrow, b);
    private static Formula ScalarData(Formula a) => And(
        Rel(a, Eq, Seq(Sq(V("B")), Plus, Par(Seq(D(1), Minus, Sq(V("X")))), Sq(V("C")))),
        Rel(Call("d", V("B")), Leq, V("k")),
        Rel(Call("d", V("C")), Leq, Pred()),
        Imp(Rel(V("k"), Eq, D(0)), Rel(V("C"), Eq, D(0))),
        Call("par", V("B"), V("k")), Call("par", V("C"), Pred()));
    private static Formula ScalarStatement() => All("k", Nat(), All("A", Poly(), Imp(And(
        Call("Even", Call("c", V("A"))),
        Rel(Call("d", V("A")), Leq, Seq(D(2), V("k"))),
        All("x", V("I"), Rel(D(0), Leq, Call("A", V("x"))))),
        Ex("B", Poly(), Ex("C", Poly(), ScalarData(V("A")))))));
    private static Formula FieldStatement()
    {
        var hypotheses = And(
            Rel(Call("d", V("p")), Leq, V("k")),
            Call("par", V("p"), V("k")),
            All("x", V("I"), Rel(Sq(Call("p", V("x"))), Leq, D(1))));
        var readout = All("t", V("T"),
            Rel(Call("Re", Call("entry", Call("U", V("t")), D(0), D(0))), Eq,
                Call("p", Call("Re", Call("z", V("t"))))));
        var conclusion = And(
            ScalarData(Seq(D(1), Minus, Sq(V("p")))),
            Rel(V("U"), Eq, Call("F", V("p"), V("B"), V("C"))),
            Rel(Seq(Call("star", V("U")), V("U")), Eq, D(1)),
            Rel(Seq(V("U"), Call("star", V("U"))), Eq, D(1)),
            All("t", V("T"), Rel(Call("det", Call("U", V("t"))), Eq, D(1))),
            readout);
        var witnesses = Ex("B", Poly(), Ex("C", Poly(),
            Ex("U", Seq(V("A"), Underscore, Grp(D(2))), conclusion)));
        return All("k", Nat(), All("p", Poly(), Imp(hypotheses, witnesses)));
    }
}
