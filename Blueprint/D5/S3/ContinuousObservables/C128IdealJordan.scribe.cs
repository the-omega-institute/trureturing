using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class C128IdealJordanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole selfadjoint restriction with the original Jordan and commutator operations.", H("The Whole Selfadjoint Ideal"),
        Blocks(
            Paragraph(Text("Use Y=[0,1], U=(0,1/4) minus all 1/n for natural n at least 5, M=CStarMatrix (Fin 2) (Fin 2) Complex with its operator norm, A=the whole C0(U,M), and X=the whole selfadjoint part of C(Y,M). In C128IdealConsequences, I is the real submodule of every selfadjoint field vanishing off U. The real linear isometry equivalence j restricts I onto the whole selfadjoint part of A; its inverse is zero extension. These are organizational definitions used by the local-section annihilator and nonzero proofs.")),
            Paragraph(Text("The following are consequences of the whole complex extension theorem and the definitions, rather than additional named D5 theorems. I is closed: it is the inverse image of the closed whole complex ideal under the continuous subtype map. S(a,b)=(ab+ba)/2 is the original real Jordan product. Define the original oriented operation D(a,b)=i(ab-ba)/2. Star reverses products and conjugates i to -i, so both S and D are selfadjoint. At every point outside U an ideal factor is zero, so S(X,I) is contained in I and D(I,I) is contained in I.")),
            Disp(Statement()),
            Paragraph(Text("Here Jordan(p,q)=(pq+qp)/2 and Oriented(p,q)=i(pq-qp)/2 in A, with exactly this commutator orientation. For r in I and t in U, j(r)(t)=r(inc(t)). Applying this evaluation identity to each summand and product gives both displayed correspondence identities by extensionality on every point of U. The restricted operation inputs carry the preceding ideal-membership proofs. The onto isometry, both inverse laws, closedness, both closure laws and both complete correspondence identities are checked at their full function-space types. No additional unconsumed S/D wrapper is retained in D5.")),
            Paragraph(Text("The content-bearing host C128IdealConsequences uses j inverse on genuine selfadjoint local identity sections to prove the ambient Jordan annihilator criterion and nonzero I. This does not prove polynomial-plus-ideal completeness, its all-input S/D closure, noncommuting seeds, the full original model, or physical realization.")))));
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
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((c, i) =>
        i == 0 ? new Formula[] { Par(c) } : new Formula[] { Sp, Land, Sp, Par(c) }).ToArray());
    private static Formula Statement() =>
        And(
            Call("IsClosed", V("I")),
            All("a", V("X"), All("r", V("I"), Seq(Call("S", V("a"), V("r")), InMacro, Sp, V("I")))),
            All("r", V("I"), All("s", V("I"), Seq(Call("D", V("r"), V("s")), InMacro, Sp, V("I")))),
            All("r", V("I"), All("t", V("U"), Seq(Call("j", V("r"), V("t")), Eq, Call("r", Call("inc", V("t")))))),
            All("r", V("I"), All("s", V("I"), Seq(Call("j", Call("S", V("r"), V("s"))), Eq, Call("Jordan", Call("j", V("r")), Call("j", V("s")))))),
            All("r", V("I"), All("s", V("I"), Seq(Call("j", Call("D", V("r"), V("s"))), Eq, Call("Oriented", Call("j", V("r")), Call("j", V("s")))))));
}
