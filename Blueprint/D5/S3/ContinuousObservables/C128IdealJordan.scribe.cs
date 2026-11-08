using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class C128IdealJordanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole selfadjoint restriction with the original Jordan and commutator operations.", H("The Whole Selfadjoint Ideal"),
        Blocks(Describe.Lean(DescribeId.Create("c128idealjordan"),
            DeclarationHandle.Create("D5/S3/ContinuousObservables/C128IdealJordan.whole_selfadjoint_ideal"),
            H("Closed ideal and exact original operations"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Use the same Y, U, operator-norm matrix algebra M and whole C0 algebra A. X is the whole selfadjoint part of C(Y,M), and I is the real submodule consisting of every selfadjoint field in the whole zero-off-U ideal J. The map j is the real linear isometry equivalence from I onto the whole selfadjoint part of A. Its inverse is zero extension; j itself is restriction.")),
                Paragraph(Text("S(a,b)=(ab+ba)/2 is the original real Jordan product and D(a,b)=i(ab-ba)/2 is the original oriented commutator. I is closed in X and S(X,I) is contained in I. For every r,s in I, D(r,s) belongs to I. The displayed Jordan and Oriented operations on A have precisely these same formulas, and j preserves both formulas on every pair. No completeness claim is made for a polynomial-plus-ideal original domain.")),
                Paragraph(Text("The inverse restriction and exact norm of the whole complex extension produce the real linear isometry equivalence. Its selfadjointness follows from star preservation. The ideal laws follow pointwise from zero outside U. Subsequent local-section arguments use the onto map j to detect ambient Jordan annihilation."))),
            DescribeRole.Theorem))));
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
