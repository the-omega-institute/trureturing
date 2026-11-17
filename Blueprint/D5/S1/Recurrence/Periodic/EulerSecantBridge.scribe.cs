using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerSecantBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerSecantBridge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The even ordinary Euler subsequence is the existing A000364 carrier.", H("Reusing the existing secant carrier"), Blocks(
            Paragraph(Text("a is the existing integer A000364 carrier in SecantNumberPurePeriodRefutation. E is ordinary A000111. The exponential identity gives the inverse hyperbolic cosine convolution; its even coefficients, combined with the exact ordinary sign bridge, satisfy the original secant recurrence. The existing a_unique theorem identifies the carriers.")),
            Node("secant_bridge", "Exact A000364 correspondence", Q("s",Eqn(E(Mul(D(2),V("s"))),Call("a",V("s")))),
                "Equality is in the integers, with the natural E value cast. No independent secant carrier is introduced.", DescribeRole.Theorem),
            Node("boundary_values", "All small-value boundaries", And(Eqn(E(D(0)),D(1)),And(Eqn(E(D(1)),D(1)),And(Eqn(E(D(2)),D(1)),And(Eqn(E(D(3)),D(2)),Q("k",Imp(LeN(D(4),V("k")),LtN(D(2),E(V("k"))))))))),
                "The source recurrence gives the initial values, and its zeroth summand proves monotonicity.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulersecantbridge-" + name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula And(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Imp(Formula x, Formula y) => Seq(P(x), Sp, Implies, Sp, P(y));
    private static Formula LtN(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula LeN(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Q(string names, Formula body)
    {
        foreach (var n in names.Split(' ').Reverse()) body = All(n, Nat(), body);
        return body;
    }
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..args]);
    private static Formula E(Formula n) => Call("E",n);

}
