using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class HalfspaceConeTransferDocument : IScribeDocumentDefinition
{
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula I => F.Id("I");
    private static Formula E => F.Id("E");
    private static Formula U => F.Id("u");
    private static Formula W => F.Id("w");
    private static Formula T => F.Id("t");
    private static Formula J => F.Id("j");
    private static Formula K => F.Id("k");
    private static Formula V(Formula i) => Call("v", i);
    private static Formula A(Formula i) => Call("a", i);
    private static Formula X(Formula i) => Call("x", i);
    private static Formula Good(Formula u) => Call("Good", u);
    private static Formula Smul(Formula t, Formula u) => Seq(t, Cdot, Sp, u);
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula All(string n, Formula ty, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(n), Colon, ty)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(Formula p, Formula q) => Seq(Parenthesized(p), Land, Sp, Parenthesized(q));
    private static Formula Le(Formula p, Formula q) => Seq(p, Leq, Sp, q);
    private static Formula Lt(Formula p, Formula q) => Seq(p, F.Lt, q);
    private static Formula Sum(string n, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(n), Colon, I)), Sp, body);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Arrow(Formula p, Formula q) => Seq(p, To, Sp, q);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(F.Id(name), [.. xs]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A conical property on a finitely generated cone intersected with a halfspace follows from positive generators and positive-negative cancellation pairs.",
        H("Conical transfer through a halfspace"), Blocks(
            Describe.Lean(DescribeId.Create("appt-halfspace-transfer"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer.halfspace_transfer"),
                H("Positive-negative mass decomposition"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Good contain zero and be closed under addition and multiplication by nonnegative real scalars. Let v be a finite family and a assign a real value to each generator. A nonnegative combination whose total a-value is nonnegative satisfies Good if the generators with nonnegative value and all positive-negative cancellation pairs satisfy Good. The proof partitions the generators by the sign of a, matches negative mass with positive mass, and retains the unused positive mass. When positive mass is zero, every negatively valued coefficient vanishes."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var zero = Good(D(0));
        var add = All("u", E, All("w", E,
            Imp(And(Good(U), Good(W)), Good(Seq(U, Plus, W)))));
        var smul = All("t", R, All("u", E,
            Imp(And(Le(D(0), T), Good(U)), Good(Smul(T, U)))));
        var positive = All("j", I, Imp(Le(D(0), A(J)), Good(V(J))));
        var pairs = All("j", I, All("k", I,
            Imp(And(Lt(D(0), A(J)), Lt(A(K), D(0))),
                Good(Seq(Smul(Parenthesized(Seq(Minus, A(K))), V(J)), Plus, Smul(A(J), V(K)))))));
        var conclusion = Good(Sum("j", Smul(X(J), V(J))));
        var hypotheses = And(All("j", I, Le(D(0), X(J))),
            And(Le(D(0), Sum("j", Seq(X(J), Cdot, Sp, A(J)))), And(positive, pairs)));
        var body = Imp(hypotheses, conclusion);
        body = All("x", Arrow(I, R), body);
        body = All("a", Arrow(I, R), body);
        body = All("v", Arrow(I, E), body);
        body = Imp(And(zero, And(add, smul)), body);
        body = All("Good", Arrow(E, F.Id("Prop")), body);
        body = Seq(Bracket(Call("Fintype", I)), Sp,
            Bracket(Call("AddCommGroup", E)), Sp, Bracket(Call("Module", R, E)), Sp, body);
        return All("I", F.Id("Type"), All("E", F.Id("Type"), body));
    }
}
