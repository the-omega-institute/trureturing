using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawLargerAtomsTerminateDocument : IScribeDocumentDefinition
{
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula And(params Formula[] fs) => Seq(Open,
        Seq(fs.SelectMany((f, i) => i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()), Close);
    private static Formula Ty(string name) => Seq(Mathbb, Grp(F.Id(name)));

    public DocumentDefinition Create()
    {
        var m = F.Id("m"); var p = F.Id("p"); var i = F.Id("i"); var j = F.Id("j");
        var d = F.Id("D"); var n = F.Id("N"); var indices = Call("Fin", m);
        var minimum = Call("inf", Call("range", p));
        var hypotheses = And(
            Seq(D(2), Sp, Le, Sp, m),
            All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("p", i))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("p", i)), D(1)),
            Equal(Call("cost", p), Seq(Call("alpha", m), Sp, Cdot, Sp, minimum)));
        var conclusion = All(j, indices, Imp(Seq(minimum, Sp, Lt, Sp, Call("p", j)),
            Ex(d, Ty("N"), Ex(n, Ty("N"), Equal(Call("p", j),
                new Formula.Fraction(n, new Formula.Power(D(2), d)))))));
        var statement = All(m, Ty("N"), All(p, Seq(indices, Sp, To, Sp, Ty("R")),
            Imp(hypotheses, conclusion)));
        var q = F.Id("q"); var depth = F.Id("d");
        var delta = new Formula.Fraction(D(1), new Formula.Power(D(2), depth));
        var changed = F.Id("P");
        var transferHypotheses = Call("TransferData", Seq(m, Comma, F.Id("n"), Comma,
            p, Comma, F.Id("I"), Comma, F.Id("enum"), Comma, q, Comma, j, Comma, depth));
        var transferStatement = Seq(Forall, Sp, m, Comma, Sp, F.Id("n"), Comma, Sp,
            p, Comma, Sp, F.Id("I"), Comma, Sp, F.Id("enum"), Comma, Sp,
            q, Comma, Sp, j, Comma, Sp, depth, Comma, Sp,
            Imp(transferHypotheses, And(
                Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("P", i)), D(1)),
                Seq(Call("cost", changed), Sp, Le, Sp, Call("cost", p), Sp, Plus, Sp,
                    delta, Sp, Cdot, Sp, Call("cost", q)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every atom above the minimum in an optimal real probability law is a terminating binary rational.",
            H("Terminating Larger Atoms of Optimal Laws"), Blocks(
                Describe.Lean(DescribeId.Create("transfer"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate.transfer"),
                    H("A dyadic mass transfer"), StatementSource.FromAuthor(Disp(transferStatement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("TransferData means that p is a real vector on Fin m with sum one; I is a finite set of recipient labels; enum is an equivalence from I to Fin n; q is a nonnegative real vector on Fin n with sum one; j is outside I; and d is a natural depth. For every h<d, the integer floor of 2^h times p(j)-2^(-d) equals the floor of 2^h p(j). Set delta=2^(-d), set R(i)=q(enum(i)) on I and zero elsewhere, and set P(i)=p(i)+delta*R(i)-delta when i=j, with no subtraction otherwise.")),
                        Paragraph(Text("The transferred law has total mass one. Its floor-tail cost is at most the original cost plus delta times the recipient cost. The shallow part uses the preserved donor floors and nonnegative recipient changes; the tail uses the floor-of-sum inequality and summability of normalized floor tails.")))),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate.result"),
                    H("Larger atoms terminate"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The law p is strictly positive and normalized on m labels, with m at least two. Its minimum mass is the infimum of its finite range. The function alpha is the infimum of the dyadic floor-tail cost divided by the minimum mass over all such real laws. Attainment means that cost(p) equals alpha(m) times that minimum.")),
                        Paragraph(Text("Let I contain the labels of minimum mass t, and let e be its cardinality. A larger atom has a label outside I, so e is smaller than m. Choose an attaining e-label law q of minimum mass u. When e is one, q is the single-label law and has zero cost.")),
                        Paragraph(Text("A nonterminating larger atom has binary digits equal to one at arbitrarily large depths. Choose such a depth d with delta=2^(-d) smaller than the gap above t divided by 1+u. Remove delta from that atom and distribute it over I according to q. The resulting actual law is positive and normalized, with minimum mass exactly t+delta*u.")),
                        Paragraph(Text("The donor's shallower floor counts remain unchanged, and the recipients' floor counts do not decrease. At later depths, the donor loses an integral dyadic count and the recipients gain at least the corresponding counts of q. Summing the resulting convergent floor-tail inequalities bounds the new cost by cost(p)+delta*cost(q). Since alpha(e) is strictly smaller than alpha(m), this cost is below alpha(m) times the new minimum mass. That contradicts the defining optimal lower bound and forces every larger atom to have a terminating binary expansion."))),
                    DescribeRole.Theorem))));
    }
}
