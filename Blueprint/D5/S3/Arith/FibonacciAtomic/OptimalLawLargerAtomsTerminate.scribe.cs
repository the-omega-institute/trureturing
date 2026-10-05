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
        var count = F.Id("n"); var subset = F.Id("I"); var q = F.Id("q");
        var enumFn = F.Id("e"); var delta = F.Id("delta"); var P = F.Id("P");
        var h = F.Id("h"); var depth = F.Id("d");
        Formula Pow(Formula x) => new Formula.Power(D(2), x);
        Formula Floor(Formula x) => Seq(Lfloor, x, Rfloor);
        Formula Times(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
        Formula SumLaw(string law, Formula labels) =>
            Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, labels)), Call(law, i));
        var shallow = All(h, Ty("N"), Imp(Seq(h, Sp, Lt, Sp, depth), Equal(
            Floor(Times(Pow(h), Seq(Open, Call("p", j), Sp, Minus, Sp,
                new Formula.Fraction(D(1), Pow(depth)), Close))),
            Floor(Times(Pow(h), Call("p", j))))));
        var transferHyp = And(Equal(SumLaw("p", indices), D(1)),
            All(i, Call("Fin", count), Seq(D(0), Sp, Le, Sp, Call("q", i))),
            Equal(SumLaw("q", Call("Fin", count)), D(1)),
            Seq(Neg, Open, j, Sp, InMacro, Sp, subset, Close), shallow);
        var transferConclusion = And(Equal(SumLaw("P", indices), D(1)),
            Seq(Call("cost", P), Sp, Le, Sp, Call("cost", p), Sp, Plus, Sp,
                Times(new Formula.Fraction(D(1), Pow(depth)), Call("cost", q))));
        var transferStatement = All(m, Ty("N"), All(count, Ty("N"),
            All(p, Seq(indices, Sp, To, Sp, Ty("R")),
            All(subset, Call("Finset", indices),
            All(enumFn, Call("Equiv", subset, Call("Fin", count)),
            All(q, Seq(Call("Fin", count), Sp, To, Sp, Ty("R")),
            All(j, indices, All(depth, Ty("N"), Imp(transferHyp, transferConclusion)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every atom above the minimum in an optimal real probability law is a terminating binary rational.",
            H("Terminating Larger Atoms of Optimal Laws"), Blocks(
                Describe.Lean(DescribeId.Create("transfer"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate.transfer"),
                    H("Dyadic mass transfer bound"), StatementSource.FromAuthor(Disp(transferStatement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Here I is a finite subset of the m labels, e is a bijection from I to Fin(n), and the donor j lies outside I. Extend q by zero outside I: R(i)=q(e(i)) on I and R(i)=0 elsewhere. With delta=2^(-d), set P(i)=p(i)+delta*R(i)-delta*1(i=j). The law p has total mass one; q is nonnegative and has total mass one. No positivity condition on p is needed for this algebraic floor-tail inequality.")),
                        Paragraph(Text("Assume that subtracting delta from the donor leaves every floor count at depths h<d unchanged. Receiver floor counts can only increase at those depths. At depths d+h, the donor loses the integral count 2^h, and the receivers gain at least the floor counts of q. Both normalized floor-tail series converge, since the sum of fractional parts is nonnegative and bounded by the number of labels. Splitting at d and summing the tail bounds proves cost(P) <= cost(p)+delta*cost(q), while conservation of transferred mass proves normalization."))),
                    DescribeRole.Theorem),
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
