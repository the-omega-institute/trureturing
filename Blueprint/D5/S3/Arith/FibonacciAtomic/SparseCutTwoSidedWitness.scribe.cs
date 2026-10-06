using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SparseCutTwoSidedWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Missing and extra observation cuts give opposite failures on actual Fibonacci sources.",
        H("Two-Sided Cut Witnesses"),
        Blocks(
            Paragraph(Text("For positive widths m at most M, q(M,n) is the initial M-digit "
                + "window of the canonical Fibonacci expansion of n. The tuple sigma(m,S,n) "
                + "contains the m-digit windows of n+t for the retained natural times t in S. "
                + "K(m,S) is the union of the inclusive intervals [t+1,t+G(m)], where G(L)=F(L+2). "
                + "All coordinates of a tuple come from the same natural source.")),
            Describe.Lean(
                DescribeId.Create("sparse-cut-two-sided-witness"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SparseCutTwoSidedWitness.result"),
                H("Actual sources beyond every bound"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The statement holds for every finite S, including the empty set, "
                        + "and every natural bound B. A missing target cut gives two sources above B "
                        + "with the same observation tuple and different target windows. An extra "
                        + "observation cut gives two sources above B with the same target window "
                        + "and different observation tuples.")),
                    Paragraph(Text("At a missing cut, finitely many open coordinate arcs contain "
                        + "a common neighborhood. The target labels on its two sides differ. At "
                        + "an extra cut, one target arc contains a neighborhood, while a retained "
                        + "coordinate changes label between the two sides. Small open collars give "
                        + "both sides positive length, also at the circle seam. The golden rotation "
                        + "visits each side beyond B and avoids every endpoint. If several coordinates "
                        + "share an extra cut, a change in any one coordinate distinguishes the tuples."))),
                DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q(Formula m, Formula n) => Call("q", m, n);
    private static Formula S(Formula m, Formula times, Formula n) =>
        Seq(SigmaLower, Underscore, Grp(m, Comma, times), Open, n, Close);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m"), big = F.Id("M"), times = F.Id("S");
        Formula bound = F.Id("B"), a = F.Id("a"), b = F.Id("b"), k = F.Id("k");
        Formula cuts = Call("K", m, times), target = Call("Icc", D(1), Call("G", big));
        Formula indices = Seq(Forall, Sp, m, Comma, big, Comma, bound, Sp, InMacro, Sp, N());
        Formula hypotheses = Seq(D(1), Sp, Le, Sp, m, Sp, Le, Sp, big);
        Formula missing = Seq(Exists, Sp, k, Sp, InMacro, Sp, target, Comma, Sp,
            k, Sp, Seq(Neg, Sp, InMacro), Sp, cuts);
        Formula extra = Seq(Exists, Sp, k, Sp, InMacro, Sp, cuts, Comma, Sp,
            k, Sp, Seq(Neg, Sp, InMacro), Sp, target);
        Formula late = Seq(Exists, Sp, a, Comma, b, Sp, InMacro, Sp, N(), Comma, Sp,
            bound, Sp, Lt, Sp, a, Sp, Land, Sp, bound, Sp, Lt, Sp, b, Sp, Land, Sp);
        Formula decode = Seq(late, S(m,times,a), Sp, Eq, Sp, S(m,times,b), Sp, Land, Sp,
            Q(big,a), Sp, Neq, Sp, Q(big,b));
        Formula predict = Seq(late, Q(big,a), Sp, Eq, Sp, Q(big,b), Sp, Land, Sp,
            S(m,times,a), Sp, Neq, Sp, S(m,times,b));
        return Disp(Seq(indices, Comma, Sp, Forall, Sp, times, Sp, Subseteq, Sp, N(),
            Sp, Seq(F.Text, Grp(F.Id("finite"))), Comma, Sp, hypotheses, Sp, Implies, Sp,
            Par(Seq(Par(missing), Sp, Implies, Sp, Par(decode))), Sp, Land, Sp,
            Par(Seq(Par(extra), Sp, Implies, Sp, Par(predict)))));
    }
}
