using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class RankThreeBlockAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/RankThreeBlockAvoidance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transitive finite linear incidence partitions admit a whole block outside each closure.",
        H("Whole-Block Avoidance in a Transitive Linear Incidence Geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incidence-count-contradiction"),
                DeclarationHandle.Create(Prefix + "incidence_count_contradiction"),
                H("Two uniform incidence counts cannot coexist"),
                StatementSource.FromAuthor(ArithmeticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the distinct-closure branch, b is the size of an original block, "
                    + "m is the number of blocks, and d is the common number of closures "
                    + "through a point. The two counts are b(d-1)=m-1 and "
                    + "(b+m-1)(d-1)=m-1. If b and m are both at least two, subtracting "
                    + "the equations forces (m-1)(d-1)=0; each factor is then handled "
                    + "by the corresponding positivity hypothesis. This is the arithmetic "
                    + "last step of the geometric avoidance proof below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transitive-linear-closure-block-avoidance"),
                DeclarationHandle.Create(Prefix + "exists_block_disjoint_of_transitive_linear_closures"),
                H("Each closure avoids an entire original block"),
                StatementSource.FromAuthor(AvoidanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite point type is P and the finite block-label type is I. "
                        + "The owner map o partitions P into its fibers, each of size at least two. "
                        + "The finite set L(i) contains the entire fiber over i. A group G acts "
                        + "transitively on points, acts on block labels, and preserves both ownership "
                        + "and closure incidence. Distinct assigned closures have at most one common "
                        + "point, and at least two assigned closures differ. The conclusion keeps "
                        + "the original owner fibers: for every i, some whole fiber over j misses L(i).")),
                    Paragraph(Text(
                        "Suppose a closure meets every original block. Point transitivity and "
                        + "equivariance first give transitivity on block labels, then transport this "
                        + "intersection property to every closure. If two original blocks have the "
                        + "same closure, a different closure must meet both blocks. The two intersection "
                        + "points have different owners, contradicting the one-point intersection "
                        + "bound. This treats repeated closures without identifying or replacing "
                        + "the original blocks.")),
                    Paragraph(Text(
                        "Closures are therefore distinct under the supposition. Every off-diagonal "
                        + "block-closure intersection and every pair of distinct closures has exactly "
                        + "one point. Counting the owner fibers inside L(i) gives its size b+m-1, "
                        + "where b is the size of the fiber over i and m is the number of block labels. "
                        + "The group action gives a bijection between the incident closure labels "
                        + "at any two points, so their common degree is d. Double counting incidences "
                        + "with all closures except L(i), first over the original fiber and then over "
                        + "L(i), gives b(d-1)=m-1 and (b+m-1)(d-1)=m-1. The arithmetic result above "
                        + "contradicts these equations. Multiple incidences at the same point are "
                        + "counted separately; distinct intersections need not be distinct points.")),
                    Paragraph(Text(
                        "For a simple rank-three matroid with rank-two partition blocks, the intended "
                        + "interpretation is L(i)=cl(B(i)). Applying this theorem requires proofs that "
                        + "the matroid ground set and invariant partition induce the stated finite "
                        + "actions and owner map, that automorphisms preserve these closures, that "
                        + "simple rank-two closures satisfy the one-point intersection bound, that "
                        + "rank three excludes a single common closure, and that rank-two blocks "
                        + "have at least two points. Those matroid bridges are not proved here. "
                        + "The conditional incidence theorem does not assert the full matroid "
                        + "statement or the subsequent field-rank comparison."))),
                DescribeRole.Theorem))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Sub(Formula left, Formula right) =>
        Seq(Open, left, Sp, Minus, Sp, right, Close);

    private static Formula Add(Formula left, Formula right) =>
        Seq(Open, left, Sp, Plus, Sp, right, Close);

    private static Formula Mul(Formula left, Formula right) =>
        Seq(Open, left, Sp, Cdot, Sp, right, Close);

    private static Formula ArithmeticFormula()
    {
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula d = F.Id("d");
        Formula one = D(1);
        Formula blockCount = Sub(Add(b, m), one);
        Formula firstCount = Seq(Mul(b, Sub(d, one)), Sp, Eq, Sp, Sub(m, one));
        Formula secondCount = Seq(Mul(blockCount, Sub(d, one)), Sp, Eq, Sp, Sub(m, one));
        Formula hypotheses = Seq(
            D(2), Sp, Le, Sp, b, Sp, Land, Sp,
            D(2), Sp, Le, Sp, m, Sp, Land, Sp,
            firstCount, Sp, Land, Sp, secondCount);
        return Disp(Seq(
            Forall, Sp, Open, b, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            Forall, Sp, Open, m, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            Forall, Sp, Open, d, Sp, Colon, Sp, Nat(), Close, Sp, Comma, Sp,
            hypotheses, Sp, Implies, Sp, F.Id("False"), Dot));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Ne(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Mem(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Act(Formula g, Formula x) => Seq(Open, g, Sp, Cdot, Sp, x, Close);
    private static Formula Imp(Formula p, Formula q) => Seq(Open, p, Close, Sp, Implies, Sp, q);
    private static Formula Conj(params Formula[] terms)
    {
        Formula result = Seq(Open, terms[0], Close);
        for (int i = 1; i < terms.Length; i++)
            result = Seq(result, Sp, Land, Sp, Open, terms[i], Close);
        return result;
    }
    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);

    private static Formula AvoidanceFormula()
    {
        Formula G = F.Id("G"), P = F.Id("P"), I = F.Id("I");
        Formula g = F.Id("g"), i = F.Id("i"), j = F.Id("j");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula Li = Call("L", i), Lj = Call("L", j);
        Formula ox = Call("o", x);
        Formula size = All("i", I, Seq(D(2), Sp, Le, Sp, Lvert, Sp,
            OpenBrace, x, Sp, Colon, Sp, P, Sp, Mid, Sp, Eqn(ox, i), CloseBrace,
            Sp, Rvert));
        Formula containment = All("x", P, Mem(x, Call("L", ox)));
        Formula ownerEquiv = All("g", G, All("x", P,
            Eqn(Call("o", Act(g, x)), Act(g, ox))));
        Formula lineEquiv = All("g", G, All("i", I, All("x", P,
            Seq(Mem(Act(g, x), Call("L", Act(g, i))), Sp, Iff, Sp, Mem(x, Li)))));
        Formula separation = All("i", I, All("j", I, Imp(Ne(Li, Lj),
            All("x", P, All("y", P, Imp(Conj(Mem(x, Li), Mem(y, Li),
                Mem(x, Lj), Mem(y, Lj)), Eqn(x, y)))))));
        Formula nonconstant = Ex("i", I, Ex("j", I, Ne(Li, Lj)));
        Formula conclusion = All("i", I, Ex("j", I, All("x", P,
            Imp(Eqn(ox, j), Seq(Neg, Sp, Open, Mem(x, Li), Close)))));
        Formula classes = Seq(
            Instance(Call("Group", G)), Instance(Call("Fintype", P)),
            Instance(Call("Finite", I)), Instance(Call("DecidableEq", I)),
            Instance(Call("MulAction", G, P)), Instance(Call("MulAction", G, I)),
            Instance(Call("MulActionIsPretransitive", G, P)));
        return Disp(All("G", Named("Type"), All("P", Named("Type"), All("I", Named("Type"),
            Seq(classes, All("o", Seq(P, Sp, To, Sp, I),
                All("L", Seq(I, Sp, To, Sp, Call("Finset", P)),
                    Imp(Conj(size, containment, ownerEquiv, lineEquiv, separation, nonconstant),
                        conclusion))))))));
    }

}
