using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class AffineValuationQueryLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/lettlsun2008cosets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact adaptive identification by affine prime-power valuation queries requires "
            + "at least d e (p-1) observations on one fixed input.",
        H("The affine valuation identification lower bound"),
        Blocks(
            Describe.Remark(DescribeId.Create("affine-static-essential-singleton"),
                H("An essential singleton in a coset cover"),
                Seq(V("m"), Sp, Ge, Sp, Budget()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Lettl and Sun's Theorem 1.3 implies this static inequality when m cosets "
                        + "cover the complement of one point in (Z/p^e Z)^d and all avoid that "
                        + "point. Adding the singleton gives an ordinary cover in which that "
                        + "singleton is essential. Here p is prime and e is positive.")))),
            Describe.Lean(DescribeId.Create("affine-complete-valuation-lower-bound"),
                DeclarationHandle.Create(Prefix + "affine_valuation_query_lower_bound"),
                H("One actual complete-response history attains the lower bound"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "X is the d-fold product of ZMod(p^e), Q is X times ZMod(p^e), "
                            + "and a query (a,c) returns the greatest r at most e for which "
                            + "p^r divides the representative of the affine value a dot x+c. "
                            + "The zero value has response e. Every row is allowed, including "
                            + "zero and nonprimitive rows. Hist is the finite-list space of "
                            + "query-response pairs and P is the deterministic dependent-tree "
                            + "space PassiveProtocol(Q,N). Run records all complete responses.")),
                    Paragraph(Text(
                        "The second conjunct includes arbitrary history selectors A:Hist to "
                            + "Q+X. Exec uses the stated fuel b(x), starts at the empty history, "
                            + "and returns the additional history t(x) together with x. Fuel "
                            + "only specifies terminating execution; it is not an observation. "
                            + "No common fuel bound is assumed. Every recorded query costs one, "
                            + "including saturated and uninformative queries.")),
                    Paragraph(Text(
                        "At a query choose the least response attained by the current nonempty "
                            + "candidate set. The exact response fiber remains nonempty. At an "
                            + "identifying leaf it is one point x. Every different point has a "
                            + "greater response at some query of that same history. Thus the "
                            + "nonsaturated queries supply possibly empty congruence fibers. "
                            + "Their nonempty fibers are cosets; together they cover the "
                            + "complement of x and avoid x.")),
                    Paragraph(Text(
                        "A character product has nonzero support precisely at x. Averaging "
                            + "its integral group-algebra expansion shows that its value at x "
                            + "is divisible by p^(de) in the cyclotomic integers. The absolute "
                            + "norm of each factor is p^(p^(e-1)), while the field degree is "
                            + "p^(e-1)(p-1). Norm divisibility gives the static inequality, "
                            + "including p=2 and e=1. Deterministic execution on the fixed "
                            + "point x realizes the whole chosen history.")),
                    Paragraph(Text(
                        "Finite-query normalization preserves terminal fibers and never "
                            + "increases actual query counts. Applied to the history selector, "
                            + "it transfers the dependent-tree lower bound to its original "
                            + "terminating traces."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula ExistsPoint(Formula length) =>
        Seq(Exists, Sp, V("x"), Sp, InMacro, Sp, V("X"), Comma, Sp,
            Budget(), Sp, Le, Sp, length);
    private static Formula Budget() => Seq(V("d"), Sp, V("e"), Sp,
        Par(Seq(V("p"), Minus, D(1))));
    private static Formula Length(Formula value) => Seq(Lvert, value, Rvert);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula ResultFormula()
    {
        var tree = All("T", V("P"), Imp(Call("Injective", Call("Run", V("T"))),
            ExistsPoint(Length(Call("Run", V("T"), V("x"))))));
        var exact = All("x", V("X"), Seq(
            Call("Exec", V("A"), Call("b", V("x")), Call("nil"), V("x")),
            Sp, Eq, Sp, Call("some", Par(Seq(Call("t", V("x")), Comma, V("x"))))));
        var raw = All("A", Seq(V("Hist"), Sp, To, Sp, V("Q"), Sp, Plus, Sp, V("X")),
            All("t", Seq(V("X"), Sp, To, Sp, V("Hist")),
                All("b", Seq(V("X"), Sp, To, Sp, Nat()),
                    Imp(exact, ExistsPoint(Length(Call("t", V("x"))))))));
        var conditions = Seq(Call("Prime", V("p")), Sp, Land, Sp,
            D(1), Sp, Le, Sp, V("e"), Sp, Land, Sp,
            D(1), Sp, Le, Sp, V("d"));
        return All("p", Nat(), All("e", Nat(), All("d", Nat(),
            Imp(conditions, Seq(Par(tree), Sp, Land, Sp, Par(raw))))));
    }
}
