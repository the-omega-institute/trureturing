using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class PlanarSewingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Planar path sewing", H("Planar path sewing"), Blocks(
            Paragraph(Text("NCMatching is a fixed-point-free involutive permutation " +
                "without interleaving chords. The circular rectangle order goes" +
                " left to right along the top and right to left along the " +
                "bottom. Adjacent seam elimination preserves noncrossing and " +
                "gives the path-defined rectangle composite.")),

            Node("capStep", CapScope(All("x", Fin(Add(X("m"), D(2))),
                All("y", Fin(Add(X("m"), D(2))),
                    Eq(Call("capStep", X("M"), X("j"), X("x"), X("y")),
                        Or(Eq(X("y"), Partner(X("M"), X("x"))),
                            And(Eq(X("x"), Call("Fin.castSucc", X("j"))),
                                Eq(X("y"), Call("Fin.succ", X("j"))))))))),
                "The relation is an original matching edge or the oriented adjacent seam."),
            Node("capSurgery_component_iff", CapScope(All("x", Fin(X("m")), All("y", Fin(X("m")),
                IffOf(Call("Relation.EqvGen", Call("capStep", X("M"), X("j")),
                    Call("skipPair", X("j"), X("x")), Call("skipPair", X("j"), X("y"))),
                    Or(Eq(X("y"), X("x")), Eq(X("y"),
                        Partner(Call("capSurgery", X("M"), X("j")), X("x")))))))),
                "The surviving relation is precisely equality or the mate " +
                "relation after cap surgery.",
                DescribeRole.Theorem),
            Node("boundaryEquiv", All("n", Nat(), Eq(Call("boundaryEquiv", X("n")),
                Call("Equiv.trans", Call("Equiv.boolProdEquivSum", Fin(X("n"))),
                    Call("Equiv.trans", Call("Equiv.sumCongr", Call("Equiv.refl", Fin(X("n"))),
                        Typed(N("Fin.revPerm"), Call("Equiv.Perm", Fin(X("n"))))),
                Call("Equiv.trans", N("finSumFinEquiv"), Call("finCongr", OmegaProof())))))),
                "The last congruence identifies n+n with 2*n. Equiv.toFun sends" +
                " a top port to i and a bottom port to n+(n-1-i)."),
            Node("toMatching", All("n", Nat(), All("M", NC(Mul(D(2), X("n"))),
                Eq(Call("Matching.mate", Call("toMatching", X("M"))),
                    Fn("x", Call("Boundary", X("n")),
                        Call("Equiv.toFun", Call("Equiv.symm", Call("boundaryEquiv", X("n"))),
                Partner(X("M"), Call("Equiv.toFun", Call("boundaryEquiv", X("n")), X("x")))))))),
                "This is the literal mate field. Its involution and " +
                "fixed-point-free proof fields follow from M.involutive and " +
                "M.noFixed under the displayed equivalence. Matching records " +
                "with equal mate fields are equal."),
            Node("composite_planar", All("n", Nat(), All("M", NC(Mul(D(2), X("n"))),
                All("N", NC(Mul(D(2), X("n"))), Ex("Q", NC(Mul(D(2), X("n"))),
                    Eq(Call("toMatching", X("Q")), Call("composite", Call("toMatching", X("M")),
                        Call("toMatching", X("N")))))))),
                "Path composition of two planar matchings is planar, including " +
                "products with internal loops.",
                DescribeRole.Theorem),
            Node("identity_planar", All("n", Nat(), Ex("Q", NC(Mul(D(2), X("n"))),
                Eq(Call("toMatching", X("Q")), Call("identityMatching", X("n"))))),
                "Reversal of the circular boundary gives the rectangle identity.",
                DescribeRole.Theorem),
            Node("capReconnection", CapScope(Eq(
                Call("CupCapBridgeProposal.NCMatching.partner", Call("capReconnection", X("M"),
                X("j"))),
                Call("capConjugate", X("M"), X("j")))),
                "This is the literal partner field. The involutive and noFixed " +
                "fields are capConjugate_involutive M j and " +
                "capConjugate_noFixed M j. Adjacent reconnection supplies " +
                "noncrossing; the proof fields do not change the partner " +
                "permutation."),
            Node("cupcap_planar", All("n", Nat(), All("j", Nat(),
                All("hj", Less(Add(X("j"), D(1)), X("n")),
                    Ex("Q", NC(Mul(D(2), X("n"))), Eq(Call("toMatching", X("Q")),
                        Call("cupcapMatching", X("j"), X("hj"))))))),
                "The standard adjacent cup-cap has a noncrossing representative.",
                DescribeRole.Theorem))));

    private static Formula NC(Formula n) => Call("CupCapBridgeProposal.NCMatching", n);
    private static Formula Partner(Formula m, Formula x) =>
        Call("CupCapBridgeProposal.NCMatching.partner", m, x);
    private static Formula CapScope(Formula body) => All("m", Nat(),
        All("M", NC(Add(X("m"), D(2))), All("j", Fin(Add(X("m"), D(1))), body)));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);

    private static Formula N(string name) => Q(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Bound(name, type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Nat() => N("Nat");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula OmegaProof() => Seq(N("by"), Sp, N("omega"));
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
