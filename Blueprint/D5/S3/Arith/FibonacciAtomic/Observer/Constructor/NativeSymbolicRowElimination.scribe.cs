using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeSymbolicRowEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sort-sensitive symbolic row exterior elimination",
        H("Exact inversion of a complete symbolic exterior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-symbolic-exterior-match-exact"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination.exterior_match_exact"),
                H("A symbolic exterior matches exactly when its finite bindings hold"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A symbolic exterior has Boolean leaves, residual variables and literal address holes. The matcher descends through ordered pair constructors, rejects constructor and hole mismatches, and decodes a target subtree into a source term only when that subtree contains no address hole. Every successful variable match contributes an explicit binding to a finite list; repeated variables are retained as repeated bindings.")),
                    Paragraph(Text("For every valuation, the theorem equates the filled symbolic exterior with an arbitrary concrete hole exterior exactly with the existence of the matcher output whose bindings all evaluate to the valuation. Thus malformed labels and absent or literal holes are rejected by the matcher, while arbitrary free subtrees remain unconstrained except for the returned bindings. This is the structural producer consumed by the later row compiler; it does not eliminate interpreted positive history equations or assert the full NIC4.3 chart."))),
                DescribeRole.Theorem)
        )));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);

    private static Formula Statement()
    {
        var x = V("X");
        var p = V("p");
        var u = V("u");
        var v = V("v");
        var bs = V("bs");
        var filled = C("exteriorFill", v, p);
        var matched = C("matchExterior", p, u);
        var binding = C("bindingHolds", v, bs);
        var rhs = Some("bs", C("List", C("Prod", x, C("Term", x))),
            And(EqOf(matched, C("some", bs)), binding));
        return All("X", V("Type"), All("p", C("SymbolicExterior", x),
            All("u", V("HoleExterior"), All("v", Arr(x, V("Source")), IffOf(EqOf(filled, u), rhs)))));
    }
}
