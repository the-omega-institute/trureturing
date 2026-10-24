using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalCanonicalClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalCanonicalClassification", H("Canonical finite coordinates and executable native prefixes"), Blocks(
            Describe.Lean(DescribeId.Create("original-canonical-synthesis"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalCanonicalClassification.original_canonical_synthesis"),
                H("Exact canonical classification, finite rigidity and inclusive prefixes"),
                SynthesisStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let E assign at most one defining expression to each of m states. Expressions contain finite grounds, original parameter atoms, literal Omega, fixed nonnegative powers of states, and ordered pairs. A mode fixes which parameter atoms are finite. The vector p retains every original natural parameter, including unused names and distinct names with equal values. The result holds for every p, and hence for every p satisfying an accepted arithmetic guard.")),
                    Paragraph(Text("Normalization computes the least remaining root link and applies its native substitution. A zero self-link becomes a free alias; a positive self-link forces Omega. Each step strictly decreases the finite set of root links. The resulting syntax and reconstruction are computed without inspecting any parameter value. Reconstruction maps every normalized solution to an original solution and fixes every original solution exactly.")),
                    Paragraph(Text("The canonical vector reconstructs the actual native solution with Omega at all undefined normalized states. This is the existing unrestricted CompletionTree interpretation of rho, ordered pairing and finite embedding. Arbitrary completed free assignments still give solutions, and the normalized solution is unique conditional on those assignments.")),
                    Paragraph(Text("The finite compiler examines only normalized displayed syntax, using at most the number of states in its saturation. Its successful outputs are finite expressions in grounds, original parameter atoms, fixed powers and pairs. Success is equivalent to actual canonical finiteness for every original expression. Every solution has the compiled finite value. Failure proves that the canonical value is infinite; another assignment to a free state may give a finite value.")),
                    Paragraph(Text("Completeness uses a finite native witness. An ordered pair leaves a nonempty sibling, so recursive calls descend in finite leaf count. Native power reflection preserves finiteness, and the exact Fibonacci length formula bounds the preimage leaf count by the image leaf count. Undefined canonical states and literal Omega have no finite witness. This produces a finite syntactic derivation, which the finite compiler resolves. Atomic coincidences and pairs that become atomic do not alter the argument.")),
                    Paragraph(Text("The executable prefix procedure uses finite trees only. At stage n it fills each Omega terminal by a complete finite binary tree through depth n minus one, evaluates finite terminals at the supplied parameters, and performs n guarded iterations. The stage-n vector agrees with the native canonical vector at every address of length less than n. Actual rho powers preserve that agreement and each ordered pair gains one depth.")),
                    Paragraph(Text("For the inclusive bound h, prefixTree uses stage h plus one and evaluates the entire original reconstruction. prefixReply then reads the requested finite address. The last conjunct covers all addresses of length at most h, including h equal to zero and absent descendants of early leaves. Alpha, beta, branch and absence retain their literal native meanings. The procedure does not evaluate an infinite semantic tree and uses no supplied rank, normalization oracle, semantic finiteness test or bound on p.")),
                    Paragraph(Text("For any FunctionalCase, apply the statement to its unchanged definitions and mode, then take e to be each designated original reconstruction expression. Zero state and parameter counts retain their literal empty-function meanings. Chart extraction and recognition of the accepted functional orientation are separate questions. No external novelty is asserted."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource SynthesisStatement()
    {
        var canonical = FnCall("canonical", V("E"), V("mode"), V("p"));
        var compiler = FnCall("canonicalCompile", V("E"), V("mode"), V("e"));
        var finiteValue = FnCall("embed", FnCall("finiteValue", V("p"), V("f")));
        var classification = For(StrataLint.Scribe.FormulaDsl.Seq(
            Par(EqOf(FnCall("isSome", compiler), V("true"))),
            StrataLint.Scribe.FormulaDsl.Sp, StrataLint.Scribe.FormulaDsl.Iff,
            StrataLint.Scribe.FormulaDsl.Sp, Par(FnCall("IsFinite", Value(canonical, V("e"))))),
            ("e", Expressions));
        var rigid = For(Imp(EqOf(compiler, FnCall("some", V("f"))),
            For(Imp(Sol(V("E"), V("v")), EqOf(Value(V("v"), V("e")), finiteValue)),
                ("v", Vector))), ("e", Expressions), ("f", FiniteExpressions));
        var infinite = For(Imp(EqOf(compiler, V("none")),
            StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Neg,
                Par(FnCall("IsFinite", Value(canonical, V("e")))))), ("e", Expressions));
        var prefixes = For(Imp(StrataLint.Scribe.FormulaDsl.Seq(FnCall("length", V("a")),
            StrataLint.Scribe.FormulaDsl.Sp, StrataLint.Scribe.FormulaDsl.Le,
            StrataLint.Scribe.FormulaDsl.Sp, V("h")),
            EqOf(FnCall("prefixReply", V("E"), V("mode"), V("p"), V("h"), V("e"), V("a")),
                FnCall("completionReadout", V("a"), Value(canonical, V("e"))))),
            ("h", Nat), ("e", Expressions), ("a", V("Address")));
        return Statement(KM(For(And(Sol(V("E"), canonical), classification, rigid, infinite, prefixes),
            ("E", Definitions), ("mode", Modes), ("p", Parameters))));
    }
    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat => V("Nat");
    private static Formula Fk => FnCall("Fin", V("k"));
    private static Formula Fm => FnCall("Fin", V("m"));
    private static Formula Expressions => FnCall("Expr", V("k"), V("m"));
    private static Formula Definitions => FnCall("Definitions", V("k"), V("m"));
    private static Formula Vector => FnCall("Function", Fm, V("CompletionTree"));
    private static Formula Modes => FnCall("Function", Fk, V("Bool"));
    private static Formula Parameters => FnCall("Function", Fk, Nat);
    private static Formula Reconstructions => FnCall("Function", Fm, Expressions);
    private static Formula FiniteExpressions => FnCall("FiniteExpr", V("k"));
    private static Formula Par(Formula value) => StrataLint.Scribe.FormulaDsl.Seq(
        StrataLint.Scribe.FormulaDsl.Open, value, StrataLint.Scribe.FormulaDsl.Close);
    private static Formula FnCall(string name, params Formula[] arguments) =>
        new Formula.Apply(StrataLint.Scribe.FormulaDsl.Seq(
            StrataLint.Scribe.FormulaDsl.Operatorname,
            StrataLint.Scribe.FormulaDsl.Grp(V(name))), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula EqOf(Formula left, Formula right) =>
        StrataLint.Scribe.FormulaDsl.Seq(left, StrataLint.Scribe.FormulaDsl.Sp,
            StrataLint.Scribe.FormulaDsl.Eq, StrataLint.Scribe.FormulaDsl.Sp, right);
    private static Formula Imp(Formula left, Formula right) =>
        StrataLint.Scribe.FormulaDsl.Seq(Par(left), StrataLint.Scribe.FormulaDsl.Sp,
            StrataLint.Scribe.FormulaDsl.Implies, StrataLint.Scribe.FormulaDsl.Sp, Par(right));
    private static Formula And(params Formula[] values) => StrataLint.Scribe.FormulaDsl.Seq(
        values.Select((value, index) => index == 0 ? Par(value) :
            StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Sp,
                StrataLint.Scribe.FormulaDsl.Land, StrataLint.Scribe.FormulaDsl.Sp, Par(value))).ToArray());
    private static Formula For(Formula body, params (string Name, Formula Type)[] binders)
    {
        foreach (var binder in binders.Reverse())
            body = StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Forall,
                StrataLint.Scribe.FormulaDsl.Sp, V(binder.Name), StrataLint.Scribe.FormulaDsl.Colon,
                StrataLint.Scribe.FormulaDsl.Sp, binder.Type, StrataLint.Scribe.FormulaDsl.Comma,
                StrataLint.Scribe.FormulaDsl.Sp, Par(body));
        return body;
    }
    private static Formula Some(string name, Formula type, Formula body) =>
        StrataLint.Scribe.FormulaDsl.Seq(StrataLint.Scribe.FormulaDsl.Exists,
            StrataLint.Scribe.FormulaDsl.Sp, V(name), StrataLint.Scribe.FormulaDsl.Colon,
            StrataLint.Scribe.FormulaDsl.Sp, type, StrataLint.Scribe.FormulaDsl.Comma,
            StrataLint.Scribe.FormulaDsl.Sp, Par(body));
    private static Formula KM(Formula body) => For(body, ("k", Nat), ("m", Nat));
    private static Formula Value(Formula v, Formula e) => FnCall("value", V("mode"), V("p"), v, e);
    private static Formula Sol(Formula e, Formula v) => FnCall("Solution", e, V("mode"), V("p"), v);
    private static Formula Rec(Formula r, Formula v) => FnCall("reconstruct", V("mode"), V("p"), r, v);
    private static Formula Native(Formula e, Formula g) => FnCall("native", e, V("mode"), V("p"), g);
    private static Formula Free(Formula e, Formula u, Formula g) => For(
        Imp(EqOf(App(e, V("i")), V("none")), EqOf(App(u, V("i")), App(g, V("i")))), ("i", Fm));
    private static StatementSource Statement(Formula formula) => StatementSource.FromAuthor(
        StrataLint.Scribe.FormulaDsl.Disp(formula));

}
