using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;
internal sealed class OriginalFiniteResolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalFiniteResolution", H("Finite resolution of original functional expressions"), Blocks(
            Describe.Lean(DescribeId.Create("original-finite-resolution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution.original_finite_resolution"),
                H("Syntactic finite derivations and parameter rigidity"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Definitions assigns each original state either its displayed defining expression or no definition. The expression language is the existing completed native language: finite grounds, shared parameter tokens, decorated state occurrences and ordered pairs. A fixed mode selects a finite atomic token or Omega. Solution imposes precisely each present defining equation in the unrestricted native completion. Undefined states may take arbitrary completed values. No finiteness restriction is imposed on a valuation.")),
                    Paragraph(Text("FiniteExpr contains finite grounds, parameter atoms, fixed powers and ordered pairs. finiteValue evaluates it in the existing finite Source. The function resolve substitutes successful finite expressions for state occurrences; a free state or an Omega token prevents resolution. Starting from an empty environment, each round resolves all original defining expressions simultaneously. A successful expression is preserved in every later round. Every nonstationary round adds a state to the finite support, so the environment is stationary after the number of original states. compile uses this derived bound and then resolves the supplied original expression.")),
                    Paragraph(Text("FiniteDerivation is an independent inductive syntactic relation. Its rules are finite grounds, finite-mode tokens, expansion through an actual original defining equation, and ordered pairing. The first conclusion proves that the terminating compiler succeeds exactly on this relation. Neither the relation nor the compiler inspects natural parameter values or semantic finiteness. The second conclusion proves that every successful finite expression denotes the exact original value in every solution, uniformly over all natural parameter assignments. The original expression may be any coordinate reconstruction, and retains every repeated occurrence and shared name.")),
                    Paragraph(Text("Nat includes zero. Definitions and parameter tuples may have empty domains; constants still resolve. Parameter atoms are never compared, expanded or bounded during resolution. Equal atoms, collapsing atomic pairs and repeated states require no special exclusions because the interpretation uses actual Source trees, the native embedding and actual rho. The formula uses Mode(k), RankTuple(k) and CompletionTuple(m) for functions from Fin(k) to Bool, from Fin(k) to Nat and from Fin(m) to CompletionTree, respectively. compile and FiniteDerivation take the original definitions E and mode b. This theorem asserts finite resolution and its rigidity; it does not assert existence of a solution or identify the unresolved expressions with infinite canonical values.")),
                    Paragraph(Text("The support argument is a finite fixed-point argument on symbolic information. The semantic induction uses native rho preservation of the finite Source embedding. The result gives uniform completeness and soundness of symbolic resolution. No external novelty claim is made."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k = V("k"); var m = V("m"); var e = V("e"); var f = V("f");
        var p = V("p"); var v = V("v"); var d = V("E"); var b = V("b");
        var compiled = Call("compile", d, b, e);
        var syntax = All("e", Call("Expr", k, m), IffOf(
            EqOf(Call("isSome", compiled), V("true")), Call("FiniteDerivation", d, b, e)));
        var sound = All("e", Call("Expr", k, m), All("f", Call("FiniteExpr", k),
            Imp(EqOf(compiled, Call("some", f)),
                All("p", Call("RankTuple", k), All("v", Call("CompletionTuple", m),
                    Imp(Call("Solution", d, b, p, v),
                        EqOf(Call("value", b, p, v, e), Call("embed", Call("finiteValue", p, f))))))));
        return StatementSource.FromAuthor(Disp(All("k", V("Nat"), All("m", V("Nat"),
            All("E", Call("Definitions", k, m), All("b", Call("Mode", k), And(syntax, sound))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. arguments]);
    private static Formula EqOf(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula left, Formula right) => Seq(Par(left), Sp, Implies, Sp, Par(right));
    private static Formula IffOf(Formula left, Formula right) => Seq(Par(left), Sp, Iff, Sp, Par(right));
    private static Formula And(Formula left, Formula right) => Seq(Par(left), Sp, Land, Sp, Par(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
