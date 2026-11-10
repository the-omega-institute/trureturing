using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeGuardedFreeExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeGuardedFreeExtension", H("Arbitrary free values have a unique guarded native extension"), Blocks(
            Describe.Lean(DescribeId.Create("native-guarded-free-extension"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedFreeExtension.guarded_extension"),
                H("Simultaneous existence and uniqueness on the unrestricted completion"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("CompletionTree is the unrestricted native PFunctor.M completion. A finite system S has m states and at most one defining expression per state. Expressions are the existing distributed native syntax: a finite ground, a parameter token with a fixed natural offset, a nonnegative power of a named state, or an ordered pair. The first k tokens denote atomic(p(j)+c); the last token denotes Omega, independently of its offset. Thus parameter values are actual finite atoms, while Omega is the actual leafless completed tree. All repeated state and parameter names retain their shared values and all pair occurrences remain ordered.")),
                    Paragraph(Text("Guarded(S) says precisely that no defining right side is a decorated state at its root. Every right side that depends on states therefore has an explicit pair root. Grounds and constant tokens need no recursive guard. This condition describes a normalized system; it does not assume that a transformation from an original system has already been proved.")),
                    Paragraph(Text("For every natural parameter tuple p and every assignment f of arbitrary completed values, there exists exactly one state tuple v satisfying all definitions and agreeing with f at every undefined state. The supplied f is unrestricted: finite, infinite and non-rational free values are included. Values of f at defined states impose no extra condition. Empty state or parameter tuples have their literal meanings.")),
                    Paragraph(Text("For existence, specialize each finite parameter token to its native finite ground and represent Omega by one extra undefined state. Prescribe the actual free values and Omega on that closed boundary. The native whole-system boundary extension gives a joint solution, and the specialization identity transports every original equation back to the parameter expression. No equation or auxiliary coordinate is discarded.")),
                    Paragraph(Text("For uniqueness, compare two joint solutions with the same prescribed free values. Induction over every cutoff depth proves equality of all state prefixes simultaneously. The depth-zero cutoffs agree without a premise. At an undefined state the values agree by the boundary condition; at a constant right side they agree identically. At an explicit pair, the induction hypothesis on its children supplies the next cutoff because pairing gains one level. Native expression evaluation preserves equality of a cutoff, using the existing exact finite-prefix evaluator. Equality at every cutoff gives equality of every four-valued address reply, hence equality of the completed trees.")),
                    Paragraph(Text("The theorem supplies the arbitrary-free-value guarded extension used in canonical finite-exception assignments. It asserts no root-link normalization, original-state reconstruction equivalence, atomic replacement, image-filter preservation or full finite-exception existence equivalence. Those conclusions require their own relations on the same original system and parameter."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k = V("k"); var m = V("m"); var s = V("S"); var p = V("p");
        var f = V("f"); var v = V("v"); var w = V("w");
        var tuple = Arr(Call("Fin", m), V("CompletionTree"));
        Formula Law(Formula x) => And(Call("Satisfies", s, p, x), Call("Extends", s, f, x));
        var unique = Some("v", tuple, And(Law(v), All("w", tuple, Imp(Law(w), EqOf(w, v)))));
        var body = Imp(Call("Guarded", s), All("f", tuple, unique));
        body = All("p", Arr(Call("Fin", k), V("Nat")), body);
        body = All("S", Call("System", k, m), body);
        body = All("m", V("Nat"), body);
        return StatementSource.FromAuthor(Disp(All("k", V("Nat"), body)));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
