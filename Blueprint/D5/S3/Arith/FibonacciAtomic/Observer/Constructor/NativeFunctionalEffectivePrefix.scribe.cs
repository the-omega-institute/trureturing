using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeFunctionalEffectivePrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFunctionalEffectivePrefix", H("Effective prefixes of canonical native solutions"), Blocks(
            Describe.Lean(DescribeId.Create("canonical-native-effective-prefix"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalEffectivePrefix.effective_prefix"),
                H("Finite execution recovers every original canonical prefix"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let k, m and r be arbitrary natural numbers. Each of the m states has an optional defining expression S. Expressions contain finite native grounds, shared parameter tokens with fixed offsets, fixed nonnegative powers of states, and ordered pairs. The mode of a token chooses its finite atomic value or Omega. The tuple p supplies arbitrary natural parameters. Each original coordinate R(i) is an arbitrary expression in these same states and tokens. All optional equations, repeated names and unused auxiliary states remain part of the common system.")),
                    Paragraph(Text("For an inclusive observation depth h, prefixProgram returns a finite pattern at cutoff depth h+1. The pattern records the actual root and every descendant through depth h. Leaves retain their two distinct labels, their descendants are absent, and holes occur only at reached positions at the next depth. The native substitution sends alpha to beta, beta to the ordered pair (beta, alpha), and preserves existing branches. Applying its finite pattern action therefore includes positions born by substitution, without identifying them with original absent descendants.")),
                    Paragraph(Text("The program specializes finite parameter tokens to their actual finite trees and represents every divergent token by one additional undefined state. It then works entirely with finite patterns. A pass substitutes all state patterns simultaneously into their defining expressions; undefined states receive the all-branch pattern. The initial state is also all-branch. Grounds are cut directly, fixed powers use the finite pattern substitution, and pairs use the two truncated child patterns. No canonical completion or limit is evaluated by the program.")),
                    Paragraph(Text("At depth d there are finitely many patterns, with P(0)=1 and P(d+1)=2+P(d)^2. For m+1 specialized states there are P(d)^(m+1) simultaneous pattern assignments. The program executes at most that many passes, stopping earlier when a pass leaves the entire state tuple unchanged, then evaluates each original reconstruction. The bound is computed by this recurrence rather than by enumerating patterns. This is a termination bound, with no efficiency claim. It is independent of the supplied parameters and the equation sizes; expanding a finite parameter terminal still incurs its actual finite evaluation cost.")),
                    Paragraph(Text("For every raw native expression E and cutoff depth d, evalPrefix(d, cutoff(d,v), E) equals cutoff(d,value(v,E)). This identity holds for arbitrary completed state values. It includes every nonnegative decorator through the native finite-prefix substitution law and every ordered pair through truncation of its two child cutoffs.")),
                    Paragraph(Text("Every finite pass is exactly the cutoff of the corresponding original native approximant. The leaf order is increasing along these approximants. If two prefix states agree, every intermediate prefix state agrees with them: a leaf present at the earlier stage persists, and a leaf present at the intermediate stage is already present at the later stage. The finite pigeonhole principle gives a repetition before the stated bound. The deterministic prefix transition then makes all later prefixes equal.")),
                    Paragraph(Text("The original native limit has exactly the leaves occurring at some approximant stage. Persistence and prefix stabilization imply that its cutoff is the stabilized finite pattern. Evaluating an arbitrary reconstruction commutes with cutoff, so the output equals the cutoff of value(mode,p,canonicalSolution(S,mode,p),R(i)) for every supplied p, h and i. This includes finite and infinite originals, empty parameter or state tuples, aliases, positive-power cycles, recursive pairs, equal finite parameter values and infinite unused auxiliaries.")),
                    Paragraph(Text("This result concerns effective prefixes of the existing canonical native solution. It imposes no finite-size, rank or acyclicity restriction, and needs no normalization or stabilization oracle. It does not supply root normalization, uniqueness for arbitrary assigned free states, either whole-system representation map, a normalization correspondence, or the remaining syntactic graph criterion. It assigns no sign to a limit and asserts no rigidity for canonically infinite coordinates in other solutions."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k = V("k"); var m = V("m"); var r = V("r"); var s = V("S");
        var b = V("b"); var p = V("p"); var rec = V("R"); var h = V("h"); var i = V("i");
        var output = Call("prefixProgram", s, b, p, rec, h, i);
        var original = Call("value", b, p, Call("canonicalSolution", s, b, p), Call("at", rec, i));
        var body = Seq(output, Sp, Eq, Sp, Call("cutoff", Seq(h, Plus, Num(1)), original));
        return StatementSource.FromAuthor(Disp(
            All("k", V("Nat"), All("m", V("Nat"), All("r", V("Nat"),
                All("S", Call("FunctionalSystem", k, m), All("b", Call("Modes", k),
                    All("p", Call("Parameters", k), All("R", Call("Reconstructions", k, m, r),
                        All("h", V("Nat"), All("i", Call("Fin", r), body)))))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
