using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeFunctionalObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFunctionalObstruction", H("Finite dependencies of native functional systems"), Blocks(
            Describe.Lean(DescribeId.Create("finite-native-dependency-cycles"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_cycle_is_silent"),
                H("A finite coordinate has no strict dependency cycle"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("System(m) assigns each of its m states either one finite expression or no equation. An expression is a finite native ground, a fixed nonnegative power of one state, or an ordered pair of expressions. It uses the existing expression type with zero scalar tokens. Every original equation is imposed jointly by Satisfies. Undefined states are unrestricted, repeated names denote the same value, and disconnected or unused states remain present.")),
                    Paragraph(Text("Values are unrestricted finite or infinite full ordered Boolean-leaf trees. The operation rho replaces alpha by beta and beta by the ordered pair (beta,alpha), and distributes through branches. It is interpreted native substitution, including the atomic sibling collisions. No rank, regularity, depth or state bound is imposed beyond the supplied finite number of states.")),
                    Paragraph(Text("A dependency retains its original defining expression, the occurrence address and the fixed power. A walk follows such dependencies. Strict means that at least one occurrence is below a pair, or at least one fixed power is positive. The theorem says that every cycle based at a finite-valued coordinate has no strict edge. Zero-power root links and alias cycles remain permitted. Finiteness is required only at that cycle's base; auxiliary values elsewhere may be infinite.")),
                    Paragraph(Text("The proof assigns alpha weight one and beta weight two, and sums weights through native pairs. Every finite tree has positive weight. A containing pair has strictly greater weight than either child, and every native substitution strictly increases weight. Original occurrence semantics and preservation of finiteness transport these comparisons along each dependency and then along the walk. A strict cycle would strictly decrease a natural number back to itself.")),
                    Paragraph(Text("In the formula, NativeValues(m) abbreviates functions from Fin(m) to CompletionTree, valueAt(v,i) means v applied to i, and Strict is Walk.Strict. The theorem concerns cycles in original simultaneous systems. It supplies neither a whole-system extension theorem nor an exact description of the projections of their solution sets. Its content is an unbounded structural descent argument, rather than a finite enumeration, checker, numeric reduction or certified instance. No external novelty is asserted."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var m = V("m");
        var s = V("S");
        var v = V("v");
        var i = V("i");
        var w = V("w");
        return StatementSource.FromAuthor(Disp(
            All("m", V("Nat"), All("S", Call("System", m),
                All("v", Call("NativeValues", m),
                    Imp(Call("Satisfies", s, v),
                        All("i", Call("Fin", m), All("w", Call("Walk", s, i, i),
                            Imp(Call("IsFinite", Call("valueAt", v, i)),
                                Seq(Neg, Sp, Call("Strict", w)))))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. arguments]);
    private static Formula Imp(Formula left, Formula right) => Seq(Par(left), Sp, Implies, Sp, Par(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
