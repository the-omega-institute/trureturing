using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeFunctionalObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFunctionalObstruction", H("Rank-free obstruction for native functional systems"), Blocks(
            Describe.Lean(DescribeId.Create("finite-native-dependency-cycles"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_cycle_is_silent"),
                H("A finite coordinate has no strict dependency cycle"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("System(m) assigns each of its m states either one finite expression or no equation. An expression is a finite native ground, a fixed nonnegative power of one state, or an ordered pair of expressions. It uses the existing expression type with zero scalar tokens. Every original equation is imposed jointly by Satisfies. Undefined states are unrestricted, repeated names denote the same value, and disconnected or unused states remain present.")),
                    Paragraph(Text("Values are unrestricted finite or infinite full ordered Boolean-leaf trees. The operation rho replaces alpha by beta and beta by the ordered pair (beta,alpha), and distributes through branches. It is interpreted native substitution, including the atomic sibling collisions. No rank, regularity, depth or state bound is imposed beyond the supplied finite number of states.")),
                    Paragraph(Text("A dependency retains its original defining expression, the occurrence address and the fixed power. A walk follows such dependencies. Strict means that at least one occurrence is below a pair, or at least one fixed power is positive. The theorem says that every cycle based at a finite-valued coordinate has no strict edge. Zero-power root links and alias cycles remain permitted. Finiteness is required only at that cycle's base; auxiliary values elsewhere may be infinite.")),
                    Paragraph(Text("The proof assigns alpha weight one and beta weight two, and sums weights through native pairs. Every finite tree has positive weight. A containing pair has strictly greater weight than either child, and every native substitution strictly increases weight. Original occurrence semantics and preservation of finiteness transport these comparisons along each dependency and then along the walk. A strict cycle would strictly decrease a natural number back to itself.")),
                    Paragraph(Text("In the formula, NativeValues(m) abbreviates functions from Fin(m) to CompletionTree, valueAt(v,i) means v applied to i, and Strict is Walk.Strict. The theorem concerns cycles in original simultaneous systems. It supplies neither a whole-system extension theorem nor an exact description of the projections of their solution sets. Its content is an unbounded structural descent argument, rather than a finite enumeration, checker, numeric reduction or certified instance. No external novelty is asserted."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-whole-system-boundary-extension"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.whole_system_boundary_extension"),
                H("A closed boundary extends to a whole-system solution"),
                ExtensionStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("BoundaryClosed(S,B) means that every variable occurrence in the defining expression of a state in B is also in B. This includes occurrences below ordered pairs and with any fixed nonnegative power. BoundaryValid(S,B,v) means that v satisfies each original equation whose state belongs to B. Undefined states contribute no equation. The assigned values may be arbitrary completed trees.")),
                    Paragraph(Text("Every such assignment extends to one joint solution w of all original equations, with w equal to v on B. The supplied values of v outside B are unrestricted, and unused and disconnected auxiliaries remain in the joint system. Taking B empty gives a completed solution of every functional system. Taking B to be the undefined states permits arbitrary values there. These are applications of the theorem, rather than additional hypotheses.")),
                    Paragraph(Text("The construction records a tree by all its labelled leaf occurrences. The leafless tree is below every tree in the inclusion order on these facts. An increasing sequence has a native completed limit: at each reached position the limit has the unique eventual leaf label if one appears, and branches otherwise. Native substitution preserves this limit because each output leaf descends from a single input leaf through the actual finite replacement of that label. In particular, substitution remains interpreted native evolution, with all atomic sibling collisions retained.")),
                    Paragraph(Text("Keep the supplied boundary values fixed, use the original right side at every other defined state, and use the leafless tree at the remaining undefined states. Iterating this operation from the constant leafless assignment yields increasing leaf facts. Their limits commute with every finite expression and therefore satisfy the fixed equations outside B. Closure of B transfers the already satisfied boundary equations to the same limiting assignment. This proves simultaneous satisfaction even when finite designated values coexist with infinite auxiliaries.")),
                    Paragraph(Text("In the formula, NativePredicates(m) means predicates on Fin(m), NativeValues(m) means functions from Fin(m) to CompletionTree, holds(B,i) means B applied to i, and valueAt(v,i) means v applied to i. The theorem establishes extension of a specified closed boundary. Finite reconstruction from free boundary values and the finite-union conversion obstruction require further mathematical arguments. No external novelty is asserted."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-finite-coordinate-perturbation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.finite_coordinate_perturbation"),
                H("A varying finite coordinate admits positive native mass"),
                PerturbationStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let u and v be two simultaneous solutions of the same original functional system S, and suppose only v(i) is finite. There is a simultaneous solution w and a finite native tree t with embed(t)=w(i). If u(i) and v(i) differ, t has strictly positive native mass gamma. The other values of u, v and w may be infinite, including unrestricted nonregular trees. No equation, auxiliary coordinate or repeated dependency is removed.")),
                    Paragraph(Text("A zero-power root-link path follows equations of the form X_j=X_k. Define the free region as the states for which every such path encounters only another zero-power root link or an undefined state. This region is closed under every original variable occurrence, and assigning one common tree to the entire region satisfies all of its original equations. Choose the finite ordered pair (alpha,alpha), which has positive native mass, and extend this boundary by the whole-system boundary extension theorem.")),
                    Paragraph(Text("For a state outside that region, some finite root-link path ends at an original defining expression which is not a zero-power root link. Every variable occurrence of this expression is below a pair or has a positive fixed power. If the original coordinate is finite, finite dependency descent therefore gives strictly smaller positive leaf weight at every such dependency. Strong induction on that weight proves that the extended coordinate is finite.")),
                    Paragraph(Text("The same induction compares u and v. A difference at an expression value requires a difference at some variable occurrence. The inductive positive mass at that occurrence survives each native power and cannot decrease through a containing ordered pair. Grounds cannot produce a difference. Equality along every original root-link path transfers the result back to the designated coordinate. This is an unbounded native construction and descent proof; no finite enumeration or external novelty is claimed.")),
                    Paragraph(Text("In the formula, NativeValues(m) abbreviates Fin(m) to CompletionTree, valueAt(v,i) means v(i), and gamma is native finite-tree mass. The existence of w is unconditional under the two original solution premises and the one coordinate finiteness premise. Positive mass is conditional only on those two designated values differing. This bridge does not itself conclude the finite-union obstruction."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-rank-free-conversion-obstruction"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction.rank_free_obstruction"),
                H("The whole homogeneous solution set has no finite functional representation"),
                ObstructionStatement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural a and finite homogeneous ordered pair expression H, suppose H has a pair at its root, its frontier consists of fixed nonnegative powers of one residual, and H(alpha)=T_a. The entire completed solution set of rho^a X=H(X) differs from the union represented by every finite list of original functional components. H has no ground and no second residual. The only anchor hypothesis is the stated alpha equality.")),
                    Paragraph(Text("A component consists of an arbitrary finite number of states, at most one original defining expression per state, and its actual designated state. Its projection existentially quantifies one joint assignment satisfying every original equation, and reads that same designated native value. NativeExpr allows finite native grounds, original variables, ordered pairs and fixed nonnegative powers around arbitrary subexpressions. A structural translation distributes powers and evaluates powered grounds. Its value-preservation proof uses the native pair law and iteration, and its whole-system equivalence retains the same assignments and designated coordinate. No normalization premise is supplied. The component syntax includes repeated states and undefined states. The finite list can be empty; components are independent. Zero-power alias cycles, positive-shift cycles, guarded cycles and unused or disconnected auxiliaries are all included. A finite designated output can coexist with infinite auxiliary values.")),
                    Paragraph(Text("The completed homogeneous split identifies the target as all distinct finite atomic iterates together with the leafless tree. If one component contained in that target produced two different atomic iterates, finite-coordinate perturbation would give a solution of the same whole component with finite positive native mass at the designated state. The leafless tree is not finite, while every atomic iterate has zero native mass. The new output contradicts containment in the target. Hence each such component contains at most one atomic iterate.")),
                    Paragraph(Text("Induction over the actual finite list makes the set of represented atomic ranks finite: each component contributes a subsingleton set of ranks, and adjoining a component takes a union. Equality with the entire target would represent every natural atomic rank, contradicting infinitude of the naturals. The argument uses the perturbation construction on its live inference path and preserves all original equations throughout.")),
                    Paragraph(Text("The displayed formula unfolds the proposition NativeObstruction. SolutionSet(a,H) means the set of all completed native values X satisfying rho^a X=eval(H,X); nativeRepresented(F) is the actual finite union of designated projections. FiniteComponents is List(NativeComponent). There is no normalization, extension, rigidity, canonical-solution or decoder premise, and no rank, depth, size, regularity or finite-value restriction on the completed domain. The result addresses exact representation of that coordinate set. It makes no claim about control, service, acquisition, erasure, stopping, productive contact or effective prefix computation. The proof is repository-derived, with no external novelty claim."))
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

    private static StatementSource ExtensionStatement()
    {
        var m = V("m"); var s = V("S"); var b = V("B");
        var v = V("v"); var w = V("w"); var i = V("i");
        return StatementSource.FromAuthor(Disp(
            All("m", V("Nat"), All("S", Call("System", m),
                All("B", Call("NativePredicates", m), All("v", Call("NativeValues", m),
                    Imp(Call("BoundaryClosed", s, b), Imp(Call("BoundaryValid", s, b, v),
                        ExistsTyped("w", Call("NativeValues", m),
                            AndAlso(Call("Satisfies", s, w),
                                All("i", Call("Fin", m), Imp(Call("holds", b, i),
                                    Seq(Call("valueAt", w, i), Sp, Eq, Sp, Call("valueAt", v, i))))))))))))));
    }

    private static StatementSource PerturbationStatement()
    {
        var m = V("m"); var s = V("S"); var u = V("u");
        var v = V("v"); var w = V("w"); var i = V("i"); var t = V("t");
        return StatementSource.FromAuthor(Disp(
            All("m", V("Nat"), All("S", Call("System", m),
                All("u", Call("NativeValues", m), All("v", Call("NativeValues", m),
                    Imp(Call("Satisfies", s, u), Imp(Call("Satisfies", s, v),
                        All("i", Call("Fin", m), Imp(Call("IsFinite", Call("valueAt", v, i)),
                            ExistsTyped("w", Call("NativeValues", m),
                                AndAlso(Call("Satisfies", s, w), ExistsTyped("t", V("Source"),
                                    AndAlso(Seq(Call("embed", t), Sp, Eq, Sp, Call("valueAt", w, i)),
                                        Imp(Seq(Call("valueAt", u, i), Sp, Neq, Sp, Call("valueAt", v, i)),
                                            Seq(D(0), Sp, Lt, Sp, Call("gamma", t)))))))))))))))));
    }

    private static StatementSource ObstructionStatement()
    {
        var a = V("a"); var h = V("H"); var family = V("F");
        return StatementSource.FromAuthor(Disp(
            All("a", V("Nat"), All("H", V("Homogeneous"),
                Imp(Call("PairRoot", h),
                    Imp(Seq(Call("eval", h, Call("leaf", V("true"))), Sp, Eq, Sp, Call("atomic", a)),
                        All("F", V("FiniteComponents"),
                            Seq(Call("SolutionSet", a, h), Sp, Neq, Sp, Call("nativeRepresented", family)))))))));
    }

    private static Formula ExistsTyped(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula AndAlso(Formula left, Formula right) => Seq(Par(left), Sp, Land, Sp, Par(right));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. arguments]);
    private static Formula Imp(Formula left, Formula right) => Seq(Par(left), Sp, Implies, Sp, Par(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
