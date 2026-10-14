using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class PairwiseSignatureRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete controlled behavior, exact quotients, and an ordered pairwise algorithm with its primitive trace.",
        H("Controlled behavior and ordered pairwise refinement"),
        Blocks(
            Paragraph(Text("Let X be nonempty, A any alphabet, F : A to X to X a total update, and o : X to O an arbitrary observation. For a finite word w, runWord applies its first letter first. Put B(x)(w)=o(runWord(F,w,x)), and let R be equality of B. The operator Phi sends a relation S to the intersection of equality of current observations with all inverse images of S under paired one-step updates. No finiteness of X, A, or O is needed here.")),
            Paragraph(Text("Equality of B is a fixed point of Phi: the empty word gives current observation equality and prefixing a letter gives closure under that update. If S is contained in Phi(S), induction on word length shows that S is contained in equality of B. Thus R is the greatest fixed point and the greatest equivalence relation within the observation kernel preserved by every update. These are the existing controlledLimitRelation and controlledRefinementOperator results in ControlledFiniteStability.")),
            Paragraph(Text("The quotient Q=X/R carries the unique maps Fbar(a)([x])=[F(a,x)] and obar([x])=o(x) that commute with the projection pi. For any exact representation r : X to S, its maps G(a) and out are defined only on the actual image range(r), and obey r(F(a,x))=G(a)(r(x)) and o(x)=out(r(x)). Iteration shows that equal r-values have equal behaviors. Consequently p(r(x))=[x] is well defined, surjective, unique, and satisfies pi=p composed with r, p composed with G(a)=Fbar(a) composed with p, and obar composed with p=out. ControlledCompletionDescent supplies the descended maps and DynamicClosureMinimality supplies the behavior factor; completionRangeEquiv identifies the behavior image with Q.")),
            Paragraph(Text("The surjection p gives the cardinal inequality |Q| <= |range(r)| even for infinite carriers. If range(r) injects into b-bit strings, it is finite and Nat.card(Q) <= 2^b. The comparison concerns the actual representation states; it places no condition on unused elements of S.")),
            Paragraph(Text("Now X and A are finite, with n=|X|>0 and k=|A|, and c0 is the number of classes of the observation kernel. Let R(h) compare observations after every word of length at most h. Then R(0) is the observation kernel and R(h+1)=Phi(R(h)). Apply controlled_finite_stability to the surjective observation into range(o); equality of subtypes transports the relations back to O without assuming O finite. If A is empty every word is empty, so all R(h) equal R(0) and h=0 suffices. Otherwise finite class growth yields h<=n-c0 with R(h)=R(h+1)=R. Unequal behaviors therefore have a distinguishing word of length at most n-c0.")),
            Paragraph(Text("The execution input supplies states Fin n, actions Fin k, the transition table F and the observation table o, together with an equality decision on O. label(f,x) is the least input index with f(y)=f(x). scanTrace visits finRange n in order, starting best=x and replacing best by min(best,y) exactly when equality succeeds. Its invariant preserves the observed value, bounds best by its initial value and every matching visited index, and counts every emitted operation. Thus its returned index is label(f,x), including singleton and zero-action cases. Definitions also admit n=0; the termination theorem retains the original nonempty-state premise.")),
            Paragraph(Text("Initial scans compare observations. A refinement signature contains the observation and the previous class label of every successor. Each pair comparison visits all action coordinates, records transition lookups, label reads, equality tests and their flags, and then updates the running minimum. After all new labels are stored, a second pair scan compares the old and new equality matrices. No recursively expanded word history is compared in this operation model.")),
            Describe.Lean(DescribeId.Create("pairwise-signature-termination"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement.pairwise_signature_termination"),
                H("Exact quotient, distinguishing words, and a uniform cost bound"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n>0, k>=0, arbitrary O with an equality decision, and supplied F and o, there exist h, cost and a label table c with h<=n-c0. In the displayed statement, d is the supplied equality decision on O, and Terminates(n,k,O,d,F,o,h,cost,c) writes all arguments of the existing predicate explicitly. Natural-number subtraction is truncated at zero. Terminates asserts c=labelsAt(h), equality of the consecutive actual tables, cost equal to the complete emitted trace length, and correctness of every initial and refinement scan through h. Equality of final labels is exactly equality of complete behaviors, and unequal behaviors have a distinguishing word of length at most n-c0.")),
                    Paragraph(Text("The initial trace has 4*n*n+n operations. Each refinement and stability round has n*n*(7*k+8)+n operations. Including h strict rounds and the last stability comparison gives cost=4*n*n+n+(h+1)*(n*n*(7*k+8)+n), bounded by 14*(k+1)*n*n*(n-c0+1). The constant is independent of the carriers, input tables and equality decision. This is a count in the stated abstract input model; evaluating arbitrary observation equality and Lean VM reduction have no claimed runtime bound.")),
                    Paragraph(Text("The relation represented by labelsAt follows the existing controlled-word recursion. A stable relation gives exactly equal least-index label tables. The scan invariant supplies those tables and their trace lengths. Substitution of h<=n-c0 yields the uniform bound; it does not replace the scan by an edge count. utilityInput has three states: 0 and 1 initially share a label, while the sole action sends 1 to the differently observed state 2. The first refinement separates them and the following round is stable, with total cost 315."))),
                DescribeRole.Theorem),
            Paragraph(Text("For supplied equivalences eX : Fin n equiv X and eA : Fin k equiv A, set E(a,x)=eX.inverse(F(eA(a),eX(x))) and r(x)=rangeFactorization(o)(eX(x)). The equality decision need only act on range(o). Induction gives eX(runWord(E,w,x))=runWord(F,map(eA,w),eX(x)); mapping by the inverse alphabet equivalence gives the converse correspondence. Hence every bounded and complete behavior relation agrees through eX, initialClasses(r)=initialClasses(o), and the final label quotient is equivalent to the original behavior quotient. Word lengths, the exact trace count and the uniform bound are preserved. All output and representation maps remain on their actual ranges.")),
            Paragraph(Text("The finite argument reuses ControlledFiniteStability, ControlledRelationRecursion, ControlledBehaviorUniversality and ControlledCompletionDescent. Mathlib supplies quotient-kernel/range equivalence, cardinal transport and finite-set minima. The running-minimum invariant and its connection to the emitted pairwise trace provide the algorithmic part of this construction.")))));

    private static Formula Statement()
    {
        var n = V("n"); var k = V("k"); var h = V("h");
        var t = V("cost"); var c = V("c"); var f = V("F"); var o = V("o");
        var output = V("O"); var decision = V("d");
        var x = V("x"); var y = V("y"); var w = V("w");
        var states = Call("Fin", n); var actions = Call("Fin", k);
        var delta = Sub(n, Call("initialClasses", o));
        var behaviorX = Call("controlledBehavior", f, o, x);
        var behaviorY = Call("controlledBehavior", f, o, y);
        var kernel = All("x", states, All("y", states,
            Seq(Par(EqF(Apply(c, x), Apply(c, y))), Iff, Par(EqF(behaviorX, behaviorY)))));
        var word = All("x", states, All("y", states,
            Imp(Ne(behaviorX, behaviorY), Ex("w", Call("List", actions), And(
                LE(Call("length", w), delta),
                Ne(Apply(o, Call("runWord", f, w, x)), Apply(o, Call("runWord", f, w, y))))))));
        var trace = Add(Mul(D(4), Mul(n,n)), n,
            Mul(Add(h,D(1)), Add(Mul(Mul(n,n), Add(Mul(D(7),k),D(8))),n)));
        var bound = Mul(Mul(Mul(D(1,4), Add(k,D(1))),Mul(n,n)),Add(delta,D(1)));
        var conclusion = Ex("h", N, Ex("cost", N, Ex("c", Arrow(states, states), And(
            LE(h,delta), Call("Terminates",n,k,output,decision,f,o,h,t,c), kernel, word,
            EqF(t,trace), LE(t,bound)))));
        return All("n", N, All("k", N,
            Imp(Seq(D(0), Lt, n), All("O", V("Type"),
                All("d", Call("DecidableEq", output),
                    All("F", Arrow(actions, Arrow(states, states)),
                        All("o", Arrow(states, output), conclusion)))))));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), To, Sp, Par(b));
    private static Formula EqF(Formula a, Formula b) => Seq(Par(a), Eq, Par(b));
    private static Formula Ne(Formula a, Formula b) => Seq(Par(a), Neq, Sp, Par(b));
    private static Formula LE(Formula a, Formula b) => Seq(Par(a), Le, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Times, Sp, Par(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Minus, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Implies, Par(b));
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Par(body));
    private static Formula Ex(string s, Formula type, Formula body) =>
        Seq(Exists, Sp, V(s), Colon, type, Comma, Par(body));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula Add(params Formula[] args) => Join(Plus, args);
    private static Formula And(params Formula[] args) => Join(Land, [.. args.Select(x => Par(x))]);
    private static Formula Apply(Formula function, params Formula[] args) =>
        Seq(function, Open, Join(Comma, args), Close);
    private static Formula Call(string s, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(s))), args);
}
