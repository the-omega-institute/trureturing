using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SeparatedLimsupMeagreDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Upper(string x) =>
        Call("limsup", Call("sequenceAt", V("U"), V(x)), V("atTop"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("u", Call("Universe")), All("X", Call("Type", V("u"))),
            OpenBracket, Call("TopologicalSpace", V("X")), CloseBracket),
        Seq(All("U", Call("Function", V("Nat"), Call("Function", V("X"), V("Real"))))),
        Seq(All("A", Call("Set", V("X"))), All("B", Call("Set", V("X"))),
            All("a", V("Real")), All("b", V("Real"))),
        Seq(All("n", V("Nat")), Call("Continuous", Call("U", V("n")))),
        Seq(Call("Dense", V("A")), Sp, Land, Sp, Call("Dense", V("B")),
            Sp, Land, Sp, Call("Ne", V("a"), V("b"))),
        Seq(All("x", V("X")), V("x"), Sp, InMacro, Sp, V("A"), Sp, Rightarrow,
            Sp, Upper("x"), Sp, Eq, Sp, V("a")),
        Seq(All("x", V("X")), V("x"), Sp, InMacro, Sp, V("B"), Sp, Rightarrow,
            Sp, Upper("x"), Sp, Eq, Sp, V("b")),
        Seq(Rightarrow, Sp, Call("IsMeagre", Call("convergenceLocus", V("U"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two dense classes with distinct constant real limsups force the convergence locus of a continuous function sequence to be meagre.",
        H("Separated dense limsup classes"), Blocks(
            Paragraph(Text("Let u be any universe, X:Type(u) any topological space, and U:Nat -> X -> Real a sequence such that every U(n) is continuous. "
                + "A and B are dense subsets of this same X. The constants a and b are real and distinct. At every x in A the real Filter.limsup of n -> U(n,x) along atTop equals a; at every x in B it equals b. "
                + "There is no bound on U, and no compactness, metrizability, separation, inhabitedness, or Baire assumption on X.")),
            Describe.Lean(DescribeId.Create("separated-limsup-meagreness"),
                DeclarationHandle.Create("D5/S3/Topology/SeparatedLimsupMeagre.separated_limsup_isMeagre"),
                H("Meagreness of the full convergence locus"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/carvalhovarandas2021historic")),
                Blocks(
                    Paragraph(Text("Here sequenceAt(U,x) is the sequence n -> U(n,x), and convergenceLocus(U) is the set of x for which there exists a real L with Tendsto(sequenceAt(U,x),atTop,nhds(L)). "
                        + "The conclusion says that this entire convergence locus is meagre, including points outside both dense classes. Real limsup retains its conditionally complete default semantics; an equality to a real number alone is never used to infer boundedness.")),
                    Paragraph(Text("Set epsilon=abs(a-b)/4, which is positive. For each natural N let E(N) consist of x such that abs(U(n,x)-U(N,x))<=epsilon for every n>=N. "
                        + "Each E(N) is closed by continuity. At every actual point y of E(N), all n>=N satisfy U(N,y)-epsilon<=U(n,y)<=U(N,y)+epsilon. "
                        + "The upper bound gives eventual boundedness above; the lower bound gives the coboundedness needed for the real limsup upper estimate. Thus any dense-class limsup c satisfies abs(c-U(N,y))<=epsilon.")),
                    Paragraph(Text("If x belongs to the interior of E(N), density puts x in the closure of A intersected with that interior and also in the corresponding closure for B. "
                        + "The closed inequalities abs(a-U(N,x))<=epsilon and abs(b-U(N,x))<=epsilon follow by continuity. They imply abs(a-b)<=2epsilon, contrary to the choice of epsilon. "
                        + "Therefore E(N) has empty interior and is nowhere dense. Every convergent real sequence is Cauchy, so its point belongs to some E(N). Countable union and monotonicity give the conclusion."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a Baire space X the complement of convergenceLocus(U) belongs to residual(X), by the definition of IsMeagre. Applying Mathlib's dense_of_mem_residual makes this same divergence set dense. "
                + "The Baire assumption is needed for this density consequence, while the meagreness theorem itself holds on every topological space.")),
            Paragraph(Text("For Carvalho and Varandas, Genericity of historic behavior for maps and flows, arXiv:2107.01200v1, Section 2, Theorem A, take an arbitrary compact metric X, a continuous T:X -> X, and a continuous real phi. "
                + "Use the actual Birkhoff average U(n,x)=(1/n) sum over k in Finset.range(n) of phi(T^[k](x)). Every iterate T^[k] is continuous, each summand is continuous, and finite sum and multiplication by the constant 1/n preserve continuity. "
                + "At n=0 the empty sum and real division give U(0,x)=0. This initial value does not affect limits or limsup along atTop. The dense upper-average classes in Theorem A are exactly A and B above. "
                + "The compact metric topology is Baire, so the observable irregular set is both residual and dense. No invariant measure, ergodicity, or orbit-gluing property is used.")),
            Paragraph(Text("A concrete inhabited instance is the product space Nat -> Fin(2), with U(n,x) the real cast of the value of x(n). Coordinate evaluation is continuous. "
                + "For each c in Fin(2), sequences eventually equal to c form a dense set: every neighborhood restricts only finitely many coordinates, and the other coordinates can be set to c. "
                + "The resulting real sequences converge to c.val and hence have that real limsup. Taking c=0 and c=1 supplies distinct dense limsup classes.")),
            Paragraph(Text("The cited v1 theorem assumes compact metric dynamics and a continuous observable. The arbitrary-sequence topological meagreness statement is a derivation of the category mechanism, rather than a verbatim quotation or a claim of literature priority."))
        )));
}
