using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeSymbolicFiniteForcingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSymbolicFiniteForcing", H("Symbolic finite coordinates of native joint solutions"), Blocks(
            Describe.Lean(DescribeId.Create("symbolic-finite-original-forcing"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicFiniteForcing.symbolic_finite_forcing"),
                H("Finite original values are independent of free solutions"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let k, m and r be arbitrary natural numbers. A functional system S gives each of its m states either one native expression or no equation. An expression is a finite native ground, a shared parameter atom with a fixed offset, a state with a fixed nonnegative power of the native substitution, or an ordered pair. A fixed Boolean mode chooses whether each token denotes its finite atomic value or the leafless tree Omega. In particular, an explicit Omega can use a token in the divergent mode. The parameter tuple p assigns arbitrary natural numbers to all token names; divergent token values ignore their corresponding entries. Each of the r original coordinates has an arbitrary expression R(i) in these same states and tokens. Repeated occurrences retain the same values.")),
                    Paragraph(Text("The canonical joint assignment K(S,mode,p) is the original native leaf limit of simultaneous equation iteration from Omega. An extra undefined state represents the explicit leafless terminal. Native specialization evaluates only the finite parameter terminals; it retains every state occurrence, power and pair. Undefined states and free zero-power alias cycles start and remain at Omega. All equations are satisfied by one common assignment, including equations for unused auxiliaries. No finiteness condition is imposed on those auxiliaries.")),
                    Paragraph(Text("To obtain the finite expressions, start with no known state values. A symbolic evaluation succeeds at a finite ground or a finite-mode token; it succeeds at a powered state precisely when that state has a known expression, and at a pair precisely when both children succeed. Each simultaneous pass evaluates every defined right side against the preceding pass. Once obtained, an expression persists unchanged. If a pass changes, its finite support strictly grows. There are m states, so after m passes no further finite expression can appear. Evaluate each original reconstruction against that pass. The resulting option is finiteExpressions(S,mode,R,i); F(S,mode,R) is exactly the finite set of successful original indices. These objects contain no parameter values.")),
                    Paragraph(Text("For every p the canonical reconstruction is finite exactly at the indices in F. Whenever finiteExpressions returns f, the reconstruction equals embed(finiteValue(p,f)) in the canonical assignment and in every joint solution of S at that same p. Here f is the existing finite native expression syntax: grounds, shared parameter atoms, fixed powers and ordered pairs. finiteValue evaluates the parameter atoms as the actual finite native iterates of alpha. Equal parameter atoms and native atomic pair collapses do not change the finite support test.")),
                    Paragraph(Text("The semantic argument uses the native leaf order. Every finite tree is maximal in this order. Each finite leaf in an increasing native limit appears at some finite stage; a finite tree has only finitely many leaves, so a common stage contains all of them. Hence a finite canonical reconstruction is already finite at some simultaneous iteration. The symbolic pass describes exactly the finite values at each such iteration, and support stabilization brings that expression back to the m-th pass. Every iteration lies below every whole-system solution. Maximality therefore forces every solution's corresponding reconstruction to have the same finite value.")),
                    Paragraph(Text("The statement is uniform in the number of states, parameters and original reconstructions. It includes empty tuples, arbitrary recursive equations, and finite original coordinates beside infinite auxiliary coordinates. Restriction to any guard on the same parameter tuple follows immediately. A canonical infinite coordinate may be finite in another solution. The result gives neither an effective prefix bound for infinite coordinates nor an algorithm recognizing which raw input reductions are accepted."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k = V("k"); var m = V("m"); var r = V("r"); var s = V("S");
        var mode = V("b"); var rec = V("R"); var p = V("p"); var i = V("i");
        var f = V("f"); var v = V("v");
        var canonical = Call("canonicalSolution", s, mode, p);
        var original = Call("value", mode, p, canonical, Call("at", rec, i));
        var output = Call("embed", Call("finiteValue", p, f));
        return StatementSource.FromAuthor(Disp(
            All("k", V("Nat"), All("m", V("Nat"), All("r", V("Nat"),
            All("S", Call("FunctionalSystem", k, m), All("b", Call("Modes", k),
            All("R", Call("Reconstructions", k, m, r),
                AndAlso(
                    All("p", Call("Parameters", k), Call("satisfies", s, mode, p, canonical)),
                    All("p", Call("Parameters", k), All("i", Call("Fin", r),
                        AndAlso(
                            Iff(Call("IsFinite", original),
                                Seq(i, Sp, InMacro, Sp, Call("finiteOriginals", s, mode, rec))),
                            All("f", Call("FiniteExpression", k),
                                Imp(Seq(Call("finiteExpressions", s, mode, rec, i), Sp, Eq, Sp, Call("some", f)),
                                    AndAlso(Seq(original, Sp, Eq, Sp, output),
                                        All("v", Call("NativeValues", m),
                                            Imp(Call("satisfies", s, mode, p, v),
                                                Seq(Call("value", mode, p, v, Call("at", rec, i)),
                                                    Sp, Eq, Sp, output)))))))))))))))));
    }

    private static FormulaNode V(string name) => F.Id(name);
    private static FormulaNode Call(string name, params FormulaNode[] args) =>
        Seq(Operatorname(name), Apply(args));
    private static FormulaNode All(string name, FormulaNode type, FormulaNode body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static FormulaNode Imp(FormulaNode p, FormulaNode q) => Seq(p, Sp, Implies, Sp, q);
    private static FormulaNode Iff(FormulaNode p, FormulaNode q) => Seq(p, Sp, IffMacro, Sp, q);
    private static FormulaNode AndAlso(FormulaNode p, FormulaNode q) =>
        Seq(OpenParen, p, Sp, Wedge, Sp, q, CloseParen);
}
