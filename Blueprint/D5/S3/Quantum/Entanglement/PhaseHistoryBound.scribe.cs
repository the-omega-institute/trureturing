using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PhaseHistoryBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sequential source moments and a common-center phase-history operator bound.",
        H("Phase History Bound"),
        Blocks(
            Paragraph(Text("The source has a two-dimensional complex memory and a fresh blank physical bit at each step. "
                + "Every emitted bit and the final memory are retained. Bit is Bool, with false denoted 0 and true denoted 1; "
                + "bit converts these labels to the real numbers 0 and 1. Throughout, p is real with 0<p<1, "
                + "n and all time indices are natural numbers, and phi and delta are arbitrary real sequences. "
                + "Space(A) is the complex Euclidean space on the finite type A, e is its coordinate basis, "
                + "Unitary(A) is its linear isometry equivalence group, and indicator(P) is 1 or 0 according to P.")),
            Def("memory", "memory", "Memory amplitudes", And(
                Eq(C("memory", p, D(0), D(0)), C("sqrt", Sub(D(1), p))),
                Eq(C("memory", p, D(0), D(1)), C("sqrt", p)),
                Eq(C("memory", p, D(1), D(0)), D(1)),
                Eq(C("memory", p, D(1), D(1)), D(0))),
                "Rows are indexed by the incoming memory and columns by the outgoing memory. "
                + "The emitted physical bit copies the incoming memory. These amplitudes are nonnegative."),
            Def("transition", "transition", "Squared memory amplitudes", And(
                Eq(C("transition", p, D(0), D(0)), Sub(D(1), p)),
                Eq(C("transition", p, D(0), D(1)), p),
                Eq(C("transition", p, D(1), D(0)), D(1)),
                Eq(C("transition", p, D(1), D(1)), D(0))),
                "The transition matrix is the entrywise square of memory, with rows (1-p,p) and (1,0). "
                + "Each row sums to one. The probability law below is derived from the physical amplitudes."),
            Def("local-step", "step", "The blank-input isometry", Eq(
                C("step", p, Id("gamma"), Pair(j, k), i),
                Mul(C("indicator", Eq(j, i)), Mul(ExpI(Mul(Id("gamma"), C("bit", i))), C("memory", p, i, k)))),
                "gamma is real and i,j,k range over Bit. step is a matrix from Bit to Bit x Bit. "
                + "Its orthonormal columns specify the action of a two-bit unitary on the blank physical input."),
            Def("paths", "Path", "A path retains its terminal memory", And(
                Eq(C("Path", D(0)), B), Eq(C("Path", Add(n, D(1))), ProdType(B, C("Path", n)))),
                "Path(n) represents (x(0),...,x(n)). Its first n entries are physical archive bits and x(n) is final memory. "
                + "pathFintype recursively supplies the finite enumeration, and pathDecidableEq recursively decides equality; "
                + "both use the Bool instances at length zero and product instances at successors."),
            Def("head", "head", "The initial memory label", And(
                Eq(C("head", D(0), i), i), Eq(C("head", Add(n, D(1)), Pair(i, x)), i)),
                "head(n,x) is x(0). At length zero the entire path is the memory label."),
            Def("observation", "observed", "Real-valued occupation observations", And(
                Eq(C("observed", D(0), i, s), C("bit", i)),
                Eq(C("observed", Add(n, D(1)), Pair(i, x), D(0)), C("bit", i)),
                Eq(C("observed", Add(n, D(1)), Pair(i, x), Add(s, D(1))), C("observed", n, x, s))),
                "For 0<=s<=n, observed(n,x,s) is the occupation bit x(s). The definition saturates at final memory beyond n; "
                + "the moment theorem uses only times through n. Write X(s) for the function x mapped to observed(n,x,s)."),
            Def("path-mass", "pathMass", "The source path mass", And(
                Eq(C("pathMass", p, D(0), i), D(1)),
                Eq(C("pathMass", p, Add(n, D(1)), Pair(i, x)),
                    Mul(C("transition", p, i, C("head", n, x)), C("pathMass", p, n, x)))),
                "pathMass is the product of the n squared memory amplitudes. Fixing head(n,x)=i supplies the initial condition; "
                + "there is no stationary initial distribution."),
            Def("path-amplitude", "pathAmplitude", "The physical amplitude along a path", And(
                Eq(C("pathAmplitude", p, phi, D(0), t, i), D(1)),
                Eq(C("pathAmplitude", p, phi, Add(n, D(1)), t, Pair(i, x)),
                    Mul(Mul(ExpI(Mul(C("phi", t), C("bit", i))), C("memory", p, i, C("head", n, x))),
                        C("pathAmplitude", p, phi, n, Add(t, D(1)), x)))),
                "The start time t shifts the phase history. Each factor is the local phase on incoming memory times its transition amplitude."),
            Def("source", "source", "The full archive-and-memory source matrix", Eq(
                C("source", p, phi, n, t, x, i),
                Mul(C("indicator", Eq(C("head", n, x), i)), C("pathAmplitude", p, phi, n, t, x))),
                "source(p,phi,n,t) has rows Path(n) and columns Bit. It includes the final memory and preserves both input columns. "
                + "At n=0 it is exactly the identity matrix on Bit, independently of p, phi and t."),
            Def("register", "register", "The path and physical register have the same coordinates", Eq(
                C("register", n, x), Pair(C("archive", n, x), C("terminal", n, x))),
                "register(n) is an equivalence from Path(n) to ((Fin(n) to Bit) x Bit): archive lists x(0) through x(n-1), "
                + "and terminal is x(n). It recursively uses SequentialRegisterCircuit.headRest, with the unique empty archive at zero."),
            Def("expectation", "expectation", "Expectation in a fixed input column", Eq(
                C("expectation", p, n, i, Id("f")), SumAt("x", C("Path", n),
                    Mul(Mul(C("indicator", Eq(C("head", n, x), i)), C("pathMass", p, n, x)), C("f", x)))),
                "f is any real function on Path(n). Write E(n,i,f) for this expectation with p understood. "
                + "Its weights are the Born probabilities of the actual circuit, and their normalization is a conclusion below."),
            Def("mean", "mean", "The nonstationary occupation mean", Eq(C("mean", p, i, s),
                Add(q, Mul(Sub(C("bit", i), q), Pow(Negate(p), s)))),
                "q=p/(1+p) is the equilibrium occupation. The transient (bit(i)-q)(-p)^s retains the deterministic initial bit. "
                + "Write m(i,s)=mean(p,i,s)."),
            Theorem("actual-source-moments", "actual_source_moments", "One actual unitary sequence realizes the path law at every length",
                All("p", R, Imp(And(Lt(D(0), p), Lt(p, D(1))), All("phi", Fn(N, R),
                    Ex("U", Fn(N, C("Unitary", ProdType(B, B))), And(
                        All("t", N, Alls("i j k", B, Eq(
                            C("U", t, C("e", Pair(D(0), i)), Pair(j, k)), C("step", p, C("phi", t), Pair(j, k), i)))),
                        Alls("n t", N, All("i", B, All("x", C("Path", n), Eq(
                            C("circuit", Id("U"), n, t, C("blankState", D(0), n, i), C("register", n, x)),
                            C("source", p, phi, n, t, x, i))))),
                        Alls("n t", N, All("i", B, All("x", C("Path", n), Eq(
                            Pow(C("norm", C("source", p, phi, n, t, x, i)), D(2)),
                            Mul(C("indicator", Eq(C("head", n, x), i)), C("pathMass", p, n, x)))))),
                        All("n", N, All("i", B, Eq(E(C("constant", D(1))), D(1)))),
                        All("n", N, All("i", B, All("s", N, Imp(Le(s, n), Eq(E(C("X", s)), M(i, s)))))),
                        All("n", N, All("i", B, Alls("s t", N, Imp(And(Le(s, t), Le(t, n)),
                            Eq(Sub(E(C("product", C("X", s), C("X", t))), Mul(M(i, s), M(i, t))),
                                Mul(Mul(Pow(Negate(p), Sub(t, s)), M(i, s)), Sub(D(1), M(i, s))))))))))))),
                "The same U is chosen before n and t, so it realizes every length and every start time. circuit, blankState, "
                + "and the unitary Hilbert spaces are those of SequentialRegisterCircuit. The first equation specifies U on its blank-input subspace; "
                + "the second identifies its actual composed coefficients with source. The remaining equations give squared amplitudes, "
                + "normalization, mean, and the exact two-time covariance. product denotes pointwise multiplication of real functions. "
                + "The proof first extends each local isometry to a unitary, then identifies the recursive circuit coefficients and "
                + "derives the moments by conditioning on the first transition. In particular, at p=1/2, n=2, i=0, s=1, t=2, the covariance is -1/8."),
            Paragraph(Text("Linearity extends the coefficient identity to every complex memory vector v: the actual initialized circuit coefficient "
                + "at register(n,x) is the sum over i of v(i)source(p,phi,n,t,x,i). Thus these are coherent source maps, including superpositions "
                + "of the two memory inputs. An arbitrary finite reference is retained in the operator inequality below.")),
            Def("history-constant", "historyConstant", "The uniform history constant", Eq(C("historyConstant", p),
                Div(Add(Div(Add(D(1), p), Sub(D(1), p)), Div(D(1), Sub(D(1), Pow(p, D(2))))), D(4))),
                "Both denominators are positive for 0<p<1. The first term bounds correlated fluctuations; the second controls "
                + "the transient displacement from a center shared by the two initial conditions."),
            Def("phase-sum", "phaseSum", "The accumulated discrepancy", Eq(C("phaseSum", Id("delta"), n, t, x),
                SumAt("s", C("Fin", n), Mul(C("delta", Add(t, C("val", s))), C("observed", n, x, C("val", s))))),
                "This sum includes the n emitted occupations, with start time t. The final memory is retained in the path but adds no extra phase."),
            Def("common-center", "center", "One scalar center for both input columns", Eq(C("center", p, Id("delta"), n),
                Add(Mul(q, SumAt("s", C("Fin", n), C("delta", C("val", s)))),
                    Mul(Sub(Div(D(1), D(2)), q), Hsum))),
                "H is the sum of delta(s)(-p)^s for 0<=s<n. This center is the arithmetic midpoint of the two conditional means "
                + "of phaseSum(delta,n,0). Their deviations from the center are (bit(i)-1/2)H. The scalar center is independent of the input vector and reference."),
            Def("error", "error", "The coherently centered source difference", Eq(C("error", p, Id("theta"), phi, n, Id("b")),
                Sub(C("source", p, C("constant", Id("theta")), n, D(0)),
                    Mul(ExpI(Id("b")), C("source", p, phi, n, D(0))))),
                "theta is the real phase of the constant source and phi is the known virtual phase history. b is one real scalar, "
                + "multiplying the entire second source matrix by the same complex phase. Write D=error(p,theta,phi,n,center(p,delta,n))."),
            Theorem("phase-history-bound", "phase_history_bound", "Uniform operator and finite-reference bounds",
                All("p", R, Imp(And(Lt(D(0), p), Lt(p, D(1))), All("n", N, All("theta", R,
                    Alls("phi delta", Fn(N, R), Imp(
                        All("t", N, Imp(Lt(t, n), Ex("k", Z, Eq(Sub(Id("theta"), C("phi", t)),
                            Add(C("delta", t), Mul(k, Mul(D(2), Pi))))))),
                        And(PSD(Sub(Mul(Bound, C("identity", B)), Mul(C("adjoint", Id("D")), Id("D")))),
                            All("J", Id("Type"), Imp(And(C("Fintype", Id("J")), C("DecidableEq", Id("J"))),
                                PSD(Sub(Mul(Bound, C("identity", ProdType(Id("J"), B))),
                                    Mul(C("adjoint", TensorError), TensorError)))))))))))),
                "Bound is historyConstant(p) times the sum of delta(s)^2 for 0<=s<n. identity(J) is the identity matrix, "
                + "adjoint is conjugate transpose, and tensor is the matrix Kronecker product; TensorError=identity(J) tensor D. "
                + "PSD means positive semidefinite. J may be any finite type in any universe, including the empty type. "
                + "Equivalently, every vector v on Bit and every vector w on J x Bit satisfy squared output norm at most Bound "
                + "times their squared input norm. This includes arbitrary coherent and reference-entangled inputs without a normalization premise. "
                + "The congruence condition allows any real representatives delta, without a minimal-distance restriction or a finite upper cutoff on n. "
                + "For n=0 both sources are the identity, the center and error are zero, and the bound is zero."),
            Paragraph(Text("For the bound, the exact covariance gives absolute covariance at most p raised to the time separation, divided by 4. "
                + "Its geometric row sum is bounded by (1+p)/(1-p), controlling the variance of the weighted phase sum. "
                + "Cauchy-Schwarz bounds H squared by the phase energy divided by (1-p^2). Adding the squared common-center bias H squared/4 "
                + "gives exactly historyConstant(p). The inequality between a phase chord and its real lift then bounds each column's squared error. "
                + "The two columns have disjoint head support, so the error Gram matrix is diagonal. This yields the operator inequality, "
                + "and tensoring its positive semidefinite remainder with the reference identity proves the reference statement.")),
            Describe.Example(DescribeId.Create("golden-specialization"), H("The original golden memory is the p=alpha squared source"),
                Disp(And(Eq(Id("alpha"), Div(Sub(C("sqrt", D(5)), D(1)), D(2))), Eq(p, Pow(Id("alpha"), D(2))),
                    Eq(Add(Pow(Id("alpha"), D(2)), Id("alpha")), D(1)),
                    Eq(C("memory", p, D(0), D(0)), C("sqrt", Id("alpha"))),
                    Eq(C("memory", p, D(0), D(1)), Id("alpha")),
                    Eq(C("historyConstant", p), Div(Add(Div(Add(D(1), Pow(Id("alpha"), D(2))), Sub(D(1), Pow(Id("alpha"), D(2)))),
                        Div(D(1), Sub(D(1), Pow(Id("alpha"), D(4))))), D(4))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "alpha=(sqrt(5)-1)/2 lies strictly between zero and one and satisfies alpha squared plus alpha equals one. "
                    + "Consequently sqrt(1-alpha squared)=sqrt(alpha) and sqrt(alpha squared)=alpha, so the memory rows are exactly "
                    + "(sqrt(alpha),alpha) and (1,0). Substituting p=alpha squared into the local step therefore realizes the original "
                    + "memory amplitudes by the same actual unitary circuit for all lengths and start times. The center and history constant "
                    + "are specialized at alpha squared, not at alpha. The bound then applies to every constant theta, virtual history, "
                    + "congruent real lift and finite reference.")))))));

    private static DocumentBlock Def(string id, string selector, string title, Formula formula, string text) =>
        Entry(id, selector, title, formula, text, DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string selector, string title, Formula formula, string text) =>
        Entry(id, selector, title, formula, text, DescribeRole.Theorem);
    private static DocumentBlock Entry(string id, string selector, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PhaseHistoryBound." + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula Id(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula p => Id("p");
    private static Formula phi => Id("phi");
    private static Formula n => Id("n");
    private static Formula t => Id("t");
    private static Formula s => Id("s");
    private static Formula i => Id("i");
    private static Formula j => Id("j");
    private static Formula k => Id("k");
    private static Formula x => Id("x");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula Z => Seq(Mathbb, Grp(Id("Z")));
    private static Formula B => Id("Bit");
    private static Formula q => Div(p, Add(D(1), p));
    private static Formula Hsum => SumAt("s", C("Fin", n), Mul(C("delta", C("val", s)), Pow(Negate(p), C("val", s))));
    private static Formula Bound => Mul(C("historyConstant", p), SumAt("s", C("Fin", n), Pow(C("delta", C("val", s)), D(2))));
    private static Formula TensorError => C("tensor", C("identity", Id("J")), Id("D"));
    private static Formula PSD(Formula a) => C("PSD", a);
    private static Formula E(Formula f) => C("E", n, i, f);
    private static Formula M(Formula a, Formula b) => C("mean", p, a, b);
    private static Formula Fn(Formula a, Formula b) => C("Function", a, b);
    private static Formula ProdType(Formula a, Formula b) => C("Prod", a, b);
    private static Formula Pair(Formula a, Formula b) => C("pair", a, b);
    private static Formula ExpI(Formula a) => C("exp", Mul(Id("imaginaryUnit"), a));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((a, b) => new Formula.Logic(b, FormulaLogicOperator.And, a));
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Alls(string names, Formula domain, Formula body) => names.Split(' ').Reverse().Aggregate(body, (b, name) => All(name, domain, b));
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
}
