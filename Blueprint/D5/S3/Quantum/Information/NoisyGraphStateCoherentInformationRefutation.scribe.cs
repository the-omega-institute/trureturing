using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class NoisyGraphStateCoherentInformationRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/sajjadkaurgoodenoughtowsleyguha2026noisygraph");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniformly dephased graph state on five plus four qubits has greater coherent information on its smaller subsystem.",
        H("Subsystem size does not order coherent information"),
        Blocks(
            Node("noisy-qubit", "noisyQubit", "An independently dephased qubit", NoisyQubitFormula(),
                "The vectors plus and minus are the one-qubit states with computational-basis amplitudes (1,1)/√2 and (1,−1)/√2. "
                    + "Their outer products are mixed with real weights P and 1−P, each explicitly included in the complex scalars. "
                    + "For P in [0,1] this is the dephasing model of Section 2.2, arXiv v2 main.tex, lines 186–194. "
                    + "The displayed matrix-valued function is defined for every real P.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cz-phase", "czPhase", "The phase from controlled-Z gates", CzPhaseFormula(),
                "For a Boolean assignment x on the disjoint union of the two vertex sets, multiply the diagonal controlled-Z entry over every edge. "
                    + "The equivalence finSumFinEquiv relabels the disjoint union as Fin (nA+nB); its inverse transports the assignment. "
                    + "Each edge contributes minus one precisely when both endpoint bits are true. "
                    + "This is the commuting controlled-Z construction of Section 2.1, arXiv v2 main.tex, lines 163–177.",
                AssessedProvenance.FromLiterature(Source)),
            Node("graph-state", "graphState", "The noisy graph-state matrix", GraphStateFormula(),
                "The computational basis is indexed by a pair of Boolean assignments, one on each subsystem. "
                    + "Multiply the independent one-qubit matrix entries and conjugate by the diagonal controlled-Z phases. "
                    + "Thus x supplies the row assignment and y the column assignment. "
                    + "For P in [0,1] this is the uniformly dephased graph state of Sections 2.1–2.2, arXiv v2 main.tex, lines 175–194. "
                    + "The matrix expression itself permits every real P and either subsystem to be empty.",
                AssessedProvenance.FromLiterature(Source)),
            Node("entropy", "entropy2", "Entropy in bits", EntropyFormula(),
                "For a finite square complex matrix rho, take the negative real part of the trace of rho times its continuous-functional-calculus logarithm, "
                    + "then divide by the natural logarithm of two. CStarMatrix.ofMatrix supplies the matrix C-star algebra. "
                    + "On density matrices this is the base-two von Neumann entropy in Section 2.3, arXiv v2 main.tex, lines 206–209. "
                    + "The displayed function has no positivity or trace-one hypothesis; its values elsewhere are the extension specified by this expression.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coherent-info-a", "coherentInfoA", "Coherent information on the first subsystem", CoherentInfoFormula("A"),
                "Trace out the second subsystem, take the entropy of the first marginal, and subtract the entropy of the joint state. "
                    + "This is the reverse coherent information of Section 2.3, arXiv v2 main.tex, lines 210–216, with the source's choice of subsystem names.",
                AssessedProvenance.FromLiterature(Source)),
            Node("coherent-info-b", "coherentInfoB", "Coherent information on the second subsystem", CoherentInfoFormula("B"),
                "Trace out the first subsystem, take the entropy of the second marginal, and subtract the entropy of the joint state. "
                    + "This is the coherent information of Section 2.3, arXiv v2 main.tex, lines 201–209.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The proposed subsystem-size ordering", ClaimFormula(),
                "For every pair of natural subsystem sizes with nB<nA, every simple graph on their disjoint union, and every common dephasing parameter P in [0,1], "
                    + "the proposed inequality places the second subsystem's coherent information below the first's. "
                    + "This is a non-strict mathematical reading of the conjecture in Section 5.4, arXiv v2 main.tex, lines 948–951. "
                    + "It allows edges inside either subsystem as well as between them.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("noisy-graph-coherent-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A nine-qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, a noisy-qubit matrix entry is one half when its two bits agree and (2P−1)/2 otherwise. "
                            + "A character product has the form ∏ⱼ(−1) raised to k(j)b(j), with natural exponents k(j) and Boolean bits b(j). "
                            + "Its sum over all assignments b is 2 to the number of bits when every k(j) is even, and zero otherwise. "
                            + "For a bipartite graph with Boolean biadjacency matrix N, its controlled-Z phase at assignments (a,b) is "
                            + "the product of (−1) raised to N(i,j)a(i)b(j). Put t=2P−1. "
                            + "On any finite set of bits, the product of noisy-qubit entries is 2 to the negative number of bits times t to the Hamming distance. "
                            + "Pairing two controlled-Z phases combines the assignments by exclusive-or. "
                            + "The character sums therefore give the first marginal entry as 2 to the power −nA times t to the Hamming distance between a and a′, "
                            + "provided N transpose sends their exclusive-or to zero over the two-element field, and is zero otherwise. "
                            + "The second marginal has the analogous expression with nB and the kernel of N.")),
                    Paragraph(Text(
                        "Take nA=5, nB=4 and no edges within either subsystem. The five biadjacency rows are "
                            + "(1,1,0,0), (1,1,0,0), (1,1,0,0), (1,0,1,0), and (1,0,0,1). "
                            + "Choose P=255/256, so t=127/128, and put s=t². "
                            + "The kernel of the transpose consists of 00000, 11000, 10100 and 01100; every nonzero element has weight two. "
                            + "The kernel of the biadjacency matrix consists of 0000 and 1111.")),
                    Paragraph(Text(
                        "Let Q_A have entry 1/4 when the exclusive-or of its two five-bit indices belongs to the transpose kernel, and zero otherwise. "
                            + "Let Q_B be half the sum of the identity and the permutation matrix that complements all four bits. "
                            + "For Q_A, two row supports are equal four-element cosets or are disjoint, so Q_A²=Q_A. "
                            + "The complement permutation is an involution, giving Q_B²=Q_B. Both matrices have real symmetric entries and hence are Hermitian. "
                            + "Each has trace eight: the diagonal entries are respectively 1/4 on 32 indices and 1/2 on 16 indices. "
                            + "The first reduced matrix equals αQ_A+β(I−Q_A), where α=(1+3s)/32 and β=(1−s)/32. "
                            + "The second equals γQ_B+δ(I−Q_B), where γ=(1+s²)/16 and δ=(1−s²)/16. "
                            + "The first equality follows from the weight-two property; the second follows because distinct allowed four-bit indices are complements and have Hamming distance four.")),
                    Paragraph(Text(
                        "For any Hermitian projection Q and real r and z, apply "
                            + "FullwoodParzygnatSubadditivityRefutation.projection_cfc to zI+(r−z)Q. "
                            + "Its logarithm is (log r)Q+(log z)(I−Q). Transporting the functional calculus to CStarMatrix and multiplying "
                            + "eliminates the cross terms, since Q(I−Q)=(I−Q)Q=0. "
                            + "Taking the trace gives the entropy numerator −trace(Q)r log r−(dimension−trace(Q))z log z. "
                            + "Thus the two marginal entropies are (−8α log α−24β log β)/log 2 and (−8γ log γ−8δ log δ)/log 2.")),
                    Paragraph(Text(
                        "Rewrite log α as log((1+3s)/4)−3 log 2, log β as log(1−s)−5 log 2, "
                            + "log γ as log((1+s²)/2)−3 log 2, and log δ as log(1−s)+log(1+s)−4 log 2. "
                            + "For positive x, the inequalities 1−1/x≤log x and log x≤x−1 give a lower bound on log((1+3s)/4) "
                            + "and an upper bound on log((1+s²)/2), respectively. "
                            + "Also 0<1−s≤1/64 and 0<1+s≤2 give log(1−s)≤−6 log 2 and log(1+s)≤log 2. "
                            + "At s=(127/128)² these bounds, together with log 2<9/10, yield "
                            + "−8α log α−24β log β<−8γ log γ−8δ log δ. "
                            + "Since log 2 is positive, the first marginal entropy is strictly smaller than the second.")),
                    Paragraph(Text(
                        "Finally apply the proposed ordering at sizes five and four, this graph, and P=255/256, which lies in [0,1]. "
                            + "Subtracting the same joint entropy from both marginal entropies preserves their strict order. "
                            + "The proposed inequality would therefore require the larger second marginal entropy to be at most the smaller first marginal entropy, a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sajjad-kaur-goodenough-towsley-guha-2026-coherent-information-ordering-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("noisy-graph-coherent-" + id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NoisyQubitFormula()
    {
        Formula plus = X("plus"), minus = X("minus"), b = X("b"), p = X("P");
        Formula plusValue = LambdaOf("b", Booleans,
            At(Qualified("D5", "S3", "Quantum", "Entanglement", "RandomizedGraphNegativityRefutation", "plusState"),
                Typed(D(1), Naturals), At(Qualified("Function", "const"), FinOf(D(1)), b)));
        Formula minusValue = LambdaOf("b", Booleans,
            Multiply(At(Qualified("ite"), Equal(b, Qualified("Bool", "true")),
                new Formula.Negate(Typed(D(1), Complexes)), Typed(D(1), Complexes)), At(plus, b)));
        Formula value = Add(
            Smul(CastComplex(p), At(Qualified("Matrix", "vecMulVec"), plus, At(Qualified("star"), plus))),
            Smul(CastComplex(Subtract(Typed(D(1), Reals), p)),
                At(Qualified("Matrix", "vecMulVec"), minus, At(Qualified("star"), minus))));
        return All("P", Reals, Equal(Typed(LocalCall("noisyQubit", p), Matrix(Booleans, Booleans)),
            Let("plus", Arrow(Booleans, Complexes), plusValue,
                Let("minus", Arrow(Booleans, Complexes), minusValue, value))));
    }

    private static Formula CzPhaseFormula()
    {
        Formula equivalence = Qualified("finSumFinEquiv");
        Formula edge = At(Qualified("Sym2", "map"),
            At(Qualified("Equiv", "toFun"), equivalence), X("e"));
        Formula assignment = At(Qualified("Function", "comp"), X("x"),
            At(Qualified("Equiv", "toFun"), At(Qualified("Equiv", "symm"), equivalence)));
        Formula entry = At(Qualified("D5", "S3", "Quantum", "Entanglement", "RandomizedGraphNegativityRefutation", "czPhase"),
            edge, assignment);
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(X("e"), Sp, InMacro, Sp, At(Qualified("SimpleGraph", "edgeFinset"), X("G")))),
            Sp, Parenthesized(entry));
        return GraphBinders(All("x", Arrow(Vertices, Booleans),
            Equal(Typed(LocalCall("czPhase", X("G"), X("x")), Complexes), product)));
    }

    private static Formula GraphStateFormula()
    {
        Formula row = At(Qualified("Sum", "elim"), At(Qualified("Prod", "fst"), X("x")),
            At(Qualified("Prod", "snd"), X("x")));
        Formula column = At(Qualified("Sum", "elim"), At(Qualified("Prod", "fst"), X("y")),
            At(Qualified("Prod", "snd"), X("y")));
        Formula entry = Multiply(Multiply(LocalCall("czPhase", X("G"), row),
            ProductOver("v", Vertices, LocalCall("noisyQubit", X("P"), At(row, X("v")), At(column, X("v"))))),
            At(Qualified("star"), LocalCall("czPhase", X("G"), column)));
        return GraphBinders(All("P", Reals,
            Equal(Typed(LocalCall("graphState", X("G"), X("P")), Matrix(Basis, Basis)),
                LambdaOf("x", Basis, LambdaOf("y", Basis, entry)))));
    }

    private static Formula EntropyFormula()
    {
        Formula matrix = At(Qualified("CStarMatrix", "ofMatrix"), X("rho"));
        Formula trace = At(Qualified("Matrix", "trace"),
            Multiply(matrix, At(Qualified("CFC", "log"), matrix)));
        Formula value = new Formula.Fraction(new Formula.Negate(At(Qualified("Complex", "re"), trace)),
            At(Qualified("Real", "log"), Typed(D(2), Reals)));
        return All("ι", Seq(Qualified("Type"), Star), Instance("Fintype", X("ι"),
            Instance("DecidableEq", X("ι"), All("rho", Matrix(X("ι"), X("ι")),
                Equal(Typed(LocalCall("entropy2", X("rho")), Reals), value)))));
    }

    private static Formula CoherentInfoFormula(string side)
    {
        Formula state = LocalCall("graphState", X("G"), X("P"));
        Formula marginal = At(Qualified("D5", "S3", "Quantum", "Information", "PartialTraceMutualInformation",
            side == "A" ? "partialTraceRight" : "partialTraceLeft"), state);
        return GraphBinders(All("P", Reals,
            Equal(Typed(LocalCall("coherentInfo" + side, X("G"), X("P")), Reals),
                Subtract(LocalCall("entropy2", marginal), LocalCall("entropy2", state)))));
    }

    private static Formula ClaimFormula()
    {
        Formula interval = At(Qualified("Set", "Icc"), Typed(D(0), Reals), Typed(D(1), Reals));
        Formula bound = new Formula.Relation(LocalCall("coherentInfoB", X("G"), X("P")),
            FormulaRelationOperator.LessThanOrEqual, LocalCall("coherentInfoA", X("G"), X("P")));
        Formula graphs = All("G", At(Qualified("SimpleGraph"), Vertices), GraphInstance(
            All("P", Reals, Imp(new Formula.Relation(X("P"), FormulaRelationOperator.MemberOf, interval), bound))));
        Formula claim = All("nA", Naturals, All("nB", Naturals,
            Imp(new Formula.Relation(X("nB"), FormulaRelationOperator.LessThan, X("nA")), graphs)));
        return Equal(Typed(Local("claim"), Qualified("Prop")), Parenthesized(claim));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Booleans => Qualified("Bool");
    private static Formula Vertices => At(Qualified("Sum"), FinOf(X("nA")), FinOf(X("nB")));
    private static Formula Basis => At(Qualified("Prod"), Arrow(FinOf(X("nA")), Booleans), Arrow(FinOf(X("nB")), Booleans));
    private static Formula X(string name) => name == "ι" ? Iota : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Information",
        "NoisyGraphStateCoherentInformationRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Matrix(Formula rows, Formula columns) => At(Qualified("Matrix"), rows, columns, Complexes);
    private static Formula CastComplex(Formula value) => Typed(At(Qualified("Complex", "ofReal"), value), Complexes);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) => At(Qualified("smul"), scalar, matrix);
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(Parenthesized(from), Parenthesized(to));
    private static Formula Imp(Formula from, Formula to) => new Formula.Logic(Parenthesized(from), FormulaLogicOperator.Implies, Parenthesized(to));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Seq(
        Mathrm, Grp(F.Id("let")), Sp, Typed(X(name), type), Colon, Eq, Sp, Parenthesized(value), Semi, Sp, Parenthesized(body));
    private static Formula ProductOver(string name, Formula type, Formula value) => Seq(
        new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(value));
    private static Formula Instance(string name, Formula type, Formula body) => Seq(
        OpenBracket, At(Qualified(name), type), CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula GraphInstance(Formula body) => Instance("DecidableRel", At(Qualified("SimpleGraph", "Adj"), X("G")), body);
    private static Formula GraphBinders(Formula body) => All("nA", Naturals, All("nB", Naturals,
        All("G", At(Qualified("SimpleGraph"), Vertices), GraphInstance(body))));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
