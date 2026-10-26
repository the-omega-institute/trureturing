using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.RandomCircuits;

internal sealed class HammingWeightPatternSpectralGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/monbroussouetal2025hammingweight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected patterns of polynomially many Hamming-weight-preserving gates have an inverse-polynomial spectral gap at fixed weight.",
        H("The spectral gap of a connected Hamming-weight gate pattern"),
        Blocks(
            Definition("swap-config", "swapConfig", "Exchanging two qubit labels", SwapFormula(),
                AssessedProvenance.FromRepo(Source),
                "Choice n k is the type of k-element subsets of Fin n. Applying the transposition of a and b to every element of such a subset gives another subset of the same cardinality. "
                    + "A subset containing both labels or neither label is fixed. This construction expresses the exchange of the two qubit positions in the RBS/FBS gate descriptions, Quantum.tex lines 158–192."),
            Definition("gate-matrix", "gateMatrix", "A single stochastic gate", GateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The real matrix has one half of the identity plus one half of the permutation matrix of the exchange. "
                    + "If the exchange fixes a configuration, its diagonal entry is one. Otherwise the two exchanged configurations each receive weight one half. "
                    + "These are the squared RBS/FBS entries at angle pi/4; the fermionic signs disappear on squaring. See Quantum.tex lines 158–192 and 1450–1458."),
            Definition("pattern-matrix", "patternMatrix", "The ordered product of the gates", PatternFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Map each ordered pair in pat to its gate matrix, reverse the list, and multiply. Thus the first gate in pat acts first on a column vector, "
                    + "and an empty pattern gives the identity matrix. The product order is T = T_J ... T_1 in Quantum.tex lines 1487–1489."),
            Definition("qubit-graph", "qubitGraph", "The graph of gate positions", GraphFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The vertices are the qubit labels. Distinct vertices x and y are adjacent when either ordered pair (x,y) or (y,x) occurs in pat. "
                    + "Repeated gates contribute the same edge, and diagonal pairs give no edge. This is the undirected form of the graph with arrows in both directions described in Quantum.tex lines 1631–1639."),
            Definition("connected-pattern", "connectedPattern", "Connected patterns", ConnectedFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Every gate has distinct endpoints, and the qubit graph is connected. Since each gate supplies both arrow directions, "
                    + "undirected connectivity is equivalent to the strong connectivity in the source's connected-pattern definition, Quantum.tex lines 1631–1640."),
            Definition("claim", "claim", "A uniform polynomial gap at fixed weight",
                Equivalence(Local("claim"), ClaimFormula()), AssessedProvenance.FromRepo(Source),
                "Fix natural numbers k, c and a with k at least one. The family pat assigns an ordered gate list to every natural n. "
                    + "For every n at least two, assume that this list is connected and has length at most c times n to the power a. "
                    + "There must then be a positive real d and a natural b, uniform in n, such that every nonzero complex eigenvector with coordinate sum zero, "
                    + "at every n greater than k and at least two, has eigenvalue modulus at most 1 minus d divided by n to the power b. "
                    + "The real entries are included in the complex numbers before matrix-vector multiplication, and n is cast to a real number in the denominator. "
                    + "This is the sum-zero eigenvector formulation of the spectral-gap question in Quantum.tex lines 1977–1986; the source defines the gap as one minus the second-largest eigenvalue modulus in lines 1397–1405."),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("An inverse-polynomial bound for every connected pattern family"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First fix n and k and write X = Choice n k. Its cardinality is the binomial coefficient n choose k, which is at most n to the power k. "
                            + "For a gate exchanging a and b, let S act on complex functions on X by permuting their coordinates, and put P = (I + S)/2. "
                            + "The complexified gate matrix acts as P, and the complexified pattern matrix acts as the successive application of these operators in list order.")),
                    Paragraph(Text(
                        "The coordinate permutation is an isometry, and w − Pw = (w − Sw)/2. The parallelogram identity gives ||Pw||² + ||w − Pw||² = ||w||². "
                            + "The residual formula and the triangle inequality show that ||w − Pw|| is at most ||w||. Linearity and this last bound imply "
                            + "||w − Pw|| ≤ ||w − z|| + ||z − Pz|| for any w and z.")),
                    Paragraph(Text(
                        "For the successive vectors w₀ = w and w_j = P_j w_{j−1}, put t_j = ||w_{j−1} − w_j||. "
                            + "There is one nonnegative t_j for each gate. Summing the preceding identity gives Σ_j t_j² = ||w||² − ||Tw||². "
                            + "Induction along the list, using the preceding inequality, bounds the defect ||w − P_j w|| of every gate at the initial vector by Σ_i t_i. "
                            + "Consequently E(w) = Σ_j ||w − P_j w||² is at most J(Σ_i t_i)², where J = (↑pat.length : ℝ) is the gate count cast to a real number. "
                            + "Cauchy–Schwarz gives (Σ_i t_i)² ≤ J Σ_i t_i², and hence E(w) ≤ J²(||w||² − ||Tw||²).")),
                    Paragraph(Text(
                        "For each gate, expansion in coordinates gives ||w − Pw||² = (1/4)Σ_s |w(s) − w(swapConfig a b s)|². "
                            + "Now join distinct configurations whenever one gate exchange sends one to the other. To show that every pair is joined by a path, consider the qubit permutations "
                            + "whose action sends every configuration to a reachable configuration. They form a subgroup: reachability is reflexive, composes under permutation multiplication, "
                            + "and reverses to give inverses. This subgroup contains every gate transposition, including either orientation of every qubit edge. "
                            + "The edge transpositions of a connected qubit graph generate all permutations. Finally, two k-element subsets are related by a permutation, so any two configurations are reachable.")),
                    Paragraph(Text(
                        "For a real function f on a finite graph, telescoping along a simple path and applying Cauchy–Schwarz bounds (f(x) − f(y))² "
                            + "by the path length times the sum of squared differences along that path. A simple path has length less than the number of vertices. "
                            + "Thus, writing N = (↑(Fintype.card X) : ℝ), (f(x) − f(y))² ≤ N A(f), "
                            + "where A(f) is the sum of (f(s) − f(t))² over ordered adjacent pairs.")),
                    Paragraph(Text(
                        "Suppose Σ_s f(s) = 0. If X is empty, all the sums vanish. Otherwise choose vertices x and y where f is minimal and maximal. "
                            + "For every s, (f(s) − f(x))(f(y) − f(s)) ≥ 0. Summing and using the zero sum gives Σ_s f(s)² ≤ −N f(x)f(y). "
                            + "Since N(f(x) + f(y))² ≥ 0, it follows that 4Σ_s f(s)² ≤ N(f(x) − f(y))². "
                            + "Combining with the path bound yields 4Σ_s f(s)² ≤ N² A(f). "
                            + "Each configuration edge is supplied by a gate, so A(f) is at most the sum over all gates and configurations of the corresponding squared differences; repeated gates only increase that sum.")),
                    Paragraph(Text(
                        "Apply the real inequality separately to the real and imaginary parts of a complex vector with coordinate sum zero. "
                            + "Adding them, using |z|² = (Re z)² + (Im z)² and the factor one quarter in the gate identity, gives ||w||² ≤ N² E(w). "
                            + "A connected pattern on at least two qubits has at least one gate: otherwise the qubit graph has no edges and cannot connect the distinct labels zero and one.")),
                    Paragraph(Text(
                        "Identify a nonzero eigenvector v with w in the complex Euclidean space on X. Then Tw = μw, and ||w||² is positive. "
                            + "The existence of a nonzero coordinate also makes N positive. Combining the two energy bounds and cancelling ||w||² gives "
                            + "1 ≤ J²N²(1 − |μ|²). Division by the positive J²N², followed by (|μ| − 1)² ≥ 0, yields |μ| ≤ 1 − 1/(2J²N²).")),
                    Paragraph(Text(
                        "For the family in the statement, J ≤ (↑(max c 1) : ℝ)(↑n : ℝ)^a and N ≤ (↑n : ℝ)^k. Squaring these nonnegative bounds gives "
                            + "2J²N² ≤ 2(↑(max c 1) : ℝ)²(↑n : ℝ)^(2a + 2k). "
                            + "Taking reciprocals of positive quantities gives the required estimate with d = 1/(2(↑(max c 1) : ℝ)²) > 0 and b = 2a + 2k. "
                            + "These choices depend only on k, c and a, so the same estimate holds for every n and every eigenvector specified in the statement."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("monbroussou-et-al-2025-hamming-weight-pattern-spectral-gap"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SwapFormula() => ConfigurationBinders(
        All("a", FinType(), All("b", FinType(), All("s", ChoiceType(),
            Equal(Typed(LocalCall("swapConfig", X("a"), X("b"), X("s")), ChoiceType()),
                At(Qualified("Set", "powersetCard", "map"), X("k"),
                    At(Qualified("Equiv", "toEmbedding"),
                        At(Qualified("Equiv", "swap"), X("a"), X("b"))), X("s")))))));

    private static Formula GateFormula() => ConfigurationBinders(
        All("a", FinType(), All("b", FinType(), All("s", ChoiceType(), All("t", ChoiceType(),
            Equal(Typed(LocalCall("gateMatrix", X("a"), X("b"), X("s"), X("t")), Reals()),
                Add(If(Equal(X("s"), X("t")), Half(), Typed(D(0), Reals())),
                    If(Equal(X("s"), LocalCall("swapConfig", X("a"), X("b"), X("t"))),
                        Half(), Typed(D(0), Reals())))))))));

    private static Formula PatternFormula() => ConfigurationBinders(All("pat", PatternType(),
        Equal(Typed(LocalCall("patternMatrix", X("pat")), MatrixType()),
            At(Qualified("List", "prod"), At(Qualified("List", "reverse"),
                At(Qualified("List", "map"), LambdaOf("e", PairType(),
                    Typed(LocalCall("gateMatrix", First(X("e")), Second(X("e"))), MatrixType())),
                    X("pat")))))));

    private static Formula GraphFormula() => All("n", Naturals(), All("pat", PatternType(),
        Equal(Typed(LocalCall("qubitGraph", X("pat")), At(Qualified("SimpleGraph"), FinType())),
            At(Qualified("SimpleGraph", "fromRel"), LambdaOf("x", FinType(),
                LambdaOf("y", FinType(), Member(Pair(X("x"), X("y")), X("pat"))))))));

    private static Formula ConnectedFormula() => All("n", Naturals(), All("pat", PatternType(),
        Equivalence(LocalCall("connectedPattern", X("pat")),
            Conjunction(All("e", PairType(), Implication(Member(X("e"), X("pat")),
                    NotEqual(First(X("e")), Second(X("e"))))),
                At(Qualified("SimpleGraph", "Connected"), LocalCall("qubitGraph", X("pat")))))));

    private static Formula ClaimFormula()
    {
        Formula patn = At(X("pat"), X("n"));
        Formula complexMatrix = At(Qualified("Matrix", "map"), LocalCall("patternMatrix", patn),
            LambdaOf("x", Reals(), At(Qualified("Complex", "ofReal"), X("x"))));
        Formula eigenvector = Equal(At(Qualified("Matrix", "mulVec"), complexMatrix, X("v")),
            At(Qualified("HSMul", "hSMul"), Mu, X("v")));
        Formula bound = LE(new Formula.Norm(Mu), Subtract(Typed(D(1), Reals()),
            new Formula.Fraction(X("d"), new Formula.Power(
                Typed(At(Qualified("Nat", "cast"), X("n")), Reals()), X("b")))));
        Formula vectors = All("μ", Complexes(), All("v", Arrow(ChoiceType(), Complexes()),
            Implication(NotEqual(X("v"), At(Qualified("Function", "const"), ChoiceType(),
                    Typed(D(0), Complexes()))),
                Implication(Equal(SumOver("s", ChoiceType(), At(X("v"), X("s"))),
                    Typed(D(0), Complexes())), Implication(eigenvector, bound)))));
        Formula conclusion = Some("d", Reals(), Conjunction(LT(Typed(D(0), Reals()), X("d")),
            Some("b", Naturals(), All("n", Naturals(), Implication(LT(X("k"), X("n")),
                Implication(LE(D(2), X("n")), vectors))))));
        Formula hypothesis = All("n", Naturals(), Implication(LE(D(2), X("n")),
            Conjunction(LocalCall("connectedPattern", patn),
                LE(At(Qualified("List", "length"), patn),
                    Multiply(X("c"), new Formula.Power(X("n"), X("a")))))));
        Formula familyType = new Formula.TypeArrow(Typed(X("n"), Naturals()), PatternType());
        return All("k", Naturals(), All("c", Naturals(), All("a", Naturals(),
            Implication(LE(D(1), X("k")), All("pat", familyType,
                Implication(hypothesis, conclusion))))));
    }

    private static Formula ConfigurationBinders(Formula body) =>
        All("n", Naturals(), All("k", Naturals(), body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinType() => At(Qualified("Fin"), X("n"));
    private static Formula ChoiceType() => At(Qualified("Erdos7", "CommonTreeUnion", "Choice"), X("n"), X("k"));
    private static Formula PairType() => Seq(FinType(), Sp, Times, Sp, FinType());
    private static Formula PatternType() => At(Qualified("List"), Parenthesized(PairType()));
    private static Formula MatrixType() => At(Qualified("Matrix"), ChoiceType(), ChoiceType(), Reals());
    private static Formula Half() => new Formula.Fraction(Typed(D(1), Reals()), Typed(D(2), Reals()));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula X(string name) => name == "μ" ? Mu : F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "RandomCircuits", "HammingWeightPatternSpectralGap", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula Member(Formula value, Formula collection) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, collection);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
