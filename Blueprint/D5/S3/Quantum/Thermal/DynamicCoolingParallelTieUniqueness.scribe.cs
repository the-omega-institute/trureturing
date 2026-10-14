using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class DynamicCoolingParallelTieUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/reda2026dynamiccooling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every initial excited population strictly between zero and one half, global unitary cooling gives a strictly smaller common target population than equal parallel single-target groups whenever M is at least two and N is at least M plus two, except for the pair (6, 2).",
        H("Strict global advantage over parallel dynamic cooling"),
        Blocks(
            Node("tau", "Single-qubit thermal weights", "tau", TauFormula(),
                "Equations (2) and (3) give the ground-state weight 1 minus P and the excited-state weight P. The definition is a real-valued function on Fin 2 for every real P; the thermal regime used below is 0 < P < 1/2.",
                AssessedProvenance.FromLiterature(Source)),
            Node("thermal-weight", "The weight of a register string", "thermalWeight", ThermalWeightFormula(),
                "Equations (2) through (4) describe N independent identical thermal qubits. A computational string is a function from Fin N to Fin 2, and its weight is the product of the single-qubit weights over all coordinates. The product also includes the empty register.",
                AssessedProvenance.FromLiterature(Source)),
            Node("rho", "The diagonal thermal register state", "rho", RhoFormula(),
                "Equation (4) is the tensor power of the single-qubit state. In the computational basis it is Matrix.diagonal of the register weights, each embedded from the real numbers into the complex numbers.",
                AssessedProvenance.FromLiterature(Source)),
            Node("population", "The excited diagonal entry of a marginal", "population", PopulationFormula(),
                "For a complex matrix A and a coordinate alpha, sum its diagonal entries over all strings whose alpha coordinate is one. This is the excited diagonal entry of the one-qubit marginal. The definition applies to every matrix, without positivity or normalization assumptions.",
                AssessedProvenance.FromRepo(Source)),
            Node("coherence", "The off-diagonal entry of a marginal", "coherence", CoherenceFormula(),
                "For each string whose alpha coordinate is zero, take the entry of A from that string to the string obtained by Function.update at alpha with value one. Their sum is the zero-one entry of the one-qubit marginal. This definition also applies to every complex matrix.",
                AssessedProvenance.FromRepo(Source)),
            Node("feasible", "Common diagonal target marginals", "feasible", FeasibleFormula(),
                "Requirement 2 in Section I and the global optimization in Equation (90) ask for identical diagonal marginals on the first M coordinates. A real g belongs to this set when one unitary makes every coordinate alpha with Fin.val alpha < M have excited population g and coherence zero. The conjugated matrix has trace one and is Hermitian: the product weights sum to one and the initial matrix is real diagonal. Thus the other diagonal entry is 1 minus g and the other off-diagonal entry is the conjugate of zero. These two conditions say exactly that each target marginal is diag(1 minus g, g).",
                AssessedProvenance.FromLiterature(Source)),
            Node("pglob", "The optimal common target population", "pGlob", PGlobFormula(),
                "Section I, requirement 2, and Equation (90) define the global optimum under equal diagonal target marginals. Here it is sInf in the real numbers of the set of feasible common populations. The definition is made for every N, M and P; the theorem uses parameters for which this set is nonempty and bounded below.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The strict global-versus-parallel inequality", "claim", ClaimFormula(),
                "Section IX, Equations (88) through (92), compares global cooling with M disjoint groups of size floor(N/M), each cooling one target, while leaving N modulo M qubits unused. The displayed Nat.div operator denotes natural-number integer division. The conjectured uniqueness of the exceptional tie gives the strict inequality for every natural pair with 2 <= M and M + 2 <= N other than (6, 2), and every real P1 with 0 < P1 < 1/2. The equality at (6, 2) is stated in Equation (92); it is not asserted by this claim.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("dynamic-cooling-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Global cooling strictly improves the parallel benchmark"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For any unitary U, the squared moduli of its entries have row and column sums one. For an output set R, summing those squared moduli over R gives coefficients between zero and one whose total is the size of R. A threshold separating a set of that many smallest thermal weights from its complement therefore bounds the probability of R from below.")),
                    Paragraph(Text(
                        "Let n be floor(N/M) and r be N modulo M. Among n-bit strings, the half-hot set consists of strings of weight greater than n/2 together with strings of weight exactly n/2 whose target bit is one. Complementing every bit pairs this set with its complement. Its thermal weights are at most the threshold P1 to the power ceil(n/2) times (1 minus P1) to the power n minus ceil(n/2), and the remaining weights are at least that threshold. The cutoff bound shows that its total weight is a lower bound for the optimal single-target population.")),
                    Paragraph(Text(
                        "A cooling permutation in each of the M blocks sends the half-hot set to the target-excited half, so all targets initially reach that total weight. A real reflection then exchanges two orthogonal unit vectors: the equal superposition of M basis strings, each with exactly one target excited, and one basis string with every target in its ground state. The strings have total excitation counts k = ceil(n/2) and K = M floor(n/2) + r, respectively, and are fixed by the block permutation. The reflection reduces every target population by the same positive amount, the difference of their thermal weights divided by M, while every target coherence remains zero.")),
                    Paragraph(Text(
                        "The arithmetic inequality ceil(n/2) < M floor(n/2) + (N modulo M) holds under the stated assumptions except at (N, M) = (6, 2). Since thermal weights strictly decrease with excitation count when 0 < P1 < 1/2, this gives a feasible common population strictly below the single-target lower bound. Taking the infimum over global unitaries proves the claim for every allowed pair and temperature."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("reda-sacchi-macchiavello-guarnieri-2026-dynamic-cooling-tie-uniqueness"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("dynamic-cooling-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Thermal", "DynamicCoolingParallelTieUniqueness", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => At(Qualified("Fin"), n);
    private static Formula Register() => Parenthesized(new Formula.TypeArrow(Fin(X("N")), Fin(D(2))));
    private static Formula RegisterMatrix() => At(Qualified("Matrix"), Register(), Register(), Complexes());
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula OfReal(Formula value) => At(Qualified("Complex", "ofReal"), value);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        F.Text, Grp(X("if")), Sp, Parenthesized(condition), Sp, F.Text, Grp(X("then")), Sp, yes,
        Sp, F.Text, Grp(X("else")), Sp, no));
    private static Formula SumOver(string variable, Formula type, Formula summand) => Seq(
        new Formula.Subscript(Sum, Seq(X(variable), Colon, Sp, type)), Sp, Parenthesized(summand));
    private static Formula LambdaOver(string variable, Formula type, Formula body) => Parenthesized(Seq(
        F.Text, Grp(X("fun")), Sp, X(variable), Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula TauFormula() => All("P", Reals(), All("b", Fin(D(2)), Equal(
        LocalCall("tau", X("P"), X("b")),
        IfThenElse(Equal(X("b"), D(0)), Subtract(D(1), X("P")), X("P")))));

    private static Formula ThermalWeightFormula()
    {
        Formula product = Seq(new Formula.Subscript(Prod, Seq(X("j"), Colon, Sp, Fin(X("N")))),
            Sp, LocalCall("tau", X("P"), At(X("x"), X("j"))));
        return All("N", Naturals(), All("P", Reals(), All("x", Register(), Equal(
            LocalCall("thermalWeight", X("P"), X("x")), product))));
    }

    private static Formula RhoFormula() => All("N", Naturals(), All("P", Reals(), Equal(
        LocalCall("rho", X("N"), X("P")), At(Qualified("Matrix", "diagonal"),
            LambdaOver("x", Register(), OfReal(LocalCall("thermalWeight", X("P"), X("x"))))))));

    private static Formula PopulationFormula() => All("N", Naturals(), All("A", RegisterMatrix(),
        All("alpha", Fin(X("N")), Equal(LocalCall("population", X("A"), X("alpha")),
            SumOver("x", Register(), IfThenElse(Equal(At(X("x"), X("alpha")), D(1)),
                At(X("A"), X("x"), X("x")), D(0)))))));

    private static Formula CoherenceFormula() => All("N", Naturals(), All("A", RegisterMatrix(),
        All("alpha", Fin(X("N")), Equal(LocalCall("coherence", X("A"), X("alpha")),
            SumOver("x", Register(), IfThenElse(Equal(At(X("x"), X("alpha")), D(0)),
                At(X("A"), X("x"), At(Qualified("Function", "update"), X("x"), X("alpha"), D(1))),
                D(0)))))));

    private static Formula FeasibleFormula()
    {
        Formula evolved = Multiply(Multiply(X("U"), LocalCall("rho", X("N"), X("P"))),
            At(Qualified("star"), X("U")));
        Formula targets = All("alpha", Fin(X("N")), Implies(
            Less(At(Qualified("Fin", "val"), X("alpha")), X("M")),
            And(Equal(LocalCall("population", evolved, X("alpha")), OfReal(X("g"))),
                Equal(LocalCall("coherence", evolved, X("alpha")), D(0)))));
        Formula predicate = Some("U", RegisterMatrix(), And(
            Member(X("U"), At(Qualified("Matrix", "unitaryGroup"), Register(), Complexes())), targets));
        Formula set = Seq(OpenBrace, X("g"), Colon, Sp, Reals(), Sp, Mid, Sp, predicate, CloseBrace);
        return All("N", Naturals(), All("M", Naturals(), All("P", Reals(), Equal(
            LocalCall("feasible", X("N"), X("M"), X("P")), set))));
    }

    private static Formula PGlobFormula() => All("N", Naturals(), All("M", Naturals(), All("P", Reals(), Equal(
        LocalCall("pGlob", X("N"), X("M"), X("P")),
        At(Qualified("sInf"), LocalCall("feasible", X("N"), X("M"), X("P")))))));

    private static Formula ClaimFormula()
    {
        Formula quotient = At(Qualified("Nat", "div"), X("N"), X("M"));
        Formula inequality = Less(LocalCall("pGlob", X("N"), X("M"), X("P1")),
            LocalCall("pGlob", quotient, D(1), X("P1")));
        Formula temperatures = All("P1", Reals(), Implies(Less(D(0), X("P1")),
            Implies(Less(X("P1"), new Formula.Fraction(D(1), D(2))), inequality)));
        Formula statement = All("N", Naturals(), All("M", Naturals(),
            Implies(AtMost(D(2), X("M")), Implies(AtMost(Add(X("M"), D(2)), X("N")),
                Implies(NotEqual(Pair(X("N"), X("M")), Pair(D(6), D(2))), temperatures)))));
        return Equivalent(Local("claim"), statement);
    }
}
