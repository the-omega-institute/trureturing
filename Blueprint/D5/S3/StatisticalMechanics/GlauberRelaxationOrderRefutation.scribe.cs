using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class GlauberRelaxationOrderRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/luozhenliueblerdahlsten2023annealing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-state Glauber annealing run has a larger spectral gap but a smaller energy relaxation rate than a partial swap process.",
        H("Glauber relaxation times do not order energy relaxation rates"), Blocks(
            Paragraph(Text(
                "The finite state space is Fin N. Energies and probabilities are real-valued, "
                    + "and probability vectors are columns. The relation A describes the neighbourhood, "
                    + "while beta is the inverse-temperature schedule. All sums over Fin N include every state. "
                    + "A DecidableRel A supplies a decision for each adjacency statement A i j; "
                    + "the bracketed DecidableRel A is an anonymous typeclass assumption. Natural numbers in real-valued "
                    + "expressions are coerced to the reals.")),
            Node("regularNeighborhood", "A regular undirected neighbourhood", RegularNeighborhoodFormula(),
                "Every state has exactly n neighbours, with n at least one. Adjacency is symmetric and irreflexive. "
                    + "Finset.univ is the finite set of all states; Finset.filter retains the states adjacent to j, "
                    + "and Finset.card counts them. This is the equal-sized neighbourhood setting of Eqs. (31) and (78)."),
            Node("gibbs", "The Gibbs distribution", GibbsFormula(),
                "The thermal probabilities used in Eq. (32) are normalized Boltzmann weights. "
                    + "Real.exp is the real exponential, and the denominator sums its weights over every state."),
            Node("edgeWeight", "Accepted transitions along edges", EdgeWeightFormula(),
                "Equations (31) and (32) give the Gibbs-ratio acceptance probability divided by the neighbourhood size n. "
                    + "The entry vanishes when A i j is false. The definition itself imposes no positivity or regularity assumptions."),
            Node("glauber", "The Glauber transition matrix", GlauberFormula(),
                "The off-diagonal entries are the accepted edge transitions. Each diagonal entry is one minus "
                    + "the sum of the edge weights in that column over all l, including l = j. "
                    + "For an irreflexive neighbourhood the self-edge weight is zero, so this is Eq. (31)."),
            Node("isSARun", "Annealing from an initial thermal state", SARunFormula(),
                "D5.S3.TotalVariation.CycleSingleCutMinimax.Probability requires nonnegative entries with total mass one, "
                    + "as required for the states in Eq. (30). Every time slice is a probability vector. "
                    + "The initial vector is the Gibbs distribution at beta(0), "
                    + "and Eq. (30) updates p(t) using the transition matrix at beta(t + 1). "
                    + "Matrix.mulVec multiplies a matrix by a column vector: its i-th coordinate is the sum "
                    + "of the matrix entries in row i times the corresponding vector entries. "
                    + "The recursion holds at every natural time."),
            Describe.Lean(
                DescribeId.Create("glauber-order-probability-mulvec"),
                DeclarationHandle.Create(Prefix + "probability_mulVec"),
                H("Column-stochastic matrices preserve probability"),
                StatementSource.FromAuthor(Disp(ProbabilityMulVecFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A real matrix with nonnegative entries and every column summing to one sends "
                        + "a probability vector to another probability vector under Matrix.mulVec."))),
                DescribeRole.Theorem),
            Node("meanEnergy", "Mean energy", MeanEnergyFormula(),
                "Mean energy is the sum of each energy level times its probability, as in Eqs. (44) and (46). "
                    + "The expression is defined for any real-valued vector p."),
            Node("energyRate", "The energy relaxation rate", EnergyRateFormula(),
                "Equation (46) divides the actual energy change at step k by the change needed to reach "
                    + "the Gibbs energy at the next inverse temperature. The conjecture below assumes that this denominator is nonzero."),
            Node("lambda2", "The second characteristic root in descending order", Lambda2Formula(),
                "Matrix.charpoly P is the characteristic polynomial det(X I - P). Polynomial.roots is its "
                    + "multiset of real roots, with algebraic multiplicity. Multiset.sort lists these roots "
                    + "using the relation y <= x, hence in descending order. List.getD takes the entry at "
                    + "zero-based index 1 and returns the real number zero if that entry is absent. "
                    + "When the characteristic polynomial splits over the reals and N is at least two, "
                    + "this is the second largest eigenvalue counted with multiplicity, as in Eq. (50)."),
            Node("claim", "The relaxation-order conjecture", ClaimFormula(),
                "Equation (50) asserts that a relaxation time no greater than that of a partial swap process "
                    + "implies an energy relaxation rate at least as large. "
                    + "Here StrictMono beta means that beta(t) < beta(u) whenever t < u. "
                    + "Polynomial.Splits says that the displayed characteristic polynomial splits into linear factors over the reals. "
                    + "The hypotheses require at least two states, a regular neighbourhood, positive strictly increasing inverse "
                    + "temperatures, the entire annealing run, real splitting, and a partial swap rate 0 < m <= 1. "
                    + "They also require nonincreasing actual energy, actual energy at least the current Gibbs energy, "
                    + "nonincreasing Gibbs energy, and a nonzero energy denominator, in that order. "
                    + "Proposition 2 gives partial swap relaxation time 1/m. With m positive, the final spectral-gap "
                    + "hypothesis ensures that the Glauber relaxation time is finite and at most 1/m. "
                    + "The conclusion is the energy-rate comparison of Eq. (50)."),
            Describe.Lean(
                DescribeId.Create("glauber-order-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A four-state cycle reverses the proposed order"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take the cycle 0-1-2-3-0 with energies (0, 1, 1, 2) and two neighbours per state. "
                        + "Choose the inverse-temperature schedule with Real.exp(beta(t)) = 2 at t = 0 and t + 31 for t > 0, "
                        + "so its successive values are 2, 32, 33, 34, and so on. Start in the Gibbs state and apply the "
                        + "Glauber updates. At the second step, k = 1, the energy relaxation rate is 2673903/17337104, "
                        + "and the second characteristic root is 1/2 + Real.sqrt(64/545). All the energy and spectral "
                        + "hypotheses hold, while the partial swap rate m = 5/32 is strictly below the Glauber spectral "
                        + "gap and strictly above the energy relaxation rate. Thus the implication in Eq. (50) fails."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("luo-zhen-liu-ebler-dahlsten-2023-relaxation-order-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("glauber-order-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ProbabilityFormula() => SizeBinder(All("p", States(),
        IffOf(At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), V("p")),
            And(All("i", FinType(), LE(D(0), At(V("p"), V("i")))),
                Equal(SumOver("i", At(V("p"), V("i"))), D(1))))));

    private static Formula RegularNeighborhoodFormula()
    {
        Formula neighbours = At(Qualified("Finset", "filter"),
            LambdaOf("i", FinType(), At(V("A"), V("i"), V("j"))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), FinType())));
        Formula conditions = And(LE(D(1), V("n")),
            And(All("i", FinType(), All("j", FinType(),
                    Imp(At(V("A"), V("i"), V("j")), At(V("A"), V("j"), V("i"))))),
                And(All("i", FinType(), new Formula.Not(Parenthesized(At(V("A"), V("i"), V("i"))))),
                    All("j", FinType(), Equal(At(Qualified("Finset", "card"), neighbours), V("n"))))));
        return GraphBinders(IffOf(LocalCall("regularNeighborhood", V("n"), V("A")), conditions));
    }

    private static Formula GibbsFormula()
    {
        Formula weight = At(Qualified("Real", "exp"), Multiply(new Formula.Negate(V("b")), At(V("E"), V("i"))));
        Formula normalization = SumOver("j",
            At(Qualified("Real", "exp"), Multiply(new Formula.Negate(V("b")), At(V("E"), V("j")))));
        return SizeBinder(EnergyBinder(All("b", Reals(), All("i", FinType(),
            Equal(LocalCall("gibbs", V("E"), V("b"), V("i")), new Formula.Fraction(weight, normalization))))));
    }

    private static Formula EdgeWeightFormula()
    {
        Formula numerator = LocalCall("gibbs", V("E"), V("b"), V("i"));
        Formula denominator = Multiply(Typed(V("n"), Reals()),
            Add(LocalCall("gibbs", V("E"), V("b"), V("i")), LocalCall("gibbs", V("E"), V("b"), V("j"))));
        return GraphBinders(EnergyBinder(All("b", Reals(), IndexBinders(
            Equal(LocalCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("i"), V("j")),
                Conditional(At(V("A"), V("i"), V("j")), new Formula.Fraction(numerator, denominator), D(0)))))));
    }

    private static Formula GlauberFormula()
    {
        Formula diagonal = Subtract(D(1), SumOver("l",
            LocalCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("l"), V("j"))));
        Formula offDiagonal = LocalCall("edgeWeight", V("n"), V("A"), V("E"), V("b"), V("i"), V("j"));
        return GraphBinders(EnergyBinder(All("b", Reals(), IndexBinders(
            Equal(LocalCall("glauber", V("n"), V("A"), V("E"), V("b"), V("i"), V("j")),
                Conditional(Equal(V("i"), V("j")), diagonal, offDiagonal))))));
    }

    private static Formula SARunFormula()
    {
        Formula next = Add(V("t"), D(1));
        Formula transition = LocalCall("glauber", V("n"), V("A"), V("E"), At(V("beta"), next));
        Formula recursion = All("t", Naturals(), Equal(At(V("p"), next),
            At(Qualified("Matrix", "mulVec"), transition, At(V("p"), V("t")))));
        Formula conditions = And(All("t", Naturals(),
            At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), At(V("p"), V("t")))),
            And(Equal(At(V("p"), D(0)), LocalCall("gibbs", V("E"), At(V("beta"), D(0)))), recursion));
        return And(ProbabilityFormula(), GraphBinders(EnergyBinder(RunBinders(
            IffOf(LocalCall("isSARun", V("n"), V("A"), V("E"), V("beta"), V("p")), conditions)))));
    }

    private static Formula ProbabilityMulVecFormula()
    {
        Formula probability = At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), V("p"));
        Formula image = At(Qualified("Matrix", "mulVec"), V("P"), V("p"));
        Formula imageProbability = At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), image);
        Formula nonnegative = All("i", FinType(), All("j", FinType(),
            LE(D(0), At(At(V("P"), V("i")), V("j")))));
        Formula columns = All("j", FinType(), Equal(
            SumOver("i", At(At(V("P"), V("i")), V("j"))), D(1)));
        return SizeBinder(All("P", MatrixType(), All("p", States(),
            Imp(nonnegative, Imp(columns, Imp(probability, imageProbability))))));
    }

    private static Formula MeanEnergyFormula() => SizeBinder(EnergyBinder(All("p", States(),
        Equal(LocalCall("meanEnergy", V("E"), V("p")),
            SumOver("i", Multiply(At(V("E"), V("i")), At(V("p"), V("i"))))))));

    private static Formula EnergyRateFormula()
    {
        Formula next = Add(V("k"), D(1));
        Formula current = LocalCall("meanEnergy", V("E"), At(V("p"), V("k")));
        Formula numerator = Subtract(LocalCall("meanEnergy", V("E"), At(V("p"), next)), current);
        Formula denominator = Subtract(LocalCall("meanEnergy", V("E"),
            LocalCall("gibbs", V("E"), At(V("beta"), next))), current);
        return SizeBinder(EnergyBinder(RunBinders(All("k", Naturals(),
            Equal(LocalCall("energyRate", V("E"), V("beta"), V("p"), V("k")),
                new Formula.Fraction(numerator, denominator))))));
    }

    private static Formula Lambda2Formula()
    {
        Formula roots = At(Qualified("Polynomial", "roots"), At(Qualified("Matrix", "charpoly"), V("P")));
        Formula descending = LambdaOf("x", Reals(), LambdaOf("y", Reals(), LE(V("y"), V("x"))));
        Formula sorted = At(Qualified("Multiset", "sort"), roots, descending);
        return SizeBinder(All("P", MatrixType(), Equal(LocalCall("lambda2", V("P")),
            At(Qualified("List", "getD"), sorted, D(1), Typed(D(0), Reals())))));
    }

    private static Formula ClaimFormula()
    {
        Formula next = Add(V("k"), D(1));
        Formula transition = LocalCall("glauber", V("n"), V("A"), V("E"), At(V("beta"), next));
        Formula actual = LocalCall("meanEnergy", V("E"), At(V("p"), V("k")));
        Formula actualNext = LocalCall("meanEnergy", V("E"), At(V("p"), next));
        Formula thermal = LocalCall("meanEnergy", V("E"), LocalCall("gibbs", V("E"), At(V("beta"), V("k"))));
        Formula thermalNext = LocalCall("meanEnergy", V("E"), LocalCall("gibbs", V("E"), At(V("beta"), next)));
        Formula[] hypotheses =
        [
            LE(D(2), V("N")),
            LocalCall("regularNeighborhood", V("n"), V("A")),
            All("t", Naturals(), LT(D(0), At(V("beta"), V("t")))),
            At(Qualified("StrictMono"), V("beta")),
            LocalCall("isSARun", V("n"), V("A"), V("E"), V("beta"), V("p")),
            At(Qualified("Polynomial", "Splits"), At(Qualified("Matrix", "charpoly"), transition)),
            LT(D(0), V("m")),
            LE(V("m"), D(1)),
            LE(actualNext, actual),
            LE(thermal, actual),
            LE(thermalNext, thermal),
            NotEqual(thermalNext, actual),
            LE(V("m"), Subtract(D(1), LocalCall("lambda2", transition)))
        ];
        Formula body = LE(V("m"), LocalCall("energyRate", V("E"), V("beta"), V("p"), V("k")));
        for (var index = hypotheses.Length - 1; index >= 0; index--)
            body = Imp(hypotheses[index], body);
        body = All("k", Naturals(), All("m", Reals(), body));
        return IffOf(Local("claim"), GraphBinders(EnergyBinder(RunBinders(body))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "GlauberRelaxationOrderRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Word(string word) => Seq(Mathrm, Grp(V(word)));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula FinType() => At(Qualified("Fin"), V("N"));
    private static Formula States() => Parenthesized(Arrow(FinType(), Reals()));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinType(), FinType(), Reals());
    private static Formula SizeBinder(Formula body) => All("N", Naturals(), body);
    private static Formula GraphBinders(Formula body) => SizeBinder(All("n", Naturals(),
        All("A", Parenthesized(Arrow(FinType(), Arrow(FinType(), Qualified("Prop")))),
            Seq(Seq(OpenBracket, At(Qualified("DecidableRel"), V("A")), CloseBracket), Sp,
                Parenthesized(body)))));
    private static Formula EnergyBinder(Formula body) => All("E", States(), body);
    private static Formula RunBinders(Formula body) =>
        All("beta", Parenthesized(Arrow(Naturals(), Reals())),
            All("p", Parenthesized(Arrow(Naturals(), States())), body));
    private static Formula IndexBinders(Formula body) => All("i", FinType(), All("j", FinType(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), FinType())), Sp, Parenthesized(body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Word("if"), Sp, Parenthesized(condition), Sp, Word("then"), Sp,
            Parenthesized(yes), Sp, Word("else"), Sp, Parenthesized(no));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
