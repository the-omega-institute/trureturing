using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ModelLevelEnsembleEquivalenceConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/ModelLevelEnsembleEquivalenceConverseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/giuffrida2025descriptionlength");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar statistic with bounded dyadic weights on binary square matrices separates model-level and measure-level ensemble equivalence.",
        H("Model-level equivalence does not imply measure-level equivalence"), Blocks(
            Paragraph(Text(
                "Giuffrida, Squartini, Grünwald and Garlaschelli, arXiv:2307.05645v4, Section III, p. 4: "
                + "“Specifically, we will focus on discrete data that can be represented as a binary n × m matrix G, i.e.” "
                + "Here m = n. Both indices range over Fin n and Bool represents the entries zero and one. "
                + "All displayed sums range over the whole indicated finite type. Natural cardinalities and n in real quotients "
                + "are coerced to the reals. Real division has its Lean total meaning at zero; only eventual positive sizes "
                + "enter the limits.")),
            Node("omega", "The size of a statistic fiber", OmegaFormula(),
                "Section III, p. 4: “Ω(c) denotes the number of configurations with c(G) = c, i.e.,” "
                + "followed by equation (15), which counts all binary matrices whose scalar statistic is c. "
                + "Finset.filter selects that fiber from Finset.univ and Finset.card counts it.", AssessedProvenance.FromLiterature(Source)),
            Node("pMic", "The microcanonical law", MicroFormula(),
                "Section III.A, p. 4: “When considering microcanonical models, entropy maximization yields the following functional form” "
                + "followed by equation (16). It is the uniform law on the selected fiber and zero outside it.", AssessedProvenance.FromLiterature(Source)),
            Node("IsMatched", "Expectation matching", MatchedFormula(),
                "Section III, p. 4: “The ML estimators θ̂(G) are found by solving the system of equations” "
                + "followed by equation (21). The equation equates the canonical expectation of the statistic to stat G. "
                + "On the same page: “When considering canonical models, entropy maximization yields the following well-known exponential form” "
                + "followed by equation (20). The canonical weights are these normalized exponentials.", AssessedProvenance.FromLiterature(Source)),
            Node("measureDiv", "Measure-level divergence", MeasureFormula(),
                "Section III.B, p. 5: “The maximum log-likelihood of a canonical model is linked to the microcanonical one through the Kullback-Leibler divergence:” "
                + "followed by equation (22). This is the divergence from the microcanonical law at stat G "
                + "to the canonical law at theta. At expectation-matched theta this is the source's measure divergence. "
                + "ClassicalDPI.klDivergence is the real finite sum of a times Real.log(a/b).", AssessedProvenance.FromLiterature(Source)),
            Node("lMic", "Maximized microcanonical likelihood", MicroLikelihoodFormula(),
                "Section III.A, p. 4: “Its maximum log-likelihood simply reads” followed by equation (17). "
                + "Exponentiating assigns the reciprocal size of the observed statistic's fiber.", AssessedProvenance.FromLiterature(Source)),
            Node("lCan", "Maximized canonical likelihood", CanonicalLikelihoodFormula(),
                "Section II, p. 3: “with θ̂(x) being the maximum-likelihood (ML) estimator of θ, i.e.” "
                + "followed by equation (5). The canonical likelihood is maximized over every real theta. The supremum also includes "
                + "limiting values approached at extreme statistic fibers.", AssessedProvenance.FromLiterature(Source)),
            Node("nmlMic", "Microcanonical normalized maximum likelihood", NmlFormula("nmlMic", "lMic"),
                "Section II, p. 3: “The unique solution to this minimax problem reads” followed by equation (8), "
                + "“which is a normalized maximum likelihood.” It divides the maximized likelihood by its sum over every possible data matrix.", AssessedProvenance.FromLiterature(Source)),
            Node("nmlCan", "Canonical normalized maximum likelihood", NmlFormula("nmlCan", "lCan"),
                "Section II, p. 3: “The unique solution to this minimax problem reads” followed by equation (8), "
                + "“which is a normalized maximum likelihood.” The canonical model uses the same likelihood-over-sum formula.", AssessedProvenance.FromLiterature(Source)),
            Node("modelDiv", "Model-level divergence", ModelFormula(),
                "Section IV.C, p. 9: “Inspired by the measure level definition of non-equivalence [18] of equation (35), we consider the following KL divergence” "
                + "followed by equation (69). It compares the two normalized maximum-likelihood distributions "
                + "using the real finite Kullback–Leibler divergence.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The converse of model-level ensemble equivalence", IffOf(Local("claim"), ClaimBody()),
                "Section IV.C, p. 9, following (71), verbatim: “i.e., whenever ensemble equivalence holds, "
                + "the corresponding microcanonical and canonical models are equivalent on the model level. "
                + "The reverse implication, verified here in the specific case of one-sided local constraints, "
                + "will be investigated in future work.” "
                + "The proposition is that converse, restricted to scalar statistics on binary n × n matrices and "
                + "to observation sequences with an eventually finite expectation-matching real parameter. "
                + "Tendsto uses Filter.atTop on natural sizes and nhds 0 on the reals, with scale n as in (35) and (70).", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("model-equivalence-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A scalar family refutes the converse"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Use the first-column statistic obtained by summing (1 + 2^(−i−1)) times the zero-one entry "
                    + "at row i. Its finite dyadic part lies in [0,1), and its integer part is the number of ones. "
                    + "Distinct first columns have distinct statistic values, so all matrix fibers have the same size. "
                    + "For an ordered finite list of energies, the canonical mass at rank k is at most 1/(k+1) "
                    + "for nonnegative theta and at most 1/(N−k) for nonpositive theta. A harmonic-sum bound then gives "
                    + "model divergence between zero and Real.log(4(n+1)²), whose quotient by n tends to zero. "
                    + "For checkerboard observations at even size n = 2m, factorization over bits bounds canonical "
                    + "first-column probability by 2^(−m) for every theta. Measure divergence divided by n is "
                    + "therefore at least Real.log(2)/2. Continuity and the two extreme-energy limits supply a finite "
                    + "expectation-matching theta for every n at least two. This contradicts the proposed converse. "
                    + "The result leaves the source's one-sided local-constraint equivalence intact."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("model-equivalence-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Q("D5", "S3", "Divergence",
        "ModelLevelEnsembleEquivalenceConverseRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula L(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula body, Formula type) => Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Mat(Formula n) => Arrow(At(Q("Fin"), n), Arrow(At(Q("Fin"), n), Q("Bool")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula BaseBinders(Formula body) =>
        All("n", Nat, All("stat", Arrow(Mat(V("n")), Real), body));
    private static Formula MatrixBinder(Formula body) => All("G", Mat(V("n")), body);
    private static Formula Canonical(Formula stat, Formula theta, Formula g) =>
        Div(At(Q("Real", "exp"), Mul(new Formula.Negate(theta), At(stat, g))),
            SumOver("H", Mat(V("n")), At(Q("Real", "exp"), Mul(new Formula.Negate(theta), At(stat, V("H"))))));

    private static Formula OmegaFormula() => BaseBinders(All("c", Real,
        Equal(L("omega", V("stat"), V("c")), At(Q("Finset", "card"),
            At(Q("Finset", "filter"), Lam("G", Mat(V("n")), Equal(At(V("stat"), V("G")), V("c"))),
                Typed(Q("Finset", "univ"), At(Q("Finset"), Mat(V("n")))))))));

    private static Formula MicroFormula() => BaseBinders(All("c", Real, MatrixBinder(
        Equal(L("pMic", V("stat"), V("c"), V("G")), Seq(Q("if"), Sp,
            Parenthesized(Equal(At(V("stat"), V("G")), V("c"))), Sp, Q("then"), Sp,
            Div(D(1), Typed(L("omega", V("stat"), V("c")), Real)), Sp, Q("else"), Sp, D(0))))));

    private static Formula MatchedFormula() => BaseBinders(All("theta", Real, MatrixBinder(
        IffOf(L("IsMatched", V("stat"), V("theta"), V("G")),
            Equal(SumOver("K", Mat(V("n")), Mul(Canonical(V("stat"), V("theta"), V("K")), At(V("stat"), V("K")))),
                At(V("stat"), V("G")))))));

    private static Formula MeasureFormula() => BaseBinders(MatrixBinder(All("theta", Real,
        Equal(L("measureDiv", V("stat"), V("G"), V("theta")),
            At(Q("D5", "S3", "Divergence", "ClassicalDPI", "klDivergence"),
                L("pMic", V("stat"), At(V("stat"), V("G"))),
                Lam("K", Mat(V("n")), Canonical(V("stat"), V("theta"), V("K"))))))));

    private static Formula MicroLikelihoodFormula() => BaseBinders(MatrixBinder(
        Equal(L("lMic", V("stat"), V("G")), Div(D(1), Typed(L("omega", V("stat"), At(V("stat"), V("G"))), Real)))));

    private static Formula CanonicalLikelihoodFormula() => BaseBinders(MatrixBinder(
        Equal(L("lCan", V("stat"), V("G")), At(Q("iSup"),
            Lam("theta", Real, Canonical(V("stat"), V("theta"), V("G")))))));

    private static Formula NmlFormula(string name, string likelihood) => BaseBinders(MatrixBinder(
        Equal(L(name, V("stat"), V("G")), Div(L(likelihood, V("stat"), V("G")),
            SumOver("H", Mat(V("n")), L(likelihood, V("stat"), V("H")))))));

    private static Formula ModelFormula() => BaseBinders(
        Equal(L("modelDiv", V("stat")), At(Q("D5", "S3", "Divergence", "ClassicalDPI", "klDivergence"),
            L("nmlMic", V("stat")), L("nmlCan", V("stat")))));

    private static Formula Limit(Formula body) => At(Q("Filter", "Tendsto"),
        Lam("n", Nat, body), Q("Filter", "atTop"), At(Q("nhds"), Typed(D(0), Real)));

    private static Formula ClaimBody()
    {
        Formula statFamily = Seq(Forall, Sp, Typed(V("n"), Nat), Comma, Sp, Arrow(Mat(V("n")), Real));
        Formula obsFamily = Seq(Forall, Sp, Typed(V("n"), Nat), Comma, Sp, Mat(V("n")));
        Formula theta = At(V("theta"), V("n"));
        Formula observed = At(V("obs"), V("n"));
        Formula statistic = At(V("stat"), V("n"));
        Formula matched = At(Q("Filter", "Eventually"),
            Lam("n", Nat, L("IsMatched", statistic, theta, observed)), Q("Filter", "atTop"));
        return All("stat", Parenthesized(statFamily),
            Imp(Limit(Div(L("modelDiv", statistic), Typed(V("n"), Real))),
                All("obs", Parenthesized(obsFamily), All("theta", Arrow(Nat, Real),
                    Imp(matched, Limit(Div(L("measureDiv", statistic, observed, theta), Typed(V("n"), Real))))))));
    }
}
