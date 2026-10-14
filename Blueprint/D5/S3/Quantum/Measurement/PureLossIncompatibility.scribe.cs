using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class PureLossIncompatibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/PureLossIncompatibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/mehboudi2025lossincompatibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every natural n at least one, some n+1 binary measurements on the full one-mode Fock space remain incompatible under pure loss of transmissivity 1/n.",
        H("Binary measurement incompatibility under pure loss"), Blocks(
            Paragraph(Text(
                "The one-mode Hilbert space consists of square-summable complex sequences. "
                    + "The outer coordinate of the two-mode space indexes the environment; "
                    + "each coordinate is a vector of the retained mode. ContinuousLinearMap "
                    + "denotes continuous complex-linear maps, and the operator 1 is the identity. "
                    + "All occupation numbers are included. Named objects retain their Lean "
                    + "namespaces, and a natural number annotated as real denotes its real cast.")),
            Node("h", "The one-mode Fock space", "H", HFormula(),
                "The exponent two gives the Hilbert norm on the completed one-mode Fock space.",
                AssessedProvenance.FromRepo()),
            Node("k", "The retained mode and its environment", "K", KFormula(),
                "A vector is a square-summable family of retained-mode vectors indexed by the environment occupation number.",
                AssessedProvenance.FromRepo()),
            Node("op", "Bounded operators on the retained mode", "Op", OpFormula(),
                "These are continuous complex-linear endomorphisms of the one-mode Hilbert space.",
                AssessedProvenance.FromRepo()),
            Node("amplify", "An operator acting in every environment coordinate", "amplify",
                AmplifyFormula(),
                "Amplification uses lp.mapCLM to apply the same retained-mode operator to each environment coordinate. The equation characterizes its action on every vector.",
                AssessedProvenance.FromRepo()),
            Node("vacuum-embedding", "Embedding with a vacuum environment", "vacuumEmbedding",
                VacuumEmbeddingFormula(),
                "The retained vector occupies environment coordinate zero. All other environment coordinates vanish; lp.single has exponent two and values in the retained-mode Hilbert space.",
                AssessedProvenance.FromRepo()),
            Node("stinespring", "The beam-splitter dilation", "stinespring", StinespringFormula(),
                "First place the environment in the vacuum, then apply the full two-mode beam splitter. Subtype.val supplies the transmissivity and Subtype.property supplies its interval condition. The isometry is viewed as a continuous linear map.",
                AssessedProvenance.FromRepo()),
            Describe.Lean(
                DescribeId.Create("pure-loss-vacuum-tensor"), DeclarationHandle.Create(Prefix + "vacuum_tensor"),
                H("The vacuum embedding is a tensor product"),
                StatementSource.FromAuthor(Disp(All("v", Local("H"),
                    Equal(LocalCall("vacuumEmbedding", X("v")),
                        At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "FockAttenuator",
                                "BeamSplitter", "tensor"), X("v"),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Embedding a retained-mode vector in environment coordinate zero is exactly its tensor product with the environment vacuum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-loss-split-zero"), DeclarationHandle.Create(Prefix + "split_zero"),
                H("Vacuum through the beam splitter"),
                StatementSource.FromAuthor(Disp(All("tau", LossType(),
                    Equal(LocalCall("stinespring", X("tau"),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(0))),
                        At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "FockAttenuator",
                            "BeamSplitter", "fockPair"), D(0), D(0)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vacuum in both modes is fixed by the beam splitter for every transmissivity in the closed unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-loss-split-one"), DeclarationHandle.Create(Prefix + "split_one"),
                H("One photon through the beam splitter"),
                StatementSource.FromAuthor(Disp(All("tau", LossType(),
                    Equal(LocalCall("stinespring", X("tau"),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(1))),
                        Add(Seq(Parenthesized(At(Qualified("Complex", "ofReal"),
                                    At(Qualified("Real", "sqrt"), At(Qualified("Subtype", "val"), X("tau"))))),
                                Sp, Cdot, Sp, Parenthesized(At(Qualified("D5", "S3", "Quantum",
                                    "QuantumChannels", "FockAttenuator", "BeamSplitter", "fockPair"), D(1), D(0)))),
                            Seq(Parenthesized(At(Qualified("Complex", "ofReal"),
                                    At(Qualified("Real", "sqrt"), new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
                                        At(Qualified("Subtype", "val"), X("tau")))))),
                                Sp, Cdot, Sp, Parenthesized(At(Qualified("D5", "S3", "Quantum",
                                    "QuantumChannels", "FockAttenuator", "BeamSplitter", "fockPair"), D(0), D(1))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A single input photon has retained-mode amplitude sqrt(tau) and environment amplitude sqrt(1-tau), both viewed as complex scalars."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-loss-split-zero-coord"), DeclarationHandle.Create(Prefix + "split_zero_coord"),
                H("Environment slices of the vacuum output"),
                StatementSource.FromAuthor(Disp(All("tau", LossType(), All("k", Naturals(),
                    Equal(At(LocalCall("stinespring", X("tau"),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(0))), X("k")),
                        At(Qualified("ite"), Equal(X("k"), D(0)),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(0)), D(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vacuum output has the retained vacuum in environment slice zero and the zero vector in every other slice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-loss-split-one-coord"), DeclarationHandle.Create(Prefix + "split_one_coord"),
                H("Environment slices of the one-photon output"),
                StatementSource.FromAuthor(Disp(All("tau", LossType(), All("k", Naturals(),
                    Equal(At(LocalCall("stinespring", X("tau"),
                            At(Qualified("D5", "S3", "Estimation",
                                "TransmissivityBetaPriorProbeRefutation", "e"), D(1))), X("k")),
                        At(Qualified("ite"), Equal(X("k"), D(0)),
                            Seq(Parenthesized(At(Qualified("Complex", "ofReal"),
                                    At(Qualified("Real", "sqrt"), At(Qualified("Subtype", "val"), X("tau"))))),
                                Sp, Cdot, Sp, Parenthesized(At(Qualified("D5", "S3", "Estimation",
                                    "TransmissivityBetaPriorProbeRefutation", "e"), D(1)))),
                            At(Qualified("ite"), Equal(X("k"), D(1)),
                                Seq(Parenthesized(At(Qualified("Complex", "ofReal"),
                                        At(Qualified("Real", "sqrt"), new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
                                            At(Qualified("Subtype", "val"), X("tau")))))),
                                    Sp, Cdot, Sp, Parenthesized(At(Qualified("D5", "S3", "Estimation",
                                        "TransmissivityBetaPriorProbeRefutation", "e"), D(0)))), D(0)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Environment slice zero contains sqrt(tau) times the retained one-photon vector; slice one contains sqrt(1-tau) times the retained vacuum. Every higher environment slice vanishes."))),
                DescribeRole.Theorem),
            Node("dual-loss", "The dual pure-loss action on effects", "dualLoss", DualLossFormula(),
                "Pull the amplified operator back along the vacuum beam-splitter dilation. This operator satisfies the trace relation defining the loss dual and is its unique solution. ContinuousLinearMap.adjoint is the Hilbert-space adjoint, and ContinuousLinearMap.comp is composition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("is-loss-dual", "The defining trace relation of the loss dual", "IsLossDual",
                IsLossDualFormula(),
                "For every pure input psi, apply beamSplitter to tensor psi (e 0) and discard the environment with purePartialTrace. The Fock-basis sum is the trace of M times this output state; HasSum requires convergence to the quadratic form of N. The frozen tensor convention places the environment in the outer sequence coordinate. The vectors e n form the retained-mode Fock basis. This is the source's dual relation on pure states, which determines the bounded operator uniquely.",
                AssessedProvenance.FromLiterature(Source)),
            Node("binary-povm", "A binary positive operator-valued measurement", "IsBinaryPOVM",
                BinaryPOVMFormula(),
                "Both effects are positive and their sum is the identity. The outcomes are labelled zero and one. Positivity is ContinuousLinearMap.IsPositive.",
                AssessedProvenance.FromLiterature(Source)),
            Node("parent", "A parent with all binary-string marginals", "HasParent", ParentFormula(),
                "The parent assigns a positive effect to every function from Fin m to Fin 2, and the effects sum to the identity. For each setting j and outcome b, sum over all strings whose j-th outcome is b. Equality with F(j,b) is the joint-measurability condition of Result 2 and Eq. (3). No outcome string is omitted.",
                AssessedProvenance.FromLiterature(Source)),
            Node("inverse-transmissivity", "The admissible reciprocal transmissivity",
                "inverseTransmissivity", InverseTransmissivityFormula(),
                "For n at least one, the reciprocal real value belongs to the closed unit interval. The parameter hn expresses this lower bound on n.",
                AssessedProvenance.FromRepo()),
            Node("claim", "Incompatibility at reciprocal integer transmissivity", "claim",
                ClaimFormula(),
                "Result 3 asserts the existence of n+1 measurements that remain incompatible at transmissivity 1/n. Their dual images exist by the defining trace relation. Every family satisfying that relation has no parent with the displayed marginals. Every natural n at least one is included, also n=1.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("pure-loss-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Incompatible binary measurements for every n"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The reduced pure output is the sum of the rank-one operators of its "
                            + "environment slices. Their squared norms are summable. "
                            + "Cauchy-Schwarz and the operator norm bound make the double "
                            + "Fock-basis and environment sum absolutely summable. Interchanging "
                            + "the sums and applying Parseval identifies its trace with the "
                            + "quadratic form of dualLoss. Uniqueness of the sum and complex "
                            + "polarization identify every operator satisfying IsLossDual "
                            + "with this pullback.")),
                    Paragraph(Text(
                        "Use the coherent-state projectors of Eq. (4) and their complements. "
                            + "For m distinct unit phases z_j and a transmissivity tau with "
                            + "m tau > 1, set Delta = m tau - 1, "
                            + "Q = sum over i<j of 1/|z_i-z_j|^2, and "
                            + "x = Delta/(2(m + 4Q)). The coherent amplitudes are sqrt(x) z_j.")),
                    Paragraph(Text(
                        "Restrict the dual click effects to the span of |0> and |1>. "
                            + "Their matrices have diagonal entries a = 1-exp(-x) and "
                            + "c = 1-exp(-x)(1-tau+tau x), with off-diagonal entries "
                            + "-b conjugate(z_j) and -b z_j, where "
                            + "b = sqrt(tau) exp(-x) sqrt(x). The scalar bounds "
                            + "c-b^2/a <= x and c >= tau-x control these matrices. "
                            + "Any full-space parent would induce a parent of these effects.")),
                    Paragraph(Text(
                        "The quadratic-form bound for a common subeffect of settings i and j "
                            + "gives its lower diagonal entry at most 4x/|z_i-z_j|^2. "
                            + "For each parent string let k count its click outcomes. "
                            + "The counting identity for pairs of clicks, together with "
                            + "k <= 1 + binomial(k,2), implies m c <= 1 + 4xQ. "
                            + "The chosen x instead gives m c - 1 - 4xQ >= Delta/2 > 0. "
                            + "Finally take m=n+1, tau=1/n and the regular phases "
                            + "z_j = exp(2 pi i j/(n+1)). They are distinct unit complex numbers, "
                            + "and m tau > 1 for every n at least one, proving the proposition."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mehboudi-rezaeinia-rahimi-keshari-2025-loss-incompatibility"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("pure-loss-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula HFormula() => Equal(Local("H"),
        Qualified("D5", "S3", "Estimation", "TransmissivityBetaPriorProbeRefutation", "FockSpace"));

    private static Formula KFormula() => Equal(Local("K"),
        At(Qualified("lp"), LambdaIgnored(Naturals(), Local("H")), D(2)));

    private static Formula OpFormula() => Equal(Local("Op"),
        At(Qualified("ContinuousLinearMap"), At(Qualified("RingHom", "id"), Complexes()),
            Local("H"), Local("H")));

    private static Formula LossType() =>
        At(Qualified("Set", "Icc"), Typed(D(0), Reals()), D(1));

    private static Formula AmplifyFormula() => All("M", Local("Op"),
        All("w", Local("K"), All("k", Naturals(),
            Equal(At(At(LocalCall("amplify", X("M")), X("w")), X("k")),
                At(X("M"), At(X("w"), X("k")))))));

    private static Formula VacuumEmbeddingFormula() => All("v", Local("H"),
        Equal(LocalCall("vacuumEmbedding", X("v")),
            At(Qualified("lp", "single"), D(2), D(0), X("v"))));

    private static Formula StinespringFormula()
    {
        Formula beamSplitter = At(
            Qualified("D5", "S3", "Quantum", "QuantumChannels", "FockAttenuator",
                "BeamSplitter", "beamSplitter"),
            At(Qualified("Subtype", "val"), X("tau")),
            At(Qualified("Subtype", "property"), X("tau")));
        Formula unitary = At(Qualified("LinearIsometry", "toContinuousLinearMap"),
            At(Qualified("LinearIsometryEquiv", "toLinearIsometry"), beamSplitter));
        return All("tau", LossType(), Equal(LocalCall("stinespring", X("tau")),
            Compose(unitary, Local("vacuumEmbedding"))));
    }

    private static Formula DualLossFormula()
    {
        Formula dilation = LocalCall("stinespring", X("tau"));
        Formula adjoint = At(Qualified("ContinuousLinearMap", "adjoint"), dilation);
        return All("tau", LossType(), All("M", Local("Op"),
            Equal(LocalCall("dualLoss", X("tau"), X("M")),
                Compose(adjoint, Compose(LocalCall("amplify", X("M")), dilation)))));
    }

    private static Formula BinaryPOVMFormula() => All("M", Arrow(FinOf(D(2)), Local("Op")),
        Equivalence(LocalCall("IsBinaryPOVM", X("M")), And(
            All("b", FinOf(D(2)), Positive(At(X("M"), X("b")))),
            Equal(Add(At(X("M"), D(0)), At(X("M"), D(1))),
                Typed(D(1), Local("Op"))))));

    private static Formula IsLossDualFormula()
    {
        Formula E(Formula n) => At(Qualified("D5", "S3", "Estimation",
            "TransmissivityBetaPriorProbeRefutation", "e"), n);
        Formula beamSplitter = At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
                "FockAttenuator", "BeamSplitter", "beamSplitter"),
            At(Qualified("Subtype", "val"), X("tau")),
            At(Qualified("Subtype", "property"), X("tau")));
        Formula tensor = At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
            "FockAttenuator", "BeamSplitter", "tensor"), X("psi"), E(D(0)));
        Formula output = At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
            "FockAttenuator", "DisplacementCovariance", "purePartialTrace"),
            At(beamSplitter, tensor));
        Formula summand = At(Qualified("inner"), Complexes(), E(X("n")),
            At(Compose(X("M"), output), E(X("n"))));
        Formula value = At(Qualified("inner"), Complexes(), X("psi"), At(X("N"), X("psi")));
        return All("tau", LossType(), All("M", Local("Op"), All("N", Local("Op"),
            Equivalence(LocalCall("IsLossDual", X("tau"), X("M"), X("N")),
                All("psi", Local("H"), At(Qualified("HasSum"),
                    LambdaOf("n", Naturals(), summand), value))))));
    }

    private static Formula ParentFormula()
    {
        Formula outcomes = Outcomes(X("m"));
        Formula positive = All("a", outcomes, Positive(At(X("G"), X("a"))));
        Formula normalized = Equal(SumOver("a", outcomes, At(X("G"), X("a"))),
            Typed(D(1), Local("Op")));
        Formula selected = At(Qualified("Finset", "filter"),
            LambdaOf("a", outcomes, Equal(At(X("a"), X("j")), X("b"))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), outcomes)));
        Formula marginal = All("j", FinOf(X("m")), All("b", FinOf(D(2)),
            Equal(SumIn("a", selected, At(X("G"), X("a"))),
                At(X("F"), X("j"), X("b")))));
        return All("m", Naturals(), All("F", Measurements(X("m")),
            Equivalence(LocalCall("HasParent", X("F")),
                Ex("G", Arrow(outcomes, Local("Op")),
                    And(positive, And(normalized, marginal))))));
    }

    private static Formula InverseTransmissivityFormula() => All("n", Naturals(),
        All("hn", LE(D(1), X("n")),
            Equal(At(Qualified("Subtype", "val"),
                    LocalCall("inverseTransmissivity", X("n"), X("hn"))),
                new Formula.Fraction(D(1), Typed(X("n"), Reals())))));

    private static Formula ClaimFormula()
    {
        Formula settings = Add(X("n"), D(1));
        Formula relations = All("j", FinOf(settings), All("b", FinOf(D(2)),
            LocalCall("IsLossDual", LocalCall("inverseTransmissivity", X("n"), X("hn")),
                At(X("M"), X("j"), X("b")), At(X("N"), X("j"), X("b")))));
        Formula family = And(
            All("j", FinOf(settings), LocalCall("IsBinaryPOVM", At(X("M"), X("j")))),
            And(Ex("N", Measurements(settings), relations),
                All("N", Measurements(settings), new Formula.Logic(Parenthesized(relations),
                    FormulaLogicOperator.Implies,
                    new Formula.Not(Parenthesized(LocalCall("HasParent", X("N"))))))));
        return Equivalence(Local("claim"), All("n", Naturals(),
            All("hn", LE(D(1), X("n")), Ex("M", Measurements(settings), family))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Measurement", "PureLossIncompatibility", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Outcomes(Formula m) => Parenthesized(Arrow(FinOf(m), FinOf(D(2))));
    private static Formula Measurements(Formula m) => Arrow(FinOf(m), Arrow(FinOf(D(2)), Local("Op")));
    private static Formula Compose(Formula left, Formula right) =>
        At(Qualified("ContinuousLinearMap", "comp"), left, right);
    private static Formula Positive(Formula value) =>
        At(Qualified("ContinuousLinearMap", "IsPositive"), value);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LambdaIgnored(Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(new Formula.Placeholder(), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
