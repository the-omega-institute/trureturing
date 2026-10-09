using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QubitWignerDistanceTensorRulesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dutta2026wignerdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Using the compact minimum bridge in WignerDistanceMinimum, equatorial qubit states obey exact multiplicativity of one plus the Wigner distance. Nonpositive Bloch-product states obey self-tensor superadditivity.",
        H("Tensor rules for the qubit Wigner distance"),
        Blocks(
            Definition("bloch", "Pauli expectation coordinates", BlochFormula(),
                "bloch(rho,p) is the real part of tr(rho pauliMatrix(p)). For p = X,Y,Z these are the Bloch coordinates r_x,r_y,r_z. Page 7: \"For a single-qubit state ρ with Bloch vector r⃗, write s(ρ) := sgn(r_x r_y r_z).\" The nonpositive sign condition is exactly r_x r_y r_z ≤ 0."),
            Definition("claimEquatorial", "Conjecture 5.6", Iff(V("claimEquatorial"), EquatorialFormula()),
                "Page 8, Conjecture 5.6 (Equatorial multiplicativity): \"For ⟨Z⟩_ρ = ⟨Z⟩_σ = 0: C(ρ ⊗ σ) = C(ρ) + C(σ) + C(ρ)C(σ).\" The quantifiers range over every complex two-by-two density matrix rho and sigma. IsDensity means positive semidefinite with trace one; the two Z expectations vanish separately. COne and CTwo denote WignerDistanceMinimum.COne and WignerDistanceMinimum.CTwo; COne_min and CTwo_min identify them with the source minimum on the corresponding Hilbert spaces."),
            Definition("claimSelfTensor", "Conjecture 5.7", Iff(V("claimSelfTensor"), SelfFormula()),
                "Page 8, Conjecture 5.7 (Self-tensor superadditivity, s ≤ 0 branch): \"For any qubit state ρ with s(ρ)≤ 0: C(ρ ⊗ ρ) ≥ 2C(ρ).\" Every density matrix is included, with the sign condition encoded by bloch(rho,X) bloch(rho,Y) bloch(rho,Z) ≤ 0. This includes zero coordinates and the stabilizer boundary."),
            Shared("Enumeration.Word", "Two-qubit Pauli labels", Equal(V("Word"), Pair(Fin(4), Fin(4))), DescribeRole.Definition,
                "A word records two Pauli labels, with 0,1,2,3 denoting I,X,Y,Z."),
            Shared("Enumeration.commutingIndependent", "Independent commuting words", IndependentFormula(), DescribeRole.Definition,
                "Both words are nonidentity and distinct. The sum of their local multiplication phases is even, which is exactly commutation."),
            Shared("Enumeration.candidate", "Rational stabilizer Wigner coordinates", CandidateFormula(), DescribeRole.Definition,
                "The signs select the two generator eigenvalues. character gives the phase-point Pauli character; phaseProduct and labelProduct give the phase and label of Pauli multiplication."),
            Shared("Enumeration.candidates", "The finite stabilizer Wigner set", CandidatesFormula(), DescribeRole.Definition,
                "The image contains the rational Wigner vectors of all independent commuting words with both binary eigenvalue signs. Finset enumeration removes repetitions."),
            Shared("Enumeration.projector", "Two-generator spectral projector", ProjectorFormula(), DescribeRole.Definition,
                "word(u) is the tensor product of the Pauli matrices labelled by u. The projector averages the identity, the two signed generators, and their product."),
            Shared("stabilizer_two_generators", "Two-qubit stabilizer generators", GeneratorsFormula(), DescribeRole.Theorem,
                "Every subgroup-defined two-qubit stabilizer projector has two independent commuting Pauli generators and binary signs."),
            Shared("projector_wigner", "Projector coordinates in the finite set", ProjectorWignerFormula(), DescribeRole.Theorem,
                "For independent commuting words, the complex projector has exactly the real casts of the rational candidate coordinates."),
            Shared("candidate_mem", "Candidate membership", WordSigns(Imp(Call("commutingIndependent", V("u"), V("v")),
                Rel(Call("candidate", V("u"), V("v"), V("epsilon"), V("delta")), FormulaRelationOperator.MemberOf, V("candidates")))), DescribeRole.Theorem,
                "Every independent commuting pair and binary sign choice gives an element of the finite candidate set."),
            Shared("stabilizer_one_classification", "One-qubit stabilizer classification", ClassificationFormula(), DescribeRole.Theorem,
                "A one-qubit stabilizer projector is a spectral projector of X, Y, or Z with either eigenvalue sign."),
            Shared("distance_one_nonpositive", "Attaining distance on the nonpositive branch", NonpositiveFormula(), DescribeRole.Theorem,
                "For a density matrix with nonpositive Bloch product, a free Wigner vector of L1 norm one attains the error equal to the state Wigner L1 norm minus one."),
            Theorem("resultEquatorial", "Equatorial multiplicativity holds", V("claimEquatorial"),
                "Every qubit Wigner vector has at most one negative coordinate. On the nonpositive Bloch-product branch an explicit stabilizer-edge mixture has error ‖W‖₁−1. A product sign functional is bounded by one on every actual two-qubit stabilizer, using subgroup generators and an exact rational certificate on sixty candidate vectors. Convex weak duality gives the lower bound ‖W_rho‖₁ ‖W_sigma‖₁−1. The product of the two nearest mixtures gives the matching upper bound. Equatorial states lie on the zero Bloch-product branch."),
            Theorem("resultSelfTensor", "Self-tensor superadditivity holds", V("claimSelfTensor"),
                "On the nonpositive branch COne(rho) = ‖W_rho‖₁−1. Applying the same product dual bound to two copies of rho gives at least (1+COne(rho))²−1, which is at least 2 COne(rho). The free tensor mixture establishes nonemptiness of the two-qubit free set."))));

    private static DocumentBlock Shared(string name, string title, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("dutta-shared-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Pair(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula PairValue(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Pt() => V("PhasePoint");
    private static Formula Points() => Pair(Pt(), Pt());
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ExistsOne(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula NotEqual(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Fr(byte a, byte b) => new Formula.Fraction(D(a), D(b));
    private static Formula Fst(Formula a) => Call("fst", a);
    private static Formula Snd(Formula a) => Call("snd", a);
    private static Formula Sign(Formula a) => new Formula.Power(Parenthesized(Subtract(D(0), D(1))), Call("val", a));
    private static Formula Words(Formula body) => All("u", V("Word"), All("v", V("Word"), body));
    private static Formula WordSigns(Formula body) => Words(All("epsilon", Fin(2), All("delta", Fin(2), body)));
    private static Formula PhaseSum() => Add(Call("phaseProduct", Fst(V("u")), Fst(V("v"))),
        Call("phaseProduct", Snd(V("u")), Snd(V("v"))));
    private static Formula IndependentFormula() => Words(Iff(Call("commutingIndependent", V("u"), V("v")),
        And(NotEqual(V("u"), PairValue(D(0), D(0))), And(NotEqual(V("v"), PairValue(D(0), D(0))),
            And(NotEqual(V("u"), V("v")), Equal(Call("mod", PhaseSum(), D(2)), D(0)))))));
    private static Formula Char(Formula label, Formula point) => Call("character", label, point);
    private static Formula CandidateFormula()
    {
        var a = V("a"); var u = V("u"); var v = V("v");
        var e = V("epsilon"); var d = V("delta");
        var first = Multiply(Multiply(Sign(e), Char(Fst(u), Fst(a))), Char(Snd(u), Snd(a)));
        var second = Multiply(Multiply(Sign(d), Char(Fst(v), Fst(a))), Char(Snd(v), Snd(a)));
        var third = Multiply(Multiply(Multiply(new Formula.Power(Parenthesized(Subtract(D(0), D(1))),
                Add(Call("val", e), Call("val", d))),
            Call("ite", Equal(Call("mod", PhaseSum(), D(4)), D(0)), D(1), Subtract(D(0), D(1)))),
            Char(Call("labelProduct", Fst(u), Fst(v)), Fst(a))),
            Char(Call("labelProduct", Snd(u), Snd(v)), Snd(a)));
        return WordSigns(All("a", Points(), Equal(Call("candidate", u, v, e, d, a),
            new Formula.Fraction(Parenthesized(Add(Add(Add(D(1), first), second), third)), D(1,6)))));
    }
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Lambda, Sp, Open, V(name), Colon, type, Close, Sp, Mapsto, Sp, body);
    private static Formula CandidatesFormula()
    {
        var k = V("k"); var type = Pair(Pair(V("Word"), V("Word")), Pair(Fin(2), Fin(2)));
        var pred = LambdaOf("k", type, Call("commutingIndependent", Fst(Fst(k)), Snd(Fst(k))));
        var value = LambdaOf("k", type, Call("candidate", Fst(Fst(k)), Snd(Fst(k)), Fst(Snd(k)), Snd(Snd(k))));
        return Equal(V("candidates"), Call("Finsetimage", value, Call("Finsetfilter", pred, Call("Finsetuniv", type))));
    }
    private static Formula ProjectorFormula()
    {
        var p = Call("smul", Sign(V("epsilon")), Call("word", V("u")));
        var q = Call("smul", Sign(V("delta")), Call("word", V("v")));
        return WordSigns(Equal(Call("projector", V("u"), V("v"), V("epsilon"), V("delta")),
            Call("smul", Fr(1,4), Parenthesized(Add(Add(Add(D(1), p), q), Multiply(p,q))))));
    }
    private static Formula GeneratorsFormula() => All("rho", V("TwoQubitMatrix"),
        Imp(Rel(V("rho"), FormulaRelationOperator.MemberOf, Call("Stab", V("pauliTwo"))),
            ExistsOne("u", V("Word"), ExistsOne("v", V("Word"), ExistsOne("epsilon", Fin(2), ExistsOne("delta", Fin(2),
                And(Call("commutingIndependent", V("u"), V("v")), Equal(V("rho"),
                    Call("projector", V("u"), V("v"), V("epsilon"), V("delta"))))))))));
    private static Formula ProjectorWignerFormula() => WordSigns(Imp(Call("commutingIndependent", V("u"), V("v")),
        Equal(Call("WignerTwo", Call("projector", V("u"), V("v"), V("epsilon"), V("delta"))),
            LambdaOf("a", Points(), Call("realCast", Call("candidate", V("u"), V("v"), V("epsilon"), V("delta"), V("a")))))));
    private static Formula ClassificationFormula() => All("rho", Qubit(),
        Imp(Rel(V("rho"), FormulaRelationOperator.MemberOf, Call("Stab", V("pauliSet"))),
            ExistsOne("p", V("Pauli"), ExistsOne("epsilon", Fin(2), And(NotEqual(V("p"), V("I")),
                Equal(V("rho"), Call("smul", Fr(1,2), Parenthesized(Add(D(1),
                    Call("smul", Sign(V("epsilon")), Call("pauliMatrix", V("p"))))))))))));
    private static Formula LOne(Formula x) => Call("norm", Call("toLp", D(1), x));
    private static Formula NonpositiveFormula()
    {
        var rho = V("rho"); var f = V("f"); var w = Call("WignerOne", rho);
        var product = Multiply(Multiply(Call("bloch", rho, V("X")), Call("bloch", rho, V("Y"))), Call("bloch", rho, V("Z")));
        return All("rho", Qubit(), Imp(Call("IsDensity", rho), Imp(Rel(product, FormulaRelationOperator.LessThanOrEqual, D(0)),
            ExistsOne("f", Arrow(Pt(), Real()), And(Rel(f, FormulaRelationOperator.MemberOf, Call("Wfree", V("phasePoint"), V("pauliSet"))),
                And(Equal(LOne(f), D(1)), And(Equal(LOne(Subtract(w,f)), Subtract(LOne(w), D(1))),
                    Equal(C(rho), Subtract(LOne(w), D(1))))))))));
    }

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create(name == "resultEquatorial"
                ? "dutta-tushar-2026-wigner-distance-equatorial-multiplicativity"
                : "dutta-tushar-2026-wigner-distance-self-tensor-superadditivity"), ResolutionKind.Proved));

    private static string NodeId(string name) => name switch
    {
        "PhasePoint" => "dutta-phase-carrier", "phasePoint" => "dutta-phase-operator",
        "phasePointTwo" => "dutta-product-frame", "Wigner" => "dutta-transform",
        "WignerOne" => "dutta-one-transform", "WignerTwo" => "dutta-two-transform",
        "pauliTwo" => "dutta-two-paulis",
        "Stab" => "dutta-stabilizers", "Wfree" => "dutta-free-polytope",
        "COne" => "dutta-one-distance", "CTwo" => "dutta-two-distance",
        "bloch" => "dutta-bloch", "claimEquatorial" => "dutta-equatorial-claim",
        "claimSelfTensor" => "dutta-self-claim", "resultEquatorial" => "dutta-equatorial-result",
        _ => "dutta-self-result"
    };
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Qubit() => V("QubitMatrix");
    private static Formula Tensor(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula TrRe(Formula m) => Call("re", Call("trace", m));
    private static Formula Pauli(string p) => V(p);
    private static Formula BlochFormula() => All("rho", Qubit(), All("p", V("Pauli"),
        Equal(Call("bloch", V("rho"), V("p")), TrRe(Multiply(V("rho"), Call("pauliMatrix", V("p")))))));
    private static Formula C(Formula rho) => Call("COne", rho);
    private static Formula EquatorialFormula()
    {
        var rho = V("rho"); var sigma = V("sigma");
        var conclusion = Equal(Call("CTwo", Tensor(rho, sigma)), Add(Add(C(rho), C(sigma)), Multiply(C(rho), C(sigma))));
        return All("rho", Qubit(), All("sigma", Qubit(), Imp(Call("IsDensity", rho), Imp(Call("IsDensity", sigma),
            Imp(Equal(Call("bloch", rho, Pauli("Z")), D(0)), Imp(Equal(Call("bloch", sigma, Pauli("Z")), D(0)), conclusion))))));
    }
    private static Formula SelfFormula()
    {
        var rho = V("rho");
        var product = Multiply(Multiply(Call("bloch", rho, Pauli("X")), Call("bloch", rho, Pauli("Y"))), Call("bloch", rho, Pauli("Z")));
        return All("rho", Qubit(), Imp(Call("IsDensity", rho), Imp(Rel(product, FormulaRelationOperator.LessThanOrEqual, D(0)),
            Rel(Call("CTwo", Tensor(rho, rho)), FormulaRelationOperator.GreaterThanOrEqual, Multiply(D(2), C(rho))))));
    }
}
