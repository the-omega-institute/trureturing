using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class GTestThresholdPriorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/GTestThresholdPrior.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/buhrmangrinkoverduynlunelweggemans2026permutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The G-test has larger Bayesian success probability than the always-unequal test exactly above the prior O/(M+O), where M counts words in a symmetric-group orbit and O counts its G-orbits.",
        H("The threshold prior of the G-test"),
        Blocks(
            Node("tensor-vec", "Vectors indexed by words", "TensorVec", TensorVecFormula(),
                "The tensor coordinates in Section 4.1.1 are words of length n on the alphabet Fin d. A vector assigns a complex amplitude to each word."),
            Node("tensor-mat", "Matrices indexed by words", "TensorMat", TensorMatFormula(),
                "Operators on the tensor coordinates have a row and a column for each word."),
            Node("word-orbit", "Words with the same multiplicities", "WordOrbit", WordOrbitFormula(),
                "The symmetric group permutes positions. Its orbit consists of the words with the same symbol multiplicities as w, corresponding to the multiplicity sector of Eqs. (11) and (12)."),
            Node("orbit-map", "The map from permutations to words", "orbitMap", OrbitMapFormula(),
                "A permutation is sent to its action on w, regarded as an element of the orbit. The position action uses the inverse permutation on coordinates."),
            Node("word-count", "The number of words in the sector", "M", WordCountFormula(),
                "This finite cardinality is the multinomial coefficient of the multiplicities in w."),
            Node("orbit-count", "The number of subgroup orbits", "O", OrbitCountFormula(),
                "Restricting the position action to G partitions the same word sector into G-orbits. The quotient counts those orbits."),
            Node("psi", "The permutation representation", "psi", PsiFormula(),
                "The position action induces a permutation of the word basis. Matrix.permMatrixHom turns that permutation into its matrix, as in the representation used in Eqs. (12) and (62)."),
            Node("ket", "A word basis vector", "ket", KetFormula(),
                "The ket has amplitude one at w and zero at every other word, as for the basis vector in Eq. (11)."),
            Node("tensor-power", "The common tensor power", "tensorPower", TensorPowerFormula(),
                "The same local matrix acts at each of the n positions. This is the tensor power in Eqs. (11) and (13)."),
            Node("repeat-ket", "A repeated pure vector", "repeatKet", RepeatKetFormula(),
                "The amplitude at a word is the product of its n single-particle amplitudes. Empty products have value one."),
            Node("equal-state", "The equal-input pure state", "equalState", EqualStateFormula(),
                "The rank-one matrix of the repeated vector is a pure equal-input state, before the Haar average in Eq. (13)."),
            Node("pi-g", "The subgroup average", "PiG", PiGFormula(),
                "Equations (61) and (62) use the average of the permutation matrices over G as the equal-outcome operator. Finset.expect is the finite average over the full subgroup."),
            Node("rho-tilde", "The permuted unequal-input state", "rhoTilde", RhoTildeFormula(),
                "For a fixed unitary U, Eq. (12) averages the conjugates of the word state after the common tensor unitary. The Haar average in Eq. (11) is taken only after these fixed-unitary states are formed."),
            Node("completeness", "Acceptance of equal inputs", "completeness", CompletenessFormula(),
                "The real trace of the equal-outcome operator against the equal-input state is the completeness probability of Eq. (63), for a normalized vector."),
            Node("soundness-error", "Acceptance of unequal inputs", "soundnessError", SoundnessErrorFormula(),
                "The real trace against the permuted unequal-input state is the soundness error appearing in Eqs. (64) and (65)."),
            Node("soundness", "Rejection of unequal inputs", "soundness", SoundnessFormula(),
                "UnifiedPinchingFee.doorGap subtracts the soundness error from one, giving the soundness probability of Eq. (65)."),
            Node("g-success", "Bayesian success of the G-test", "P_G", SuccessFormula(),
                "The prior p weights equal inputs. AffineMap.lineMap interpolates from soundness at p = 0 to completeness at p = 1, as in the Bayesian comparison of Section 4.1."),
            Node("trivial-success", "Bayesian success of the always-unequal test", "P_T", TrivialSuccessFormula(),
                "The test that always reports unequal succeeds with probability one minus the equal-input prior, as in Theorem 5."),
            Node("claim", "The exact threshold and trace identity", "claim", ClaimFormula(),
                "Section 6 asks for the prior below which the trivial test outperforms the G-test. For a nonconstant word, a normalized equal-input vector and p in Set.Icc 0 1, the threshold is O/(M+O), with equality exactly at that prior. The Haar integral of Eq. (11) is replaced by every fixed unitary because the traces tested do not depend on U. The comparison is between these two tests.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("g-test-threshold-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The orbit ratio determines the threshold"),
                StatementSource.FromAuthor(Disp(Q("claim"))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "On a word, the diagonal of PiG is the stabilizer cardinality divided by the subgroup cardinality. Commutation with the common tensor unitary removes U from the tested trace. The symmetric-group average is uniform on the word orbit; Burnside's lemma makes the sum of stabilizer cardinalities over the word orbit equal to O times the subgroup cardinality, giving trace O/M. A repeated normalized vector is fixed by every position permutation, so completeness is one. Substitution into the Bayesian success probability reduces the strict comparison and the equality comparison to linear inequalities and identities in p, with threshold O/(M+O)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("buhrman-grinko-verduyn-lunel-weggemans-2026-g-test-threshold-prior"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("g-test-threshold-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NamedArg(string name, Formula value) => Parenthesized(Seq(X(name), Sp, Colon, Eq, Sp, value));
    private static Formula Numbers(string name) => Seq(Mathbb, Grp(X(name)));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(
        LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula Constant(Formula type, Formula value) => App(Q("Function", "const"), type, value);
    private static Formula EqualTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Different(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Greater(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesThat(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula EquivalentTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula DividedBy(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word() => App(Q("OccupancyWordSectors", "Word"), Fin(X("d")), X("n"));
    private static Formula Perm() => App(Q("Equiv", "Perm"), Fin(X("n")));
    private static Formula Group() => Call("Subgroup", Perm());
    private static Formula Mat(Formula index) => Call("Matrix", index, index, Numbers("C"));
    private static Formula LocalMatrix() => Mat(Fin(X("d")));
    private static Formula Unitary() => App(Q("Matrix", "unitaryGroup"), Fin(X("d")), Numbers("C"));
    private static Formula NaturalParameters(Formula body) => All("n", Numbers("N"), All("d", Numbers("N"), body));
    private static Formula WordParameters(Formula body) => NaturalParameters(All("w", Word(), body));
    private static Formula TestParameters(Formula body) => NaturalParameters(All("G", Group(), All("w", Word(), All("U", Unitary(), body))));
    private static Formula Orbit() => App(Q("MulAction", "orbit"), Perm(), X("w"));
    private static Formula Act(Formula g, Formula x) => App(Q("SMul", "smul"), g, x);
    private static Formula Adjoint(Formula a) => App(Q("Matrix", "conjTranspose"), a);
    private static Formula Density(Formula v) => App(Q("PureStateHandshake", "rankOneDensity"), v);
    private static Formula Tensor(Formula a) => Call("tensorPower", X("n"), a);
    private static Formula Product(Formula domain, Formula factors) => App(Q("ProductPrefixRigidity", "productMap"), domain, factors);
    private static Formula PsiAt(Formula permutation) => App(Q("psi"), NamedArg("d", X("d")), permutation);
    private static Formula Expect(Formula function) => App(Q("Finset", "expect"), Q("Finset", "univ"), function);
    private static Formula PG() => new Formula.Subscript(Q("P"), X("G"));
    private static Formula PT() => new Formula.Subscript(Q("P"), X("T"));

    private static Formula TensorVecFormula() => NaturalParameters(EqualTo(Call("TensorVec", X("n"), X("d")), Arrow(Word(), Numbers("C"))));
    private static Formula TensorMatFormula() => NaturalParameters(EqualTo(Call("TensorMat", X("n"), X("d")), Mat(Word())));
    private static Formula WordOrbitFormula() => WordParameters(EqualTo(Call("WordOrbit", X("w")),
        Call("Subtype", Lambda("x", Word(), Member(X("x"), Orbit())))));
    private static Formula OrbitMapFormula() => WordParameters(All("pi", Perm(), EqualTo(Call("orbitMap", X("w"), X("pi")),
        App(Q("Set", "rangeFactorization"), Lambda("sigma", Perm(), Act(X("sigma"), X("w"))), X("pi")))));
    private static Formula WordCountFormula() => WordParameters(EqualTo(Call("M", X("w")), App(Q("Fintype", "card"), Call("WordOrbit", X("w")))));
    private static Formula OrbitCountFormula() => NaturalParameters(All("G", Group(), All("w", Word(), EqualTo(Call("O", X("G"), X("w")),
        App(Q("Fintype", "card"), App(Q("MulAction", "orbitRel", "Quotient"), X("G"), Call("WordOrbit", X("w"))))))));

    private static Formula PsiFormula()
    {
        var type = Parenthesized(Seq(Perm(), Sp, new Formula.Power(To, Star), Sp, Call("TensorMat", X("n"), X("d"))));
        var matrices = App(Q("Matrix", "permMatrixHom"), NamedArg("n", Word()), NamedArg("R", Numbers("C")));
        var permutations = App(Q("MulAction", "toPermHom"), Perm(), Word());
        return NaturalParameters(EqualTo(Typed(Q("psi"), type), App(Q("MonoidHom", "comp"), matrices, permutations)));
    }

    private static Formula KetFormula() => WordParameters(EqualTo(Call("ket", X("w")), App(Q("Pi", "single"), X("w"), D(1))));
    private static Formula TensorPowerFormula() => NaturalParameters(All("A", LocalMatrix(), EqualTo(Tensor(X("A")),
        Product(Constant(Fin(X("n")), Fin(X("d"))), Constant(Fin(X("n")), X("A"))))));
    private static Formula RepeatKetFormula()
    {
        var factors = Constant(Fin(X("n")), Lambda("a", Fin(X("d")), Constant(Q("Unit"), App(X("phi"), X("a")))));
        var entry = App(Product(Constant(Fin(X("n")), Q("Unit")), factors), X("x"), Constant(Fin(X("n")), Q("Unit", "unit")));
        return NaturalParameters(All("phi", Arrow(Fin(X("d")), Numbers("C")), EqualTo(Call("repeatKet", X("n"), X("phi")), Lambda("x", Word(), entry))));
    }
    private static Formula EqualStateFormula() => NaturalParameters(All("phi", Arrow(Fin(X("d")), Numbers("C")),
        EqualTo(Call("equalState", X("n"), X("phi")), Density(Call("repeatKet", X("n"), X("phi"))))));
    private static Formula PiGFormula() => NaturalParameters(All("G", Group(), EqualTo(Call("PiG", X("G")),
        Expect(Lambda("g", X("G"), PsiAt(Typed(X("g"), Perm())))))));
    private static Formula RhoTildeFormula()
    {
        var conjugate = TimesOf(TimesOf(X("T"), Density(Call("ket", X("w")))), Adjoint(X("T")));
        var summand = TimesOf(TimesOf(PsiAt(X("pi")), Parenthesized(conjugate)), PsiAt(new Formula.Power(X("pi"), new Formula.Negate(D(1)))));
        var body = Seq(X("let"), Sp, X("T"), Sp, Colon, Eq, Sp, Tensor(Typed(X("U"), LocalMatrix())), Semi, Sp,
            Expect(Lambda("pi", Perm(), summand)));
        return WordParameters(All("U", Unitary(), EqualTo(Call("rhoTilde", X("w"), X("U")), body)));
    }
    private static Formula CompletenessFormula() => NaturalParameters(All("G", Group(), All("phi", Arrow(Fin(X("d")), Numbers("C")),
        EqualTo(Call("completeness", X("G"), X("phi")), App(Q("RHLinalg", "rtrace"), TimesOf(Call("PiG", X("G")), Call("equalState", X("n"), X("phi"))))))));
    private static Formula SoundnessErrorFormula() => TestParameters(EqualTo(Call("soundnessError", X("G"), X("w"), X("U")),
        App(Q("RHLinalg", "rtrace"), TimesOf(Call("PiG", X("G")), Call("rhoTilde", X("w"), X("U"))))));
    private static Formula SoundnessFormula() => TestParameters(EqualTo(Call("soundness", X("G"), X("w"), X("U")),
        App(Q("UnifiedPinchingFee", "doorGap"), Call("soundnessError", X("G"), X("w"), X("U")))));
    private static Formula SuccessFormula() => TestParameters(All("phi", Arrow(Fin(X("d")), Numbers("C")), All("p", Numbers("R"),
        EqualTo(App(PG(), X("G"), X("w"), X("U"), X("phi"), X("p")),
            App(Q("AffineMap", "lineMap"), Call("soundness", X("G"), X("w"), X("U")), Call("completeness", X("G"), X("phi")), X("p"))))));
    private static Formula TrivialSuccessFormula() => All("p", Numbers("R"), EqualTo(App(PT(), X("p")), App(Q("UnifiedPinchingFee", "doorGap"), X("p"))));

    private static Formula ClaimFormula()
    {
        var nonconstant = Some("i", Fin(X("n")), Some("j", Fin(X("n")), Different(App(X("w"), X("i")), App(X("w"), X("j")))));
        var normalized = EqualTo(Call("dotProduct", Call("star", X("phi")), X("phi")), Typed(D(1), Numbers("C")));
        var prior = Member(X("p"), App(Q("Set", "Icc"), Typed(D(0), Numbers("R")), D(1)));
        var orbitReal = Typed(Call("O", X("G"), X("w")), Numbers("R"));
        var wordsReal = Typed(Call("M", X("w")), Numbers("R"));
        var threshold = DividedBy(orbitReal, PlusOf(wordsReal, orbitReal));
        var success = App(PG(), X("G"), X("w"), X("U"), X("phi"), X("p"));
        var trivial = App(PT(), X("p"));
        var comparison = And(EquivalentTo(Greater(success, trivial), Greater(X("p"), threshold)),
            EquivalentTo(EqualTo(success, trivial), EqualTo(X("p"), threshold)));
        var trace = EqualTo(App(Q("Matrix", "trace"), TimesOf(Call("PiG", X("G")), Call("rhoTilde", X("w"), X("U")))),
            DividedBy(Typed(Call("O", X("G"), X("w")), Numbers("C")), Typed(Call("M", X("w")), Numbers("C"))));
        var body = TestParameters(All("phi", Arrow(Fin(X("d")), Numbers("C")), All("p", Numbers("R"),
            ImpliesThat(nonconstant, ImpliesThat(normalized, ImpliesThat(prior, And(comparison, trace)))))));
        return EquivalentTo(Q("claim"), body);
    }
}
