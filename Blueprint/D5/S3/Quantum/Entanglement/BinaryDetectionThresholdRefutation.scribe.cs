using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class BinaryDetectionThresholdRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/cope2021binarydetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Section 4.3 conjecture eta* = 4/(m+4) is refuted at m = 13 by a three-input leader model and a universal local extension at efficiency 6/25.",
        H("Refuting the binary detection threshold conjecture"),
        Blocks(
            Node("parity-box", "The binary parity distribution", ParityBoxFormula(),
                "At each input pair the parity box gives probability one half exactly to the two Boolean output pairs whose xor is the prescribed bit.",
                "parityBox", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("binary-eq", "A binary table is determined by its marginals and one entry", BinaryEqualityFormula(),
                "Two real two-by-two tables agree when their total masses, one selected row sum, one selected column sum and the selected corner entry agree.",
                "binary_eq", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("isns", "No-signalling box", IsNSFormula(), "Cope, Section 2, arXiv v3 p. 2: “However, we do assume that Alice and Bob can isolate their systems, also referred to here as devices, from communicating with each other.” Inputs are Fin m and outputs are Bool; the formula also records nonnegativity and normalization.", "IsNSBox", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lossy", "Lossy extension", LossyFormula(), "Cope, Section 2, arXiv v3 p. 2: “The model considered here adds an extra output to both parties to alter the original distribution p(ab|xy) in the following way:” The four branches are equation (3), with none denoting F.", "lossy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("local", "Local box", IsLocalFormula(), "Cope, Section 2, arXiv v3 p. 2: “These distributions may always be expressed as convex combinations of deterministic distributions p(ab|xy)=δₐ,ₐₓδᵦ,ᵦᵧ, which are finite in number.” The finite weights run over pairs of deterministic Option Bool response functions.", "IsLocal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eta", "Detection threshold", EtaFormula(), "Cope, Section 2, arXiv v3 p. 3: “We will refer to η∗ as the no-signalling threshold.” etaStar is the supremum of efficiencies in [0,1] for which every no-signalling box has a local lossy extension.", "etaStar", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Section 4.3 conjecture", ClaimFormula(), "Cope, Section 4.3, arXiv v3 p. 6: “In order to prove that our conjecture of η∗=4/(m+4) for mₐ=mᵦ=m is correct, one would need to provide a extremal NS distribution pᴺˢ, and corresponding Bell inequality sᵡʸₐ′ᵦ′, such that ∑ₐ′,ᵦ′,ₓ,ᵧ sᵡʸₐ′ᵦ′ pᴺˢη(a′b′|xy) ≰ k, ∀ η > η∗.” The Lean claim encodes the conjectured equality for every natural m at least 2; inputs are Fin m and outputs are Bool, with none denoting failure.", "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("cope-refutation-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture is false"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("At m = 13, the counting identity and universal extension prove 6/25 <= etaStar 13, contradicting etaStar 13 = 4/17.")),
                    Paragraph(Text("The response indicators use FiberwiseEqualDistanceLift.labelKernel on paired outputs. The finite output maps use CycleSingleCutMinimax.push on the product outcome space, and the two marginal tables use ChainRule.marginal with swapped coordinates for Bob. The independent parity-bit weights use GreenClassWindowEntropy.windowLaw with complemented ScoreBridge.bernoulliMass bits.")),
                    Paragraph(Text("A deterministic response atom is the product of the two response indicators. Any finite family of such atoms with nonnegative weights summing to one defines a local box: summing weights over equal response functions gives the weights in IsLocal.")),
                    Paragraph(Text("For each matrix G : Fin 13 -> Fin 13 -> Bool, the parity box assigns one half exactly when Bool.xor a b = G x y. The leader model includes the all-failure atom with weight (13-12)^2/25^2 = 1/625. Each ordered triple of distinct inputs, each triple of leader bits and each of the two leader orientations has weight (48*13/25^2)/(2*13*12*11*8).")),
                    Paragraph(Text("On the ordered triple i,j,k the leader returns ri,rj,rk respectively and fails on every other input. A follower at y returns the common value of Bool.xor ri (G i y), Bool.xor rj (G j y), Bool.xor rk (G k y) when all three agree, and fails otherwise. The opposite orientation transposes G and exchanges the parties. Exactly two of the eight leader bit patterns agree.")),
                    Paragraph(Text("The model is the sum of these weighted deterministic response indicators and the all-failure atom. There are 1716 ordered distinct triples; for a fixed input 396 contain it and 1320 miss it. The two orientations give joint entries 18/625 on the prescribed parity and zero on the other parity, each single-failure entry 57/625, and the double-failure entry 361/625. Thus the model equals lossy (6/25) of the parity box for every G, and that lossy parity box is local.")),
                    Paragraph(Text("The active leader part has total weight 624/625. Its joint conclusive probability is c = 3/52 and each party's single conclusive probability is d = 25/104, so the calibrated efficiency is c/d = 6/25. Optimizing raw joint success alone does not optimize this ratio.")),
                    Paragraph(Text("Every binary no-signalling box is reconstructed as a finite mixture of locally mapped parity boxes. A common uniform threshold selects active inputs and gives pair activation probabilities equal to the minimum of their activation parameters. Independent parity bits then match each minor-output joint mass; normalization and the two marginals determine the other three entries. Local output maps preserve locality and commute with lossy, and normalized mixtures preserve both identities. This extends the leader model to every IsNSBox at m = 13."))
                ), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("cope-2021-binary-detection-threshold"), ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("cope-refutation-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ParityBoxFormula()
    {
        Formula g = F.Id("G"), x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula parity = new Formula.Apply(Qualified("Bool", "xor"), [a, b]);
        return All("G", ArrowMany(Fin(N(13)), Fin(N(13)), Bool()),
            All("x", Fin(N(13)), All("y", Fin(N(13)), All("a", Bool(), All("b", Bool(),
                Eq(Call("parityBox", g, x, y, a, b), Ite(Eq(parity, new Formula.Apply(g, [x, y])),
                    new Formula.Fraction(N(1), N(2)), N(0))))))));
    }

    private static Formula BinaryEqualityFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g"), ma = F.Id("ma"), mb = F.Id("mb");
        Formula a = F.Id("a"), b = F.Id("b");
        Formula Total(Formula table) => FiniteSum("a", Bool(),
            FiniteSum("b", Bool(), new Formula.Apply(table, [a, b])));
        Formula Row(Formula table) => FiniteSum("b", Bool(), new Formula.Apply(table, [ma, b]));
        Formula Column(Formula table) => FiniteSum("a", Bool(), new Formula.Apply(table, [a, mb]));
        Formula corner = Eq(new Formula.Apply(f, [ma, mb]), new Formula.Apply(g, [ma, mb]));
        Formula body = Imp(Eq(Total(f), Total(g)), Imp(Eq(Row(f), Row(g)),
            Imp(Eq(Column(f), Column(g)), Imp(corner, Eq(f, g)))));
        return All("f", ArrowMany(Bool(), Bool(), Real()), All("g", ArrowMany(Bool(), Bool(), Real()),
            All("ma", Bool(), All("mb", Bool(), body))));
    }

    private static Formula Q(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Qualified(string owner, string name) => Seq(Q(owner), Dot, Q(name));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : new Formula.Apply(Q(name), [.. args]);

    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula N(byte n) => new Formula.Number(n);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Bool() => Q("Bool");

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula Option(Formula a) => Call("Option", a);

    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula ArrowMany(params Formula[] types)
    {
        Formula result = types[^1];
        for (var i = types.Length - 2; i >= 0; i--)
            result = Arrow(types[i], result);
        return result;
    }

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula FiniteSum(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Sp, InMacro, Sp, domain)), Parenthesized(body));

    private static Formula Ite(Formula c, Formula t, Formula e) => Call("ite", c, t, e);

    private static Formula IsNSFormula()
    {
        Formula m = F.Id("m"), p = F.Id("p"), x = F.Id("x"), y = F.Id("y"),
            yp = F.Id("yPrime"), xp = F.Id("xPrime"), a = F.Id("a"), b = F.Id("b");
        Formula pType = ArrowMany(Fin(m), Fin(m), Bool(), Bool(), Real());
        Formula nonneg = All("x", Fin(m), All("y", Fin(m), All("a", Bool(),
            All("b", Bool(), Le(N(0), Call("p", x, y, a, b))))));
        Formula norm = All("x", Fin(m), All("y", Fin(m), Eq(
            FiniteSum("a", Bool(), FiniteSum("b", Bool(), Call("p", x, y, a, b))), N(1))));
        Formula margA = All("x", Fin(m), All("y", Fin(m), All("yPrime", Fin(m), All("a", Bool(), Eq(
            FiniteSum("b", Bool(), Call("p", x, y, a, b)),
            FiniteSum("b", Bool(), Call("p", x, yp, a, b)))))));
        Formula margB = All("x", Fin(m), All("xPrime", Fin(m), All("y", Fin(m), All("b", Bool(), Eq(
            FiniteSum("a", Bool(), Call("p", x, y, a, b)),
            FiniteSum("a", Bool(), Call("p", xp, y, a, b)))))));
        return Disp(All("m", Nat(), All("p", pType,
            Eq(Call("IsNSBox", p), And(nonneg, And(norm, And(margA, margB)))))));
    }

    private static Formula LossyFormula()
    {
        Formula m = F.Id("m"), eta = F.Id("eta"), p = F.Id("p"), x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula pType = ArrowMany(Fin(m), Fin(m), Bool(), Bool(), Real());
        Formula q = Call("lossy", eta, p, x, y);
        Formula someA = Call("some", a), someB = Call("some", b), none = Call("none");
        Formula detected = All("a", Bool(), All("b", Bool(), Eq(Call("lossy", eta, p, x, y, someA, someB),
            new Formula.Binary(new Formula.Power(Parenthesized(eta), N(2)), FormulaBinaryOperator.Multiply,
                Call("p", x, y, a, b)))));
        Formula oneFail = All("a", Bool(), Eq(Call("lossy", eta, p, x, y, someA, none),
            new Formula.Binary(eta, FormulaBinaryOperator.Multiply,
                new Formula.Binary(new Formula.Binary(N(1), FormulaBinaryOperator.Subtract, eta), FormulaBinaryOperator.Multiply,
                    FiniteSum("b", Bool(), Call("p", x, y, a, b))))));
        Formula otherFail = All("b", Bool(), Eq(Call("lossy", eta, p, x, y, none, someB),
            new Formula.Binary(eta, FormulaBinaryOperator.Multiply,
                new Formula.Binary(new Formula.Binary(N(1), FormulaBinaryOperator.Subtract, eta), FormulaBinaryOperator.Multiply,
                    FiniteSum("a", Bool(), Call("p", x, y, a, b))))));
        Formula bothFail = Eq(Call("lossy", eta, p, x, y, none, none),
            new Formula.Power(Parenthesized(new Formula.Binary(N(1), FormulaBinaryOperator.Subtract, eta)), N(2)));
        Formula branches = And(detected, And(oneFail, And(otherFail, bothFail)));
        return Disp(All("m", Nat(), All("eta", Real(), All("p", pType,
            All("x", Fin(m), All("y", Fin(m), branches))))));
    }

    private static Formula IsLocalFormula()
    {
        Formula m = F.Id("m"), q = F.Id("q"), s = F.Id("s"), x = F.Id("x"), y = F.Id("y"), a = F.Id("a"), b = F.Id("b");
        Formula strategy = Call("Prod", Arrow(Fin(m), Option(Bool())), Arrow(Fin(m), Option(Bool())));
        Formula qType = ArrowMany(Fin(m), Fin(m), Option(Bool()), Option(Bool()), Real());
        Formula wType = Arrow(strategy, Real());
        Formula weight = All("s", strategy, Le(N(0), Call("w", s)));
        Formula atom = Ite(And(Eq(new Formula.Apply(Qualified("Prod", "fst"), [s, x]), a),
            Eq(new Formula.Apply(Qualified("Prod", "snd"), [s, y]), b)), N(1), N(0));
        Formula action = All("x", Fin(m), All("y", Fin(m), All("a", Option(Bool()), All("b", Option(Bool()), Eq(
            Call("q", x, y, a, b), FiniteSum("s", strategy, Mul(Call("w", s), atom)))))));
        return Disp(All("m", Nat(), All("q", qType, Eq(Call("IsLocal", q),
            Exists("w", wType,
                And(weight, And(Eq(FiniteSum("s", strategy, Call("w", s)), N(1)), action)))))));
    }

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Frac(Formula n, Formula d) => new Formula.Fraction(n, d);

    private static Formula EtaFormula()
    {
        Formula m = F.Id("m"), eta = F.Id("eta"), p = F.Id("p");
        Formula pType = new Formula.TypeArrow(Fin(m), new Formula.TypeArrow(Fin(m),
            new Formula.TypeArrow(Bool(), new Formula.TypeArrow(Bool(), Real()))));
        Formula predicate = And(Le(D(0), eta), And(Le(eta, D(1)),
            All("p", pType, Imp(Call("IsNSBox", p), Call("IsLocal", Call("lossy", eta, p))))));
        Formula set = Seq(Esc, OpenBrace, eta, Colon, Real(), Sp, Mid, Sp, predicate, Esc, CloseBrace);
        return Disp(All("m", Nat(), Eq(Call("etaStar", m), Call("sSup", set))));
    }
    private static Formula ClaimFormula() => Disp(Eq(F.Id("claim"), All("m", Nat(),
        Imp(Le(D(2), F.Id("m")), Eq(Call("etaStar", F.Id("m")),
            Frac(D(4), Parenthesized(Seq(Parenthesized(Seq(F.Id("m"), Colon, Real())), Plus, D(4)))))))));

}
