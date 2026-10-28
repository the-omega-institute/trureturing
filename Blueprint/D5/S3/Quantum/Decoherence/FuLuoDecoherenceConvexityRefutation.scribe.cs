using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FuLuoDecoherenceConvexityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Decoherence/FuLuoDecoherenceConvexityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/fuluo2021decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit four-dimensional system with four qubit sub-environments violates the conjectured convexity of the Fu-Luo decoherence quantifier.",
        H("Fu-Luo decoherence convexity is refuted"),
        Blocks(
            SourceQuotation(),
            Node("classicality", "The classicality functional J", JFormula(),
                "Equation (17) states verbatim: \"J(ρ,Π) = 1 + tr(√ρ Π†(√ρ)) = 1 + Σ_i 〈i|√ρ|i〉².\" The encoding uses the standard basis of Fin d and takes the real part of each diagonal square.",
                "J", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("environment-index", "Environment basis labels", EnvIdxFormula(),
                "An environment basis label assigns to each part l a basis element of Fin (k l).",
                "EnvIdx", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("local-lift", "A local environment operator", LiftEFormula(),
                "The source describes U_{Ei} acting only on H_{Ei}. The encoding applies Ui at coordinate i and enforces equality at every other environment coordinate.",
                "liftE", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("product-environment", "The product environment state", RhoEFormula(),
                "The source describes the initial state as ρ_SE = ρ_S ⊗ ρ_E with ρ_E = ρ_{E1} ⊗ ρ_{E2} ⊗ ⋯ ⊗ ρ_{Ed}. The encoding multiplies the corresponding entries of the component density states.",
                "rhoE", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("decoherence-overlap", "The environment overlap matrix", OmegaFormula(),
                "Equation (21) states verbatim: \"ρ′_S = tr_E ρ′_SE = Σ_{i,j=1}^d tr(U_{Ei} ρ_E U_{Ej}†) · Π_i ρ_S Π_j\". The overlap is the displayed trace factor.",
                "omega", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("final-state", "The final system state", FinalStateFormula(),
                "Equation (22) states verbatim that the reduced state is \"ρ_S ∘ Ω\", where ∘ is the Hadamard product and Ω = (ω_ij). The encoding multiplies each entry by omega.",
                "finalState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("decoherence-quantifier", "The decoherence quantifier D", DFormula(),
                "Equation (27) states verbatim: \"D(ρ_S|Π, U) = J(ρ′_S, Π) − J(ρ_S, Π)\". The encoding subtracts the initial classicality from the final classicality.",
                "D", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("convexity-claim", "The conjectured convexity statement", ClaimFormula(),
                "The source states verbatim after Proposition 3: \"We conjecture that D(rho_S|Pi, U) is convex in rho. It seems that a proof may require some deep mathematics.\" The formal statement expands convexity as the Jensen inequality for every dimension, product environment, family of local unitaries, pair of density states, and t in [0,1].",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("refutation", "An explicit violation in dimension four", ResultFormula(),
                "For four system coordinates, four qubit environments in the state |0><0|, and detector unitaries (X, X, Z, Z), the two explicit density states have D equal to 5/16 while their midpoint has D equal to 3/8. Thus the Jensen inequality in the expanded claim is false.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("fu-luo-decoherence-convexity"),
                    ResolutionKind.Refuted), WitnessExposition()))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "S. Fu and S. Luo, Quantifying Decoherence via Increases in Classicality, Entropy 23(12) (2021), 1594, Section 3. The source states verbatim: \"We conjecture that D(ρ_S|Π, U) is convex in ρ. It seems that a proof may require some deep mathematics.\" Equation (17) states \"J(ρ,Π) = 1 + tr(√ρ Π†(√ρ)) = 1 + Σ_i 〈i|√ρ|i〉².\" Equations (21)–(22) state \"ρ′_S = tr_E ρ′_SE = Σ_{i,j=1}^d tr(U_{Ei} ρ_E U_{Ej}†) · Π_i ρ_S Π_j\", with \"ρ_S ∘ Ω\", and Equation (27) states \"D(ρ_S|Π, U) = J(ρ′_S, Π) − J(ρ_S, Π)\"."));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null, DocumentBlock[]? exposition = null) => Describe.Lean(
        DescribeId.Create("fuluo-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks([Paragraph(Text(prose)), .. exposition ?? []]), role, openProblemResolutionClaim: resolution);

    private static DocumentBlock[] WitnessExposition()
    {
        var f = Call("false");
        var t = Call("true");
        var q = Seq(Sqrt, Grp(D(3)));
        var r = Seq(Sqrt, Grp(D(2)));
        var nq = Seq(Minus, q);
        var rq = Mul(r, q);
        var midpointEntries = MatrixFour(
            D(1), D(0), q, D(0),
            D(0), D(1), D(0), q,
            q, D(0), D(3), D(0),
            D(0), q, D(0), D(3));
        return [
            Paragraph(Text("In the standard basis of Fin 4, the private definitions R false and R true are the two input matrices. The density states state false and state true use these matrices through CStarMatrix.ofMatrix. All entries below are real, regarded as complex numbers.")),
            Display(Equal(Call("R", f), Scale(Fraction(D(1), D(8)), MatrixFour(
                D(1), D(1), q, q,
                D(1), D(1), q, q,
                q, q, D(3), D(3),
                q, q, D(3), D(3))))),
            Display(Equal(Call("R", t), Scale(Fraction(D(1), D(8)), MatrixFour(
                D(1), Seq(Minus, D(1)), q, nq,
                Seq(Minus, D(1)), D(1), nq, q,
                q, nq, D(3), Seq(Minus, D(3)),
                nq, q, Seq(Minus, D(3)), D(3))))),
            Paragraph(Text("The private lemma mixture identifies their midpoint with M.")),
            Display(Equal(
                Add(Scale(Fraction(D(1), D(2)), Call("R", f)),
                    Scale(Fraction(D(1), D(2)), Call("R", t))), Call("M"))),
            Display(Equal(Call("M"), Scale(Fraction(D(1), D(8)), midpointEntries))),
            Paragraph(Text("For the same tau and detectors, final_R and final_M give the output matrices B false, B true and BM.")),
            Display(All("b", Call("Bool"), Equal(
                Call("finalState", Call("tau"), Call("detectors"), Call("R", F.Id("b"))),
                Call("B", F.Id("b"))))),
            Display(Equal(Call("B", f), Scale(Fraction(D(1), D(8)), MatrixFour(
                D(1), D(0), D(0), D(0),
                D(0), D(1), D(0), D(0),
                D(0), D(0), D(3), D(3),
                D(0), D(0), D(3), D(3))))),
            Display(Equal(Call("B", t), Scale(Fraction(D(1), D(8)), MatrixFour(
                D(1), D(0), D(0), D(0),
                D(0), D(1), D(0), D(0),
                D(0), D(0), D(3), Seq(Minus, D(3)),
                D(0), D(0), Seq(Minus, D(3)), D(3))))),
            Display(Equal(
                Call("finalState", Call("tau"), Call("detectors"), Call("M")), Call("BM"))),
            Display(Equal(Call("BM"), Scale(Fraction(D(1), D(8)), MatrixFour(
                D(1), D(0), D(0), D(0),
                D(0), D(1), D(0), D(0),
                D(0), D(0), D(3), D(0),
                D(0), D(0), D(0), D(3))))),
            Paragraph(Text("The positive square-root certificates use R itself for each endpoint, SM for M, S for B, and SBM for BM. The private lemmas R_pos, SM_pos, S_pos and SBM_pos certify positive semidefiniteness; R_square, SM_square, S_square and SBM_square certify the squares. The lemmas sqrt_R, sqrt_M, sqrt_B and sqrt_BM identify these with CFC.sqrt.")),
            Display(Equal(Call("SM"), Scale(Fraction(r, D(8)), midpointEntries))),
            Display(Equal(Call("S", f), Scale(Fraction(D(1), D(4)), MatrixFour(
                r, D(0), D(0), D(0),
                D(0), r, D(0), D(0),
                D(0), D(0), q, q,
                D(0), D(0), q, q)))),
            Display(Equal(Call("S", t), Scale(Fraction(D(1), D(4)), MatrixFour(
                r, D(0), D(0), D(0),
                D(0), r, D(0), D(0),
                D(0), D(0), q, nq,
                D(0), D(0), nq, q)))),
            Display(Equal(Call("SBM"), Scale(Fraction(D(1), D(4)), MatrixFour(
                r, D(0), D(0), D(0),
                D(0), r, D(0), D(0),
                D(0), D(0), rq, D(0),
                D(0), D(0), D(0), rq)))),
            Display(All("b", Call("Bool"),
                SquareRootCertificate(Call("R", F.Id("b")), Call("R", F.Id("b"))))),
            Display(SquareRootCertificate(Call("M"), Call("SM"))),
            Display(All("b", Call("Bool"),
                SquareRootCertificate(Call("B", F.Id("b")), Call("S", F.Id("b"))))),
            Display(SquareRootCertificate(Call("BM"), Call("SBM")))
        ];
    }

    private static DocumentBlock Display(Formula formula) => new DocumentBlock.DisplayFormula(formula);

    private static Formula SquareRootCertificate(Formula matrix, Formula root) =>
        new Formula.Logic(Parenthesized(Equal(Apply(Qualified("CFC", "sqrt"), matrix), root)),
            FormulaLogicOperator.And, Parenthesized(new Formula.Logic(
                CallQualified("Matrix", "PosSemidef", root), FormulaLogicOperator.And,
                Parenthesized(Equal(Mul(root, root), matrix)))));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula MatrixFour(
        Formula a, Formula b, Formula c, Formula d,
        Formula e, Formula f, Formula g, Formula h,
        Formula i, Formula j, Formula k, Formula l,
        Formula m, Formula n, Formula o, Formula p) => Seq(
        Begin, Grp(F.Id("pmatrix")),
        a, Amp, b, Amp, c, Amp, d, RowBreak,
        e, Amp, f, Amp, g, Amp, h, RowBreak,
        i, Amp, j, Amp, k, Amp, l, RowBreak,
        m, Amp, n, Amp, o, Amp, p,
        End, Grp(F.Id("pmatrix")));

    private static Formula JFormula() => Disp(All("d", Nat(), All("rho", MatrixType(FinOf(F.Id("d"))),
        Equal(Call("J", F.Id("rho")), Add(D(1), SumOver("i", FinOf(F.Id("d")),
            RealPart(Power(Entry(Apply(Qualified("CFC", "sqrt"), F.Id("rho")), F.Id("i"), F.Id("i")), D(2)))))))));

    private static Formula EnvIdxFormula() => Disp(All("d", Nat(), All("k", Fn(FinOf(F.Id("d")), Nat()),
        Equal(Call("EnvIdx", F.Id("k")), DepFn("l", FinOf(F.Id("d")), FinOf(Apply(F.Id("k"), F.Id("l"))))))));

    private static Formula LiftEFormula()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var i = F.Id("i");
        var ui = F.Id("Ui");
        var x = F.Id("x");
        var y = F.Id("y");
        var condition = All("l", FinOf(d), Implies(NotEqual(F.Id("l"), i),
            Equal(Apply(x, F.Id("l")), Apply(y, F.Id("l")))));
        var entry = Call("ite", Parenthesized(condition),
            Apply(Apply(ui, Apply(x, i)), Apply(y, i)), D(0));
        return Disp(All("d", Nat(), All("k", Fn(FinOf(d), Nat()), All("i", FinOf(d),
            All("Ui", MatrixType(FinOf(Apply(k, i))),
                Equal(Call("liftE", i, ui),
                    Lambda("x", Call("EnvIdx", k), Lambda("y", Call("EnvIdx", k), entry))))))));
    }

    private static Formula RhoEFormula() => Disp(All("d", Nat(), All("k", Fn(FinOf(F.Id("d")), Nat()),
        All("tau", DepFn("l", FinOf(F.Id("d")), Call("DensityState", FinOf(Apply(F.Id("k"), F.Id("l"))))),
            Equal(Call("rhoE", F.Id("tau")),
                Lambda("x", Call("EnvIdx", F.Id("k")), Lambda("y", Call("EnvIdx", F.Id("k")),
                    ProductOver("l", FinOf(F.Id("d")),
                        Apply(Apply(Apply(Qualified("Subtype", "val"), Apply(F.Id("tau"), F.Id("l"))), Apply(F.Id("x"), F.Id("l"))),
                            Apply(F.Id("y"), F.Id("l")))))))))));

    private static Formula OmegaFormula()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var tau = F.Id("tau");
        var u = F.Id("U");
        var i = F.Id("i");
        var j = F.Id("j");
        var left = Mul(Call("liftE", i, Call("val", Apply(u, i))), Call("rhoE", tau));
        var right = CallQualified("Matrix", "conjTranspose",
            Call("liftE", j, Call("val", Apply(u, j))));
        var equation = Equal(Call("omega", tau, u, i, j),
            CallQualified("Matrix", "trace", Mul(left, right)));
        var result = equation;
        result = All("j", FinOf(d), result);
        result = All("i", FinOf(d), result);
        result = All("U", DepFn("l", FinOf(d),
            CallQualified("Matrix", "unitaryGroup", FinOf(Apply(k, F.Id("l"))), Complex())), result);
        result = All("tau", DepFn("l", FinOf(d),
            Call("DensityState", FinOf(Apply(k, F.Id("l"))))), result);
        result = All("k", Fn(FinOf(d), Nat()), result);
        result = All("d", Nat(), result);
        return Disp(result);
    }

    private static Formula FinalStateFormula() => Disp(All("d", Nat(), All("k", Fn(FinOf(F.Id("d")), Nat()),
        All("tau", DepFn("l", FinOf(F.Id("d")), Call("DensityState", FinOf(Apply(F.Id("k"), F.Id("l"))))),
            All("U", DepFn("l", FinOf(F.Id("d")),
                CallQualified("Matrix", "unitaryGroup", FinOf(Apply(F.Id("k"), F.Id("l"))), Complex())),
                All("rho", MatrixType(FinOf(F.Id("d"))),
                    Equal(Call("finalState", F.Id("tau"), F.Id("U"), F.Id("rho")),
                        Lambda("a", FinOf(F.Id("d")), Lambda("b", FinOf(F.Id("d")),
                            Mul(Entry(F.Id("rho"), F.Id("a"), F.Id("b")),
                                Call("omega", F.Id("tau"), F.Id("U"), F.Id("a"), F.Id("b"))))))))))));

    private static Formula DFormula() => Disp(All("d", Nat(), All("k", Fn(FinOf(F.Id("d")), Nat()),
        All("tau", DepFn("l", FinOf(F.Id("d")), Call("DensityState", FinOf(Apply(F.Id("k"), F.Id("l"))))),
            All("U", DepFn("l", FinOf(F.Id("d")),
                CallQualified("Matrix", "unitaryGroup", FinOf(Apply(F.Id("k"), F.Id("l"))), Complex())),
                All("rho", MatrixType(FinOf(F.Id("d"))),
                    Equal(Call("D", F.Id("tau"), F.Id("U"), F.Id("rho")),
                        Subtract(Call("J", Call("finalState", F.Id("tau"), F.Id("U"), F.Id("rho"))),
                            Call("J", F.Id("rho"))))))))));

    private static Formula ClaimFormula() => Disp(Equivalent(Seq(Operatorname, Grp(F.Id("claim"))), ClaimBody()));

    private static Formula ClaimBody()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var tau = F.Id("tau");
        var u = F.Id("U");
        var rho = F.Id("rho");
        var sigma = F.Id("sigma");
        var t = F.Id("t");
        var toMatrix = Qualified("CStarMatrix", "ofMatrix");
        var fromMatrix = Qualified("Equiv", "symm");
        var rhoVal = Apply(Qualified("Subtype", "val"), rho);
        var sigmaVal = Apply(Qualified("Subtype", "val"), sigma);
        var rhoOperator = Apply(Apply(fromMatrix, toMatrix), rhoVal);
        var sigmaOperator = Apply(Apply(fromMatrix, toMatrix), sigmaVal);
        var mixedOperator = Apply(Apply(fromMatrix, toMatrix),
            Add(Scale(t, rhoVal), Scale(Subtract(D(1), t), sigmaVal)));
        var lhs = Call("D", tau, u, mixedOperator);
        var rhs = Add(Mul(t, Call("D", tau, u, rhoOperator)),
            Mul(Subtract(D(1), t), Call("D", tau, u, sigmaOperator)));
        var body = LessThanOrEqual(lhs, rhs);
        body = Implies(LessThanOrEqual(D(0), t), Implies(LessThanOrEqual(t, D(1)), body));
        body = All("t", Real(), body);
        body = All("sigma", Call("DensityState", FinOf(d)), body);
        body = All("rho", Call("DensityState", FinOf(d)), body);
        body = All("U", DepFn("l", FinOf(d),
            CallQualified("Matrix", "unitaryGroup", FinOf(Apply(k, F.Id("l"))), Complex())), body);
        body = All("tau", DepFn("l", FinOf(d),
            Call("DensityState", FinOf(Apply(k, F.Id("l"))))), body);
        body = All("k", Fn(FinOf(d), Nat()), body);
        body = All("d", Nat(), body);
        return body;
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(Parenthesized(ClaimBody())));

    private static Formula MatrixType(Formula n) => Call("Matrix", n, n, Complex());
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula DepFn(string name, Formula domain, Formula body) =>
        Parenthesized(new Formula.TypeArrow(Parenthesized(Seq(F.Id(name), Colon, Sp, domain)), body));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula CallQualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equivalent(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LessThanOrEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Scale(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula RealPart(Formula a) => CallQualified("Complex", "re", a);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, body);
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(Prod, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, body);
    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        new Formula.Apply(matrix, [i, j]);
}
