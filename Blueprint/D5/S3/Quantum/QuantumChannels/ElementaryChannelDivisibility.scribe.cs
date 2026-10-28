using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ElementaryChannelDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/ElementaryChannelDivisibility.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Quantum/vomende2024divisibility");
    private static Formula I => Named("I");
    private static Formula J => Named("J");
    private static Formula X => Named("X");
    private static Formula K => Named("K");
    private static Formula G => Named("G");
    private static Formula T => Named("t");
    private static Formula V => Parenthesized(Seq(I, To, ComplexType()));
    private static Formula M => App("Matrix", I, I, ComplexType());
    private static Formula Map => Parenthesized(Seq(M,
        new Formula.Subscript(To, Seq(F.Id("l"), OpenBracket, ComplexType(), CloseBracket)), M));
    private static Formula Xv => Named("x");
    private static Formula Yv => Named("y");
    private static Formula Uv => Named("u");
    private static Formula Wv => Named("v");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Kraus-space criterion for elementary right division of finite quantum channels.",
        H("Elementary channel divisibility"), Blocks(
            Paragraph(Text("The index type I is finite. Matrices act on the complex coordinate space I → ℂ. The inner product is conjugate linear in its first argument, and tr denotes Matrix.trace. CP is the existing complete-positivity predicate, quantifying every finite amplification; CPTP also preserves the trace of every matrix. No assertion about a physical gate set, a local operations protocol, a success probability or a preparation cost follows from these statements.")),
            Node("factorofkernel", "Matrix factorization from kernel inclusion", "factor_of_kernel",
                FactorOfKernelFormula(),
                "If every vector annihilated by R is also annihilated by S, then S factors as CR. The linear map induced by S on the quotient by ker R descends to the range of R and extends to the whole finite coordinate space.",
                DescribeRole.Theorem, false),
            Node("kernelofsubpsd", "Kernel inclusion from positive domination", "kernel_of_sub_psd",
                KernelOfSubPsdFormula(),
                "If B and A − tB are positive semidefinite and t > 0, every vector annihilated by A is annihilated by B. On such a vector the two positivity inequalities force the quadratic form of B to vanish, and positive semidefiniteness then forces B to annihilate the vector.",
                DescribeRole.Theorem, false),
            Node("orthogonalunitpair", "Ordered orthogonal unit pair", "OrthogonalUnitPair",
                Context(All("x", V, All("y", V, Iff(App("OrthogonalUnitPair", Xv, Yv),
                    And(EqTo(Inner(Xv, Xv), D(1)), EqTo(Inner(Yv, Yv), D(1)), EqTo(Inner(Xv, Yv), D(0))))))),
                "The two vectors are separately normalized and orthogonal in the displayed order.", DescribeRole.Definition, true),
            Node("ketbra", "Rank one operator", "ketbra",
                Context(All("u", V, All("v", V, EqTo(App("ketbra", Uv, Wv),
                    App("vecMulVec", Uv, App("star", Wv)))))),
                "The operator ketbra(u,v) sends z to u⟨v,z⟩.", DescribeRole.Definition, true),
            Node("ketbrastar", "Adjoint of a rank one operator", "ketbra_star",
                KetbraStarFormula(),
                "Taking the adjoint exchanges the two vectors of the rank one operator.",
                DescribeRole.Theorem, false),
            Node("elementaryk", "First elementary Kraus operator", "elementaryK",
                Context(All("t", RealType(), All("x", V, EqTo(App("elementaryK", T, Xv),
                    Filter(SquareRoot(Subtract(D(1), T)), Xv))))),
                "This is Kₜ = I − (1 − √(1−t))|x⟩⟨x| from Definition 1. The real square root is embedded in ℂ.", DescribeRole.Definition, true),
            Node("elementaryl", "Second elementary Kraus operator", "elementaryL",
                Context(All("t", RealType(), All("x", V, All("y", V,
                    EqTo(App("elementaryL", T, Xv, Yv),
                        Smul(SquareRoot(T), App("ketbra", Yv, Xv))))))),
                "This is Lₜ = √t |y⟩⟨x| from Definition 1, with the real coefficient embedded in ℂ.", DescribeRole.Definition, true),
            Node("elementary", "Elementary channel", "elementary",
                Context(All("t", RealType(), All("x", V, All("y", V, All("X", M,
                    EqTo(Apply(App("elementary", T, Xv, Yv), X),
                        Add(Conjugate(App("elementaryK", T, Xv), X),
                            Conjugate(App("elementaryL", T, Xv, Yv), X)))))))),
                "The map is precisely the sum of conjugations by the two source Kraus operators. For an orthogonal unit pair and 0 < t < 1 it is an actual trace-preserving completely positive map.", DescribeRole.Definition, true),
            Node("elementaryinverse", "Exact elementary inverse", "elementaryInverse",
                Context(All("t", RealType(), All("x", V, All("y", V, All("X", M,
                    EqTo(Apply(App("elementaryInverse", T, Xv, Yv), X),
                        Subtract(Conjugate(Filter(Inverse(SquareRoot(Subtract(D(1), T))), Xv), X),
                            Smul(Divide(T, Subtract(D(1), T)), Conjugate(App("ketbra", Yv, Xv), X))))))))),
                "Equation (2) defines this linear map. The theorem below proves both inverse identities in its stated range, together with trace preservation on every matrix.", DescribeRole.Definition, true),
            Node("cptp", "Actual quantum channel", "CPTP",
                Context(All("Phi", Map, Iff(App("CPTP", Phi),
                    And(App("CP", Phi), All("X", M, EqTo(Trace(Apply(Phi, X)), Trace(X))))))),
                "CP is PhyslibLeaf.MatrixMap.IsCompletelyPositive, rather than positivity only on states or at a bounded amplification. The second conjunct is all-matrix trace preservation.", DescribeRole.Definition, false),
            Node("divides", "Elementary right division", "Divides",
                Context(All("Phi", Map, All("x", V, All("y", V,
                    Iff(App("Divides", Phi, Xv, Yv), Some("t", RealType(),
                        And(PositiveParameter(), App("CP", Residual(Phi))))))))),
                "The elementary channel is on the right of the composition. The same ordered pair is retained. The inverse formula is justified by the theorem when the pair is orthogonal and normalized.", DescribeRole.Definition, true),
            Node("necessary", "Necessary Kraus-space criterion", "Necessary",
                Context(Kraus(All("x", V, All("y", V,
                    Iff(App("Necessary", K, Xv, Yv), HSCondition(Yv, Xv)))))),
                "Orthogonality is to the complex linear span of the Kraus family. Span induction equates this with tr(Kⱼ*G) = 0 for every Kraus index. The tests range over all complex matrices G and all Kraus indices j. This is Proposition 1's condition.", DescribeRole.Definition, true),
            Node("sufficient", "Sufficient Kraus-space criterion", "Sufficient",
                Context(Kraus(All("x", V, All("y", V,
                    Iff(App("Sufficient", K, Xv, Yv),
                        And(App("Necessary", K, Xv, Yv), HSCondition(Xv, Xv))))))),
                "Theorem 1 adds the diagonal test ⟨x,Kⱼ*Gx⟩ = 0 to the necessary criterion. Its separate rank-reduction conclusion is not asserted here.", DescribeRole.Definition, true),
            Node("result", "The exact criterion and failure of the stronger converse", "result",
                Context(Implies(Seq(D(2), Leq, App("card", I)),
                    And(KrausExistence(), FixedCriterion(), ExistentialCriterion(), ActualDivision(), Counterexample()))),
                "Every actual CPTP map has a finite Kraus representation. For every finite dimension at least two, the necessary criterion is equivalent to elementary division for the same ordered pair, and therefore also after existential quantification over pairs. These equivalences hold for every finite Kraus representation of an actual CPTP map. The last conjunct exhibits an actual CPTP map with an elementary division and no pair satisfying the stronger sufficient criterion, in every representation. Thus neither the fixed-pair nor the existential-pair converse of that sufficient criterion holds. The Proved resolution marker records this combined classification: both necessary-criterion equivalences are proved, while both assertions that elementary division implies the stronger sufficient criterion are refuted.", DescribeRole.Theorem, false,
                "In input-first Choi coordinates let A = C(Φ) and Z = (|y⟩⟨x|)ᵀ ⊗ I. Hilbert–Schmidt orthogonality identifies the tests with ker A ⊆ ker(ZA Z*). If this inclusion holds, square roots factor as √B = C√A for B = ZA Z*. The operator norm bound gives B ≤ ‖C‖²A, and t = 1/(2(‖C‖²+1)) gives A−tB ≥ 0, including singular A. The exact Choi matrix of the residual is D(A−tB)D*, where D = Rᵀ ⊗ I and R is the inverse filter. Its congruence is invertible for 0 < t < 1.",
                "For distinct basis vectors eᵣ,eₛ, take Φ = elementary(15/16,eᵣ,eₛ) and Q = elementary(3/4,eᵣ,eₛ). Direct Kraus algebra gives Q∘Q = Φ, hence Φ∘Q⁻¹ = Q. For any unit u, the diagonal sufficient test fails: the Hilbert–Schmidt tests Eᵣᵢ for i ≠ r force either uᵣ = 0 or all other coordinates to vanish, while a diagonal orthogonal test gives 1−|I||uᵣ|² = 0. Both alternatives contradict normalization when |I| ≥ 2. The intrinsic kernel criterion transfers this obstruction to every finite Kraus representation. These are finite-dimensional conclusions; no dimension-one pair or infinite-dimensional domination statement is included.")
        )));

    private static Formula FactorOfKernelFormula()
    {
        Formula r = Named("R"), s = Named("S"), c = Named("C"), v = Named("v");
        return Context(All("R", M, All("S", M,
            Implies(All("v", V,
                    Implies(EqTo(App("mulVec", r, v), D(0)),
                        EqTo(App("mulVec", s, v), D(0)))),
                Some("C", M, EqTo(s, Multiply(c, r)))))));
    }

    private static Formula KernelOfSubPsdFormula()
    {
        Formula a = Named("A"), b = Named("B"), v = Named("v");
        return Context(All("A", M, All("B", M, All("t", RealType(),
            Implies(And(App("PosSemidef", b), Seq(D(0), Lt, T),
                    App("PosSemidef", Subtract(a, Smul(T, b)))),
                All("v", V, Implies(EqTo(App("mulVec", a, v), D(0)),
                    EqTo(App("mulVec", b, v), D(0)))))))));
    }

    private static Formula KetbraStarFormula()
    {
        Formula n = Named("n"), u = Named("u"), w = Named("w");
        Formula vector = Parenthesized(Seq(n, To, ComplexType()));
        return All("n", Named("Type"),
            Seq(Forall, Sp, OpenBracket, App("Fintype", n), CloseBracket,
                OpenBracket, App("DecidableEq", n), CloseBracket, Comma, Sp,
                All("u", vector, All("w", vector,
                    EqTo(Adj(App("ketbra", u, w)), App("ketbra", w, u))))));
    }

    private static Formula KrausExistence() => All("Phi", Map,
        Implies(App("CPTP", Phi), Some("K", Parenthesized(Seq(Parenthesized(Seq(I, Times, I)), To, M)),
            KrausEquality(Parenthesized(Seq(I, Times, I))))));
    private static Formula FixedCriterion() => Kraus(All("Phi", Map,
        Implies(And(App("CPTP", Phi), KrausEquality(J)),
            All("x", V, All("y", V, Implies(Pair(Xv, Yv),
                Iff(App("Necessary", K, Xv, Yv), App("Divides", Phi, Xv, Yv))))))));
    private static Formula ExistentialCriterion() => Kraus(All("Phi", Map,
        Implies(And(App("CPTP", Phi), KrausEquality(J)),
            Iff(Some("x", V, Some("y", V, And(Pair(Xv, Yv), App("Necessary", K, Xv, Yv)))),
                Some("x", V, Some("y", V, And(Pair(Xv, Yv), App("Divides", Phi, Xv, Yv))))))));
    private static Formula ActualDivision() => All("t", RealType(), Implies(PositiveParameter(),
        All("x", V, All("y", V, Implies(Pair(Xv, Yv),
            And(App("CPTP", App("elementary", T, Xv, Yv)),
                EqTo(Compose(App("elementary", T, Xv, Yv), App("elementaryInverse", T, Xv, Yv)), Named("id")),
                EqTo(Compose(App("elementaryInverse", T, Xv, Yv), App("elementary", T, Xv, Yv)), Named("id")),
                All("X", M, EqTo(Trace(Apply(App("elementaryInverse", T, Xv, Yv), X)), Trace(X))),
                All("Phi", Map, Implies(And(App("CPTP", Phi), App("CP", Residual(Phi))),
                    And(App("CPTP", Residual(Phi)),
                        EqTo(Compose(Residual(Phi), App("elementary", T, Xv, Yv)), Phi))))))))));
    private static Formula Counterexample() => Some("Phi", Map,
        And(App("CPTP", Phi),
            Some("x", V, Some("y", V, And(Pair(Xv, Yv), App("Divides", Phi, Xv, Yv)))),
            Kraus(Implies(KrausEquality(J), All("u", V, All("v", V,
                Implies(Pair(Uv, Wv), Seq(Neg, App("Sufficient", K, Uv, Wv)))))))));
    private static Formula HSCondition(Formula y, Formula x) => All("G", M,
        Implies(All("H", M, Implies(Seq(Named("H"), InMacro,
            App("span", ComplexType(), App("range", K))),
                EqTo(Trace(Multiply(Adj(Named("H")), G)), D(0)))),
            All("j", J, EqTo(Inner(y, Apply(Multiply(Adj(Apply(K, Named("j"))), G), x)), D(0)))));
    private static Formula KrausEquality(Formula indexType) => EqTo(
        Seq(Sum, Underscore, Grp(Seq(Variable("j"), InMacro, indexType)), Sp,
            Parenthesized(Seq(F.Id("fun"), Sp,
                Parenthesized(Seq(Variable("X"), Colon, M)), Sp, Mapsto, Sp,
                Multiply(
                    Multiply(Apply(K, Variable("j")), Variable("X")),
                    Adj(Apply(K, Variable("j"))))))),
        Phi);
    private static Formula Kraus(Formula body) => All("J", Named("Type"),
        Seq(Forall, Sp, OpenBracket, App("Fintype", J), CloseBracket, Comma, Sp,
            All("K", Parenthesized(Seq(J, To, M)), body)));
    private static Formula Context(Formula body) => All("I", Named("Type"),
        Seq(Forall, Sp, OpenBracket, App("Fintype", I), CloseBracket,
            OpenBracket, App("DecidableEq", I), CloseBracket, Comma, Sp, body));
    private static Formula PositiveParameter() => And(Seq(D(0), Lt, T), Seq(T, Lt, D(1)));
    private static Formula Pair(Formula x, Formula y) => App("OrthogonalUnitPair", x, y);
    private static Formula Residual(Formula phi) => Compose(phi, App("elementaryInverse", T, Xv, Yv));
    private static Formula Filter(Formula a, Formula x) => Add(D(1), Smul(Subtract(a, D(1)), App("ketbra", x, x)));
    private static Formula Conjugate(Formula a, Formula x) => Multiply(Multiply(a, x), Adj(a));
    private static Formula Trace(Formula x) => App("tr", x);
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, x, Comma, y, Rangle);
    private static Formula Adj(Formula x) => new Formula.Power(Parenthesized(x), Star);
    private static Formula Inverse(Formula x) => new Formula.Power(Parenthesized(x), Seq(Minus, D(1)));
    private static Formula SquareRoot(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Add(Formula x, Formula y) => Parenthesized(Seq(x, Plus, y));
    private static Formula Subtract(Formula x, Formula y) => Parenthesized(Seq(x, Minus, y));
    private static Formula Multiply(Formula x, Formula y) => Parenthesized(Seq(x, Sp, y));
    private static Formula Compose(Formula x, Formula y) => Parenthesized(Seq(x, Circ, y));
    private static Formula Smul(Formula x, Formula y) => Parenthesized(Seq(Parenthesized(x), Cdot, Parenthesized(y)));
    private static Formula EqTo(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Iff(Formula x, Formula y) => Parenthesized(Seq(Parenthesized(x), Leftrightarrow, Parenthesized(y)));
    private static Formula Implies(Formula x, Formula y) => Parenthesized(Seq(Parenthesized(x), To, Parenthesized(y)));
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(Variable(x), Colon, type)), Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(Variable(x), Colon, type)), Comma, Sp, body);
    private static Formula And(params Formula[] xs)
    {
        var pieces = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            pieces[i * 2] = Parenthesized(xs[i]);
            if (i + 1 < xs.Length) pieces[i * 2 + 1] = Land;
        }
        return Parenthesized(Seq(pieces));
    }
    private static Formula App(string f, params Formula[] args) => Apply(Named(f), args);
    private static Formula Apply(Formula f, params Formula[] args)
    {
        var pieces = new Formula[args.Length * 2 - 1];
        for (var i = 0; i < args.Length; i++)
        {
            pieces[i * 2] = args[i];
            if (i + 1 < args.Length) pieces[i * 2 + 1] = Comma;
        }
        return Parenthesized(Seq(f, Parenthesized(Seq(pieces))));
    }
    private static Formula Variable(string s) => s == "Phi" ? Phi : Named(s);
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Parenthesized(Formula x) => new Formula.LatexSequence([Open, x, Close]);
    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, bool literature, params string[] remaining)
    {
        var blocks = new DocumentBlock[remaining.Length + 1];
        blocks[0] = Paragraph(Text(prose));
        for (var i = 0; i < remaining.Length; i++) blocks[i + 1] = Paragraph(Text(remaining[i]));
        return Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), literature
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(blocks), role, openProblemResolutionClaim: name == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vomende-2024-elementary-channel-divisibility"),
                    ResolutionKind.Proved)
                : null);
    }
}
