using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class TwirlingPhaseRetrievabilityCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/TwirlingPhaseRetrievabilityCounterexample.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hanliu2023twirling");

    private const string TwirlQuote =
        "We define a linear map Φ<sub>π, σ</sub>: B(K, H) → B(K, H) by Φ<sub>π, σ</sub>(T) = ∫<sub>G</sub>π(g)Tσ(g<sup>−1</sup>) dμ(g) and denote Φ<sub>π, σ</sub> by Φ<sub>π</sub> when π = σ.";
    private const string PhaseQuote =
        "A subspace M of H is called phase retrievable under Φ if Φ is pure state injective on M, i.e., Φ(x⊗x) = Φ(y⊗y) implies that x⊗x = y⊗y for x, y∈M, or equivalently if there exists a POVM {F<sub>j</sub>}<sub>j∈𝕁</sub> in B(K) such that {P<sub>M</sub>Φ<sup>*</sup>(F<sub>j</sub>)P<sub>M</sub>}<sub>j∈𝕁</sub> is a phase retrievable operator valued frame for M, where P<sub>M</sub> is the orthogonal projection onto M.";
    private const string IndexQuote =
        "The phase retrievability index pr(Φ<sub>π</sub>) is defined to be the largest integer k such that there exits a k-dimensional subspace M⊂H such that M is phase retrievable under Φ.";
    private const string FrameQuote =
        "For an n-dimensional Hilbert space H, we will use ℐ<sub>n</sub> to denote the smallest integer N such that there is a phase retrievable frame {x<sub>j</sub>}<sub>j=1</sub><sup>N</sup> for H.";
    private const string CodeQuote =
        "Let 𝒞 be a subspace of H, and let P be the orthogonal projections onto 𝒞. Suppose Φ is a quantum channel with Kraus operators {E<sub>i</sub>}<sub>i=1</sub><sup>r</sup>. Then the following are equivalent:";
    private const string CodeItems =
        "(i) 𝒞 is a quantum code for Φ. (ii) there exists a Hermitian matrix A = [a<sub>ij</sub>] such that PE<sub>i</sub><sup>*</sup>E<sub>j</sub>P = a<sub>ij</sub>P holds for all i, j.";
    private const string BetaQuote =
        "β(Φ<sub>π</sub>) = max{m<sub>1</sub>, ... , m<sub>d</sub>} is the largest number m such that there exists a quantum code of dimension m.";
    private const string IrreducibleQuote =
        "A representation π is called irreducible if 0 and H are the only invariant subspaces.";
    private const string DecompositionQuote =
        "where m<sub>i</sub>∈ℕ and π<sub>1</sub>, ... , π<sub>d</sub> are inequivalent irreducible unitary representations of G acting on Hilbert spaces H<sub>1</sub>, ... , H<sub>d</sub>, respectively.";
    private const string ClaimQuote =
        "Conjecture. Let π = m<sub>1</sub>π<sub>1</sub>⊕ ... ⊕ m<sub>d</sub>π<sub>d</sub> be a unitary representation of G such that π<sub>i</sub> and π<sub>j</sub> are inequivalent irreducible representations for all i≠j and ℐ<sub>k</sub> ≤ d < ℐ<sub>k+1</sub>. Then pr(Φ<sub>π</sub>) = max {β(Φ<sub>π</sub>), k}.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three characters of C3 with multiplicity two contradict the proposed twirling phase index formula.",
        H("Overlapping pairs refute the twirling phase index formula"),
        Blocks(
            Node("chi-unit", "Unit modulus of the three characters", "chi_unit", ChiUnitFormula(),
                "For every character index and group element, the character's conjugate product is one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("scale-norm-sq", "The squared two-coordinate scale", "scale_normSq",
                Disp(Eqn(App(Q("Complex", "normSq"),
                    new Formula.Power(Seq(Sqrt, Grp(D(2))), new Formula.Negate(D(1)))),
                    new Formula.Fraction(D(1), D(2)))),
                "The reciprocal of the positive real square root of two is regarded as a complex scalar. "
                    + "Its squared complex modulus is one half.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Paragraph(Text("All vector and matrix coordinates are complex. Fin indices start at zero. "
                + "Matrix.vecMulVec(x, star(x)) is the rank-one state of x. Anonymous brackets "
                + "display Lean typeclass assumptions; val displays a unitary matrix's coercion. "
                + "Natural suprema and infima encode the extremal dimensions and frame lengths. "
                + "The finite-group conjecture is implied by the source's compact-group conjecture.")),
            Node("twirl", "The finite twirling channel", "twirl", TwirlFormula(),
                "Page 3: “" + TwirlQuote + "” For finite G normalized Haar integration is "
                + "the uniform average. pi is a group homomorphism into Matrix.unitaryGroup. "
                + "Unitarity makes the inverse equal to star. I indexes the coordinate space.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phase", "Phase retrievable subspaces", "PhaseRetrievable", PhaseFormula(),
                "Page 5: “" + PhaseQuote + "” The encoding uses the pure-state-injectivity "
                + "clause. Phi maps square matrices, M is a complex submodule, and x and y "
                + "range over every member of M, with no normalization restriction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("index", "The phase retrievability index", "pr", IndexFormula(false),
                "Page 5: “" + IndexQuote + "” The spelling exits is retained. k is a "
                + "natural dimension, finrank is over Complex, and the supremum is over "
                + "dimensions of all phase retrievable subspaces.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("code", "Correctable codes", "IsCode", CodeFormula(),
                "Page 5, Lemma 3.1: “" + CodeQuote + "” Its first two items read: “" + CodeItems
                + "” The encoding takes the Knill–Laflamme clause for the Kraus family "
                + "pi(g)/sqrt(card G). The common normalization is absorbed into c. "
                + "A self-adjoint idempotent with range M is its orthogonal projection. "
                + "The compression scalars are automatically Hermitian for a nonzero code; "
                + "for the zero code they may be chosen zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("beta", "The code dimension index", "beta", IndexFormula(true),
                "Page 2: “" + BetaQuote + "” Theorem 3.4, page 7, proves the equality. "
                + "Here beta(pi) denotes beta of the induced twirling channel, as the "
                + "supremum of the finranks of the IsCode subspaces.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("length", "Minimal complex frame length", "frameLength", FrameFormula(),
                "Page 4: “" + FrameQuote + "” k is the source's n, and n is the family's "
                + "length N. f has n vectors in Fin k to Complex. The norms of the complex "
                + "dotProducts are their magnitudes. A retrieving family spans: a nonzero "
                + "vector orthogonal to the family would collide with zero. No additional "
                + "frame condition changes the family of admissible lengths.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("irreducible", "Nonzero irreducible representations", "Irreducible", IrreducibleFormula(),
                "Page 2: “" + IrreducibleQuote + "” rho acts on Fin n to Complex. "
                + "The dimension is positive, as required for an irreducible representation. "
                + "Every invariant submodule equals bottom or top.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("inequivalent", "No invertible intertwiner", "Inequivalent", InequivalentFormula(),
                "Page 2: “" + DecompositionQuote + "” rho and sigma are inequivalent "
                + "when there is no complex-linear equivalence intertwining every group "
                + "element. This is the finite-dimensional unitary equivalence convention.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("block", "The multiplicity decomposition", "blockRep", BlockFormula(),
                "Page 2 displays U pi(g) U star = m1 pi1 direct-sum ... direct-sum md pid "
                + "and states: “" + DecompositionQuote + "” blockRep(rho,m) is the "
                + "homomorphism with blocks Matrix.kronecker(1,val(rho(i,g))). The dependent "
                + "index has a block label, a multiplicity coordinate and an irreducible "
                + "coordinate. The displayed expression binds the complete family n and m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The final conjecture of Section 5", "claim", ClaimFormula(),
                "Page 13: “" + ClaimQuote + "” The encoding quantifies finite groups G, "
                + "the number d of pairwise inequivalent irreducibles, their dimensions n, "
                + "positive multiplicities m and the frame-length index k. The source's "
                + "one-based summand labels become Fin d. The finite-group specialization "
                + "is sufficient for a refutation of the compact-group assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", "result", Disp(new Formula.Not(F.Id("claim"))),
                "Take G = Multiplicative(ZMod(3)), the three one-dimensional characters, "
                + "d = 3 and every multiplicity equal to two. Character orthogonality "
                + "identifies the twirl with three-block pinching. The isometric map "
                + "(u,v,w) to ((u,v),(u,w),(v,w))/sqrt(2) places every entry of a three by "
                + "three operator in a surviving two by two compression. Its range is "
                + "phase retrievable, giving pr at least three. Knill–Laflamme compressions "
                + "force every code to inject into a block of dimension two, and a whole "
                + "block attains that dimension. One frame vector retrieves the complex "
                + "one-dimensional space; three vectors cannot retrieve the two-dimensional "
                + "space, whereas four can. Thus k = 1 and max(beta,k) = 2. The three-vector "
                + "obstruction uses real rank-nullity to construct nonzero x and y for "
                + "which x+y and x-y have equal measurements but different rank-one states. "
                + "The rectangular matrix uses Matrix.conjTranspose, while square matrices "
                + "use star. The multiplicity-one character case is compatible with this "
                + "counterexample, as are the source's code formula and lower bounds.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("han-liu-2023-twirling-phase-retrievability"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("hl-twirling-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        Seq(function, Sp, Parenthesized(Seq([.. args.SelectMany((x, i) =>
            i == 0 ? new[] { x } : new[] { Comma, Sp, x })])));
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Some(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula NeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula TypeType() => Call("Type");
    private static Formula FinType(Formula n) => Call("Fin", n);
    private static Formula Vectors(Formula index) => Arrow(index, ComplexType());
    private static Formula Matrices(Formula index) => Call("Matrix", index, index, ComplexType());
    private static Formula Submodules(Formula index) => Call("Submodule", ComplexType(), Vectors(index));
    private static Formula Unitaries(Formula index) => App(Q("Matrix", "unitaryGroup"), index, ComplexType());
    private static Formula Hom(Formula g, Formula index) => Seq(g, Sp, To,
        Caret, Grp(Star), Sp, Unitaries(index));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula StarOf(Formula a) => Call("star", a);
    private static Formula Outer(Formula a) => App(Q("Matrix", "vecMulVec"), a, StarOf(a));
    private static Formula Finrank(Formula m) => App(Q("Module", "finrank"), ComplexType(), m);
    private static Formula Instance(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula MatrixInstances(Formula i, Formula body) =>
        Instance("Fintype", i, Instance("DecidableEq", i, body));
    private static Formula GroupInstances(Formula g, bool finite, Formula body) =>
        Instance("Group", g, finite ? Instance("Fintype", g, body) : body);
    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, domain)), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula domain, Formula condition) =>
        Seq(Esc, OpenBrace, F.Id(name), Sp, Colon, Sp, domain, Sp, Mid, Sp, condition, Esc, CloseBrace);

    private static Formula ChiUnitFormula()
    {
        var i = F.Id("i"); var g = F.Id("g");
        var phase = App(Q("ZMod", "stdAddChar"),
            Mul(App(Q("ZMod", "finEquiv"), D(3), i), App(Q("Multiplicative", "toAdd"), g)));
        return Disp(All("i", FinType(D(3)), All("g", Call("Multiplicative", Call("ZMod", D(3))),
            Eqn(Mul(StarOf(phase), phase), D(1)))));
    }

    private static Formula TwirlFormula()
    {
        var g = F.Id("G"); var i = F.Id("I"); var pi = F.Id("pi"); var x = F.Id("X");
        var v = Val(App(pi, F.Id("g")));
        var summand = Mul(Mul(v, x), StarOf(v));
        var sum = Seq(Sum, Underscore, Grp(F.Id("g"), Sp, Colon, Sp, g), Sp, Parenthesized(summand));
        var inverse = new Formula.Power(App(Q("Fintype", "card"), g), new Formula.Negate(D(1)));
        var rhs = Seq(Parenthesized(Seq(inverse, Sp, Colon, Sp, ComplexType())), Sp, Cdot, Sp, sum);
        return Disp(All("G", TypeType(), GroupInstances(g, true, All("I", TypeType(),
            MatrixInstances(i, All("pi", Hom(g, i), All("X", Matrices(i), Eqn(Call("twirl", pi, x), rhs))))))));
    }

    private static Formula PhaseFormula()
    {
        var i = F.Id("I"); var phi = F.Id("Phi"); var m = F.Id("M"); var x = F.Id("x"); var y = F.Id("y");
        var predicate = All("x", Vectors(i), Imp(Member(x, m), All("y", Vectors(i),
            Imp(Member(y, m), Imp(Eqn(App(phi, Outer(x)), App(phi, Outer(y))), Eqn(Outer(x), Outer(y)))))));
        return Disp(All("I", TypeType(), All("Phi", Arrow(Matrices(i), Matrices(i)),
            All("M", Submodules(i), IffTo(Call("PhaseRetrievable", phi, m), predicate)))));
    }

    private static Formula IndexFormula(bool code)
    {
        var g = F.Id("G"); var i = F.Id("I"); var phi = F.Id("Phi"); var pi = F.Id("pi");
        var m = F.Id("M"); var k = F.Id("k"); var input = code ? pi : phi;
        var predicate = Call(code ? "IsCode" : "PhaseRetrievable", input, m);
        var set = SetOf("k", NatType(), Some("M", Submodules(i), And(Eqn(Finrank(m), k), predicate)));
        var equation = Eqn(Call(code ? "beta" : "pr", input), Call("sSup", set));
        if (!code) return Disp(All("I", TypeType(), All("Phi", Arrow(Matrices(i), Matrices(i)), equation)));
        return Disp(All("G", TypeType(), GroupInstances(g, false, All("I", TypeType(),
            MatrixInstances(i, All("pi", Hom(g, i), equation))))));
    }

    private static Formula CodeFormula()
    {
        var gtype = F.Id("G"); var i = F.Id("I"); var pi = F.Id("pi"); var m = F.Id("M");
        var p = F.Id("P"); var c = F.Id("c"); var g = F.Id("g"); var h = F.Id("h");
        var range = App(Q("LinearMap", "range"), App(Q("Matrix", "mulVecLin"), p));
        var compression = Mul(Mul(Mul(p, StarOf(Val(App(pi, g)))), Val(App(pi, h))), p);
        var conditions = And(Eqn(StarOf(p), p), And(Eqn(Mul(p, p), p), And(Eqn(range, m),
            Some("c", Arrow(gtype, Arrow(gtype, ComplexType())), All("g", gtype, All("h", gtype,
                Eqn(compression, Seq(App(c, g, h), Sp, Cdot, Sp, p))))))));
        var equation = IffTo(Call("IsCode", pi, m), Some("P", Matrices(i), conditions));
        return Disp(All("G", TypeType(), GroupInstances(gtype, false, All("I", TypeType(),
            MatrixInstances(i, All("pi", Hom(gtype, i), All("M", Submodules(i), equation)))))));
    }

    private static Formula Retrieval(Formula f, Formula n, Formula k)
    {
        var x = F.Id("x"); var y = F.Id("y"); var j = F.Id("j");
        var fx = Call("dotProduct", x, StarOf(App(f, j)));
        var fy = Call("dotProduct", y, StarOf(App(f, j)));
        return All("x", Vectors(FinType(k)), All("y", Vectors(FinType(k)),
            Imp(All("j", FinType(n), Eqn(Call("norm", fx), Call("norm", fy))), Eqn(Outer(x), Outer(y)))));
    }

    private static Formula FrameFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("f");
        var set = SetOf("n", NatType(), Some("f", Arrow(FinType(n), Vectors(FinType(k))), Retrieval(f, n, k)));
        return Disp(All("k", NatType(), Eqn(Call("frameLength", k), Call("sInf", set))));
    }

    private static Formula Action(Formula rho, Formula g, Formula x) =>
        App(Q("Matrix", "mulVec"), Val(App(rho, g)), x);

    private static Formula IrreducibleFormula()
    {
        var gtype = F.Id("G"); var n = F.Id("n"); var rho = F.Id("rho"); var m = F.Id("M");
        var x = F.Id("x"); var g = F.Id("g");
        var invariant = All("g", gtype, All("x", Vectors(FinType(n)),
            Imp(Member(x, m), Member(Action(rho, g, x), m))));
        var trivial = Or(Eqn(m, Q("Bot", "bot")), Eqn(m, Q("Top", "top")));
        var predicate = And(Less(D(0), n), All("M", Submodules(FinType(n)), Imp(invariant, trivial)));
        return Disp(All("G", TypeType(), GroupInstances(gtype, false, All("n", NatType(),
            All("rho", Hom(gtype, FinType(n)), IffTo(Call("Irreducible", rho), predicate))))));
    }

    private static Formula InequivalentFormula()
    {
        var gtype = F.Id("G"); var n = F.Id("n"); var k = F.Id("k");
        var rho = F.Id("rho"); var sigma = F.Id("sigma"); var t = F.Id("T"); var x = F.Id("x"); var g = F.Id("g");
        var equivalence = Seq(Vectors(FinType(n)), Sp, Equiv,
            new Formula.Subscript(Grp(), Seq(F.Id("l"), OpenBracket, ComplexType(), CloseBracket)), Sp,
            Vectors(FinType(k)));
        var intertwines = All("g", gtype, All("x", Vectors(FinType(n)),
            Eqn(App(t, Action(rho, g, x)), Action(sigma, g, App(t, x)))));
        var predicate = new Formula.Not(Some("T", equivalence, intertwines));
        return Disp(All("G", TypeType(), GroupInstances(gtype, false, All("n", NatType(), All("k", NatType(),
            All("rho", Hom(gtype, FinType(n)), All("sigma", Hom(gtype, FinType(k)),
                IffTo(Call("Inequivalent", rho, sigma), predicate))))))));
    }

    private static Formula DecompositionIndex(Formula d, Formula n, Formula m)
    {
        var i = F.Id("i");
        return Seq(Sigma, new Formula.Subscript(Grp(), Seq(i, Sp, Colon, Sp, FinType(d))), Sp,
            Parenthesized(Seq(FinType(App(m, i)), Sp, Times, Sp, FinType(App(n, i)))));
    }

    private static Formula RepresentationFamily(Formula g, Formula d, Formula n) =>
        All("i", FinType(d), Hom(g, FinType(App(n, F.Id("i")))));

    private static Formula BlockFormula()
    {
        var gtype = F.Id("G"); var d = F.Id("d"); var n = F.Id("n"); var m = F.Id("m");
        var rho = F.Id("rho"); var g = F.Id("g"); var i = F.Id("i"); var mi = FinType(App(m, i));
        var identity = Parenthesized(Seq(D(1), Sp, Colon, Sp, Matrices(mi)));
        var block = App(Q("Matrix", "kronecker"), identity, Val(App(rho, i, g)));
        var rhs = App(Seq(Q("Matrix", "blockDiagonal"), Apos), LambdaOf("i", FinType(d), block));
        var lhs = Val(App(Call("blockRep", rho, m), g));
        var equation = Eqn(Parenthesized(Seq(lhs, Sp, Colon, Sp, Matrices(DecompositionIndex(d, n, m)))), rhs);
        return Disp(All("G", TypeType(), GroupInstances(gtype, false, All("d", NatType(),
            All("n", Arrow(FinType(d), NatType()), All("rho", RepresentationFamily(gtype, d, n),
                All("m", Arrow(FinType(d), NatType()), All("g", gtype, equation))))))));
    }

    private static Formula ClaimFormula()
    {
        var gtype = F.Id("G"); var d = F.Id("d"); var n = F.Id("n"); var m = F.Id("m");
        var rho = F.Id("rho"); var k = F.Id("k"); var i = F.Id("i"); var j = F.Id("j");
        var irreducible = All("i", FinType(d), Call("Irreducible", App(rho, i)));
        var inequivalent = All("i", FinType(d), All("j", FinType(d), Imp(NeqTo(i, j),
            Call("Inequivalent", App(rho, i), App(rho, j)))));
        var positive = All("i", FinType(d), LeqTo(D(1), App(m, i)));
        var representation = Call("blockRep", rho, m);
        var conclusion = Eqn(Call("pr", Call("twirl", representation)), Call("max", Call("beta", representation), k));
        var indexed = All("k", NatType(), Imp(LeqTo(Call("frameLength", k), d),
            Imp(Less(d, Call("frameLength", Add(k, D(1)))), conclusion)));
        var body = All("G", TypeType(), GroupInstances(gtype, true, All("d", NatType(),
            All("n", Arrow(FinType(d), NatType()), All("m", Arrow(FinType(d), NatType()),
                All("rho", RepresentationFamily(gtype, d, n), Imp(irreducible, Imp(inequivalent, Imp(positive, indexed)))))))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}
