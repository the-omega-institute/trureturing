using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class StabilizerExtensionQuaternaryMinimalLengthDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Codes/StabilizerExtensionQuaternaryMinimalLength.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/mahmoud2026macwilliams");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quaternary quantum extension property already fails at lengths one and three, so length five is not minimal.",
        H("A quaternary refutation of the length-five extension expectation"),
        Blocks(
            Node("tr", "The trace map on the quaternary field", TrFormula(),
                "The carrier K 1 is the four-element field 𝔽₄, and tr x = x + x squared is its trace to the binary subfield. The label alphabet HilbertPhase (K 1) is A₄ = 𝔽₄² in the source's notation (MzWi_Ext_Th.tex, lines 211–217)."),
            Node("symp", "The trace-symplectic pairing", SympFormula(),
                "For two vectors u and v of labels, sum the determinant-like terms u_i.1 v_i.2 − v_i.1 u_i.2 and apply tr. The carrier HilbertPhase (K 1) is the label alphabet 𝔽₄², and the expression is the coordinate form of the trace-symplectic pairing in the source (MzWi_Ext_Th.tex, lines 211–215)."),
            Node("selfOrthogonal", "Trace-symplectic self-orthogonality", SelfOrthogonalFormula(),
                "An additive subgroup C is self-orthogonal when the trace-symplectic pairing of every two of its elements is zero. This is the self-orthogonality condition imposed on additive stabilizer codes in the source (MzWi_Ext_Th.tex, lines 217 and 237–239)."),
            Node("qepWitness", "A monomial extension witness", QepWitnessFormula(),
                "A permutation π of the coordinates and a determinant-one two-by-two matrix τ_i at each coordinate witness an extension when f u at coordinate i equals τ_i applied to u at the coordinate π⁻¹(i). The determinant-one condition is the concrete symplectic condition for the quaternary label alphabet, matching the monomial transformation in Definition 2.1 (MzWi_Ext_Th.tex, lines 221–223)."),
            Node("QEP", "The quaternary quantum extension property", QepFormula(),
                "QEP n asserts that every pair of self-orthogonal additive subgroups of the label alphabet at length n, together with every additive bijection preserving Hamming weight, has a witness of the preceding monomial form. This is the source's Definition 2.3 specialized to q = 4 (MzWi_Ext_Th.tex, lines 237–239)."),
            Node("QEPAdd", "The extension property for coordinate additive automorphisms", QepAddFormula(),
                "QEPAdd n has the same hypotheses as QEP n, but permits an arbitrary additive equivalence of the label alphabet at each coordinate in the extension equation. For K 1 = 𝔽₄, this is the full coordinatewise additive-automorphism version described alongside the symplectic group in Definition 2.1 (MzWi_Ext_Th.tex, lines 221–223)."),
            Node("claim", "The expected minimal length five", ClaimFormula(),
                "The claim is the disjunction of two leastness assertions: either 5 is the least positive length where QEP fails, or 5 is the least positive length where QEPAdd fails. It is the q = 4 instance of the expectation that the minimal counterexample length is q + 1 (MzWi_Ext_Th.tex, lines 427–430)."),
            Describe.Lean(
                DescribeId.Create("mahmoud-qep-quaternary-result"),
                DeclarationHandle.Create(Module + "result"),
                H("Lengths one and three refute the length-five claim"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Choose an element w of the four-element field with w different from 0 and 1. "
                            + "For length one, use the additive maps (a,b) ↦ (a + b w, 0) and "
                            + "(a,b) ↦ (a,b) from the binary pair space into the one-coordinate label alphabet. "
                            + "Their images are self-orthogonal, the induced additive equivalence preserves Hamming weight, "
                            + "and the only coordinate permutation is the identity. If a determinant-one matrix extended "
                            + "this equivalence, the image of (1,0) would force its lower-left entry to be zero; "
                            + "its action on the source label (w,0), corresponding to the binary parameter (0,1), "
                            + "would then force 1 = 0 times w, a contradiction. Thus QEP 1 fails.")),
                    Paragraph(Text(
                        "For length three, use the additive maps (a,b) ↦ ((a,b w),(a,b w),(0,0)) and "
                            + "(a,b) ↦ ((a+b,0),(a,0),(b,0)). Their images are self-orthogonal and the induced equivalence "
                            + "preserves Hamming weight. If a coordinatewise additive extension existed, let j be the image "
                            + "of coordinate 2 under its permutation. Every vector in the first image is zero at coordinate 2, "
                            + "so every image under the extension is zero at j. Additive surjectivity would then make every "
                            + "element of the second image zero at j, but explicit elements of that image are nonzero at each "
                            + "of the three coordinates. This contradiction proves QEPAdd 3 fails.")),
                    Paragraph(Text(
                        "The first leastness assertion in the claim cannot hold because 1 is a positive member of its failure set, "
                            + "and the second cannot hold because 3 is a positive member of its failure set. The two smaller "
                            + "counterexample lengths contradict the asserted least value 5."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mahmoud-2026-quaternary-extension-minimal-length-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("mahmoud-qep-quaternary-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(X(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);

    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);

    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula All(string name, Formula type, Formula body) =>
        All(X(name), type, body);

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Smul(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula K1() => Call("K", D(1));
    private static Formula Labels() => Call("HilbertPhase", K1());
    private static Formula Index(Formula n) => Call("Fin", n);
    private static Formula Vectors(Formula n) => Arrow(Index(n), Labels());
    private static Formula Code(Formula n) => Call("AddSubgroup", Vectors(n));
    private static Formula CodeType(Formula code) => Call("Subtype", code);
    private static Formula AddEquiv(Formula left, Formula right) =>
        Call("AddEquiv", CodeType(left), CodeType(right));
    private static Formula Matrix2() => Call("Matrix", Index(D(2)), Index(D(2)), K1());
    private static Formula Permutation(Formula n) => QCall("Equiv", "Perm", Index(n));
    private static Formula Coe(Formula value) => Call("coe", value);
    private static Formula ApplyCoordinate(Formula value, Formula index) =>
        At(value, index);
    private static Formula Projection(Formula value, byte index) =>
        Seq(value, Dot, D(index));
    private static Formula SumOver(string variable, Formula type, Formula term) =>
        Seq(new Formula.Subscript(Sum, Typed(X(variable), type)), Sp, Parenthesized(term));

    private static Formula TrFormula()
    {
        var x = X("x");
        return All("x", K1(), Equal(Call("tr", x),
            Add(x, new Formula.Power(x, D(2)))));
    }

    private static Formula SympFormula()
    {
        var n = X("n");
        var u = X("u");
        var v = X("v");
        var ui = ApplyCoordinate(u, X("i"));
        var vi = ApplyCoordinate(v, X("i"));
        var summand = Subtract(
            Multiply(Projection(ui, 1), Projection(vi, 2)),
            Multiply(Projection(vi, 1), Projection(ui, 2)));
        var sum = SumOver("i", Index(n), summand);
        return All("n", Naturals(), All("u", Vectors(n), All("v", Vectors(n),
            Equal(Call("symp", u, v), Call("tr", sum)))));
    }

    private static Formula SelfOrthogonalFormula()
    {
        var n = X("n");
        var c = X("C");
        var u = X("u");
        var v = X("v");
        var body = All("u", Vectors(n), Imp(
            Member(u, c),
            All("v", Vectors(n), Imp(Member(v, c),
                Equal(Call("symp", u, v), Typed(D(0), K1()))))));
        return All("n", Naturals(), All("C", Code(n),
            IffF(Call("selfOrthogonal", c), body)));
    }

    private static Formula QepWitnessFormula()
    {
        var n = X("n");
        var c = X("C");
        var d = X("D");
        var f = X("f");
        var tau = Tau;
        var pi = Pi;
        var i = X("i");
        var u = X("u");
        var determinant = Equal(
            QCall("Matrix", "det", At(tau, i)),
            Typed(D(1), K1()));
        var action = Equal(
            ApplyCoordinate(Coe(At(f, u)), i),
            Smul(At(tau, i),
                ApplyCoordinate(Coe(u), At(QCall("Equiv", "symm", pi), i))));
        var witnessBody = And(All("i", Index(n), determinant),
            All("u", CodeType(c), All("i", Index(n), action)));
        return All("n", Naturals(),
            All("C", Code(n), All("D", Code(n),
                All("f", AddEquiv(c, d),
                    All(pi, Permutation(n), All(tau, Arrow(Index(n), Matrix2()),
                        IffF(Call("qepWitness", f, pi, tau), witnessBody)))))));
    }

    private static Formula QepFormula()
    {
        var n = X("n");
        var c = X("C");
        var d = X("D");
        var f = X("f");
        var u = X("u");
        var pi = Pi;
        var tau = Tau;
        var premise = Call("selfOrthogonal", c);
        var weight = All("u", CodeType(c), Equal(
            Call("hammingNorm", Coe(At(f, u))),
            Call("hammingNorm", Coe(u))));
        var conclusion = Some(pi, Permutation(n),
            Some(tau, Arrow(Index(n), Matrix2()), Call("qepWitness", f, pi, tau)));
        var qepBody = All("C", Code(n), All("D", Code(n),
            Imp(premise,
                Imp(Call("selfOrthogonal", d),
                    All("f", AddEquiv(c, d), Imp(weight, conclusion))))));
        return All("n", Naturals(), IffF(Call("QEP", n), qepBody));
    }

    private static Formula QepAddFormula()
    {
        var n = X("n");
        var c = X("C");
        var d = X("D");
        var f = X("f");
        var u = X("u");
        var pi = Pi;
        var tau = Tau;
        var premise = Call("selfOrthogonal", c);
        var weight = All("u", CodeType(c), Equal(
            Call("hammingNorm", Coe(At(f, u))),
            Call("hammingNorm", Coe(u))));
        var action = Equal(
            ApplyCoordinate(Coe(At(f, u)), X("i")),
            At(At(tau, X("i")),
                ApplyCoordinate(Coe(u), At(QCall("Equiv", "symm", pi), X("i")))));
        var coordinateEquation = All("u", CodeType(c), All("i", Index(n), action));
        var conclusion = Some(pi, Permutation(n),
            Some(tau, Arrow(Index(n), Call("AddEquiv", Labels(), Labels())),
                coordinateEquation));
        var addBody = All("C", Code(n), All("D", Code(n),
            Imp(premise,
                Imp(Call("selfOrthogonal", d),
                    All("f", AddEquiv(c, d), Imp(weight, conclusion))))));
        return All("n", Naturals(), IffF(Call("QEPAdd", n), addBody));
    }

    private static Formula SetOfFailures(string predicate)
    {
        var n = X("n");
        return Seq(OpenBrace, n, Sp, Colon, Sp, Naturals(), Sp, Mid, Sp,
            And(LessOrEqual(Typed(D(1), Naturals()), n),
                new Formula.Not(Parenthesized(Call(predicate, n)))),
            CloseBrace);
    }

    private static Formula ClaimFormula()
    {
        var qepLeast = Call("IsLeast", SetOfFailures("QEP"), Typed(D(5), Naturals()));
        var addLeast = Call("IsLeast", SetOfFailures("QEPAdd"), Typed(D(5), Naturals()));
        return Or(qepLeast, addLeast);
    }

    private static Formula ResultFormula() =>
        new Formula.Not(Parenthesized(ClaimFormula()));
}
