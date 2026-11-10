using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class HighSpinCHSHNonviolationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuantumBounds/HighSpinCHSHNonviolation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/hanotelloubenets2025chshspinone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linear spin components obey the CHSH bound for every spin at least one.",
        H("Nonviolation of CHSH for all high-spin components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("high-spin-chsh-unit-direction"),
                DeclarationHandle.Create(Module + ".unit"),
                H("Unit measurement directions"),
                StatementSource.FromAuthor(Disp(UnitFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A direction is unit when the sum of the squares of its three real components is one. "
                        + "This is the unit-vector condition used for spin projections in the companion "
                        + "high-spin construction (arXiv:2412.03470v2, TeX lines 210–237)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("high-spin-chsh-operator"),
                DeclarationHandle.Create(Module + ".chshOperator"),
                H("The linear-spin CHSH operator"),
                StatementSource.FromAuthor(Disp(ChshOperatorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For four real measurement directions, this is the alternating sum of the four "
                        + "Kronecker products of their linear spin components. It is the operator in "
                        + "the source's CHSH expression (Final_Revision_Hanotel_Loubenets.tex, lines 108–115), "
                        + "with the spin observables described in the companion paper (TeX lines 253–261)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("high-spin-chsh-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The high-spin nonviolation assertion"),
                StatementSource.FromAuthor(Disp(Equivalence(LocalCall("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two, every positive semidefinite complex density matrix "
                        + "on the tensor product of two (n+1)-dimensional spaces, and every four unit real "
                        + "directions, the trace expectation of the linear-spin CHSH operator has norm at most "
                        + "the real cast of n squared divided by two. With n = 2s, this is the bound 2s² for "
                        + "spin s ≥ 1, addressing the open high-spin question stated in the source "
                        + "(Final_Revision_Hanotel_Loubenets.tex, line 201)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("high-spin-chsh-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Every high-spin linear-spin CHSH expectation obeys the bound"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix n, a positive semidefinite trace-one matrix ρ, and four unit directions. "
                            + "For each n-qubit slot, form the slot Pauli matrix associated with a direction. "
                            + "The Dicke map sends the (n+1)-dimensional spin basis into the symmetric n-qubit "
                            + "subspace; counting subsets of each cardinality proves that its adjoint times it "
                            + "is the identity.")),
                    Paragraph(Text(
                        "The slot matrices are Hermitian involutions. Their diagonal and flip entries decompose "
                            + "into raising, lowering, and z parts. Counting subsets not containing the selected slot "
                            + "and using the binomial coefficient identities gives the compression formula: each "
                            + "slot matrix compresses to (2/n) times the corresponding linear spin component. "
                            + "Tensoring two Dicke maps therefore compresses the lifted four-slot CHSH operator to "
                            + "the stated spin CHSH operator, with the scalar factor (n/2)².")),
                    Paragraph(Text(
                        "Use distinct slots for the two local settings. Operators on different slots commute, "
                            + "so the lifted CHSH operator is Hermitian and the commuting-pair CHSH identity gives "
                            + "its square as four times the identity. Conjugating ρ by the isometric dilation preserves "
                            + "positive semidefiniteness and trace one.")),
                    Paragraph(Text(
                        "The Hermitian square gives an operator norm at most two, and the density-matrix "
                            + "expectation estimate bounds the norm of its trace expectation by that operator norm. "
                            + "Cyclicity of trace moves the dilation through the original expectation; multiplying by "
                            + "the norm of (n/2)² yields (n/2)²·2 = n²/2. This proves the claim for every n ≥ 2."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanotel-loubenets-2025-high-spin-chsh-nonviolation"),
                    ResolutionKind.Proved)))));

    private static Formula UnitFormula() => All("u", VectorType(), Equivalence(Unit(X("u")), Equal(
        Add(Add(Pow(At(X("u"), D(0)), D(2)), Pow(At(X("u"), D(1)), D(2))),
            Pow(At(X("u"), D(2)), D(2))),
        Typed(D(1), Reals()))));

    private static Formula ChshOperatorFormula() =>
        All("n", Naturals(), AllDirections(Equal(
            Typed(LocalCall("chshOperator", X("n"), X("a"), X("c"), X("b"), X("d")),
                MatrixType(Add(X("n"), D(1)))),
            Subtract(
                Add(
                    Add(
                        Kronecker(Spin(X("n"), X("a")), Spin(X("n"), X("b"))),
                        Kronecker(Spin(X("n"), X("a")), Spin(X("n"), X("d")))),
                    Kronecker(Spin(X("n"), X("c")), Spin(X("n"), X("b")))),
                Kronecker(Spin(X("n"), X("c")), Spin(X("n"), X("d")))))));

    private static Formula ClaimBody() => All("n", Naturals(),
        Imp(Le(Typed(D(2), Naturals()), X("n")),
            All("ρ", MatrixType(Add(X("n"), D(1))),
                Imp(PosSemidef(X("ρ")),
                    Imp(Equal(Trace(X("ρ")), Typed(D(1), Complexes())),
                        AllDirections(
                            Imp(Unit(X("a")),
                                Imp(Unit(X("c")),
                                    Imp(Unit(X("b")),
                                        Imp(Unit(X("d")),
                                            Le(
                                                new Formula.Norm(Trace(Multiply(
                                                    X("ρ"),
                                                    LocalCall("chshOperator", X("n"), X("a"), X("c"), X("b"), X("d"))))),
                                                new Formula.Fraction(
                                                    new Formula.Power(NatCastReal(X("n")), D(2)),
                                                    Typed(D(2), Reals())))))))))))));

    private static Formula AllDirections(Formula body) =>
        Seq(Forall, Sp,
            Typed(Seq(X("a"), Sp, X("c"), Sp, X("b"), Sp, X("d")), VectorType()),
            Comma, Sp, Parenthesized(body));

    private static Formula Unit(Formula direction) => LocalCall("unit", direction);

    private static Formula Spin(Formula n, Formula direction) => At(
        Qualified("D5", "S3", "Quantum", "Contextuality", "TemporalHardySpinAttainment", "spinComponent"),
        n, direction);

    private static Formula Kronecker(Formula left, Formula right) => At(
        Qualified("Matrix", "kroneckerMap"),
        LambdaOf("x1", Complexes(), LambdaOf("x2", Complexes(), Multiply(X("x1"), X("x2")))),
        left, right);

    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);

    private static Formula PosSemidef(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula MatrixType(Formula size) => At(
        Qualified("Matrix"), Product(FinOf(size), FinOf(size)), Product(FinOf(size), FinOf(size)), Complexes());

    private static Formula VectorType() => Arrow(FinOf(D(3)), Reals());

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);

    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));

    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Qualified("D5", "S3", "QuantumBounds", "HighSpinCHSHNonviolation", name), arguments);

    private static Formula X(string name) => name == "ρ" ? Rho : F.Id(name);

    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
                items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula NatCastReal(Formula value) =>
        Typed(At(Qualified("Nat", "cast"), value), Reals());

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));

    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
