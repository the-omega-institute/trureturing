using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class AllenMeyerNegativityRegionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/allen2017polynomialmonogamy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized asymmetric three-qutrit vector has a negativity triple outside the family in equation (13) of Allen and Meyer.",
        H("The Allen–Meyer family omits achievable three-qutrit negativities"),
        Blocks(
            Paragraph(Text(
                "The three factors are A, B and C, each indexed by Fin(3) = {0, 1, 2}. "
                    + "A vector is a complex-valued function on Fin(3) × (Fin(3) × Fin(3)); "
                    + "the triple (i, j, k) means (i, (j, k)). The ket |ijk⟩ is the coordinate "
                    + "vector with value one there and zero elsewhere. A bar denotes complex conjugation, "
                    + "and real coefficients in vectors are included in the complex numbers. "
                    + "The definitions below apply to arbitrary vectors; unit normalization is imposed in claim.")),
            Node("pairAB", "Tracing out C", PairFormula(true),
                "The reduced matrix on A and B is partialTraceRight of rankOneDensity of the "
                    + "amplitude ((i, j), k) ↦ psi(i, j, k). The rank-one density has entries "
                    + "v(p) times the complex conjugate of v(q), and partialTraceRight sums its "
                    + "entries at (p, k), (q, k) over k. "
                    + "For p = (i, j) and q = (i', j'), its entry sums over the common C index. "
                    + "This is the A|B reduced state used in the negativity region following equation (13)."),
            Node("pairAC", "Tracing out B", PairFormula(false),
                "The reduced matrix on A and C is partialTraceRight of rankOneDensity of the "
                    + "amplitude ((i, k), j) ↦ psi(i, j, k). Its rank-one entries are traced over "
                    + "the common final index j. "
                    + "For p = (i, k) and q = (i', k'), its entry sums over the common B index. "
                    + "This is the A|C reduced state used in the same region."),
            Node("negativityTriple", "The three partial-transpose negativities", TripleFormula(),
                "The coordinates are the negativities of the AB and AC reduced matrices and of the pure "
                    + "state rankOneDensity(psi) = |psi⟩⟨psi| across A|BC, in that order. Its entry "
                    + "at p, q is psi(p) times the complex conjugate of psi(q). "
                    + "The notation Γ transposes the second factor: "
                    + "for row (i, j) and column (k, l), the transposed entry is the original entry at "
                    + "row (i, l) and column (k, j). The subscript-one norm is the trace norm. "
                    + "Each coordinate is (‖rho^Γ‖₁ − 1)/2. Allen and Meyer use twice this value and "
                    + "transpose A; transposing the other factor gives the same trace norm. "
                    + "The common factor one half does not change equality of triples."),
            Node("familyState", "Equation (13) for three qutrits", FamilyFormula(),
                "The same coefficients a, b and c occur at both nonzero levels j = 1 and j = 2. "
                    + "The seven coordinate vectors in this sum are distinct. Thus its squared norm "
                    + "is d² + 2(a² + b² + c²), without any restriction on the real parameters."),
            Node("claim", "The conjectured entire negativity region", ClaimFormula(),
                "For every unit three-qutrit vector, some member of equation (13) with nonnegative "
                    + "real coefficients and unit norm has exactly the same negativity triple. "
                    + "This is the conjecture immediately after equation (13), restricted to dimension three. "
                    + "The paper orders the pair coordinates as AC, AB and uses squared negativities; "
                    + "a fixed coordinate swap and squaring nonnegative negativities do not affect equality of triples."),
            Describe.Lean(
                DescribeId.Create("allen-meyer-negativity-region-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An asymmetric vector lies outside the family"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write x, y and z for the paper's negativities N = ‖rho^Γ‖₁ − 1 of AB, AC "
                            + "and A|BC, respectively, so these are twice the coordinates of negativityTriple. "
                            + "For a normalized family state with nonnegative coefficients, put "
                            + "r = √(a² + b² + c²), u = b² + c² and delta = z − y. "
                            + "Its Schmidt coefficients across A|BC are d, r, r, giving z = 4dr + 2r². "
                            + "A difference of positive semidefinite matrices for the AC partial transpose "
                            + "gives y ≤ 2a² + 4ad. When r is positive this implies "
                            + "delta ≥ 2(1 + d/r)u.")),
                    Paragraph(Text(
                        "If z ≥ 14/11 and delta ≤ 2/209, normalization and the Schmidt formula imply "
                            + "r > 0, 1/7 ≤ d/r ≤ 3, u ≤ 1/209 and a² ≥ 18r²/19, in particular a > 0. "
                            + "A Gram decomposition of the AB partial transpose as a difference of positive "
                            + "semidefinite matrices gives x ≤ 2b² + 4d²u/a² ≤ 2u(1 + 2d²/a²). "
                            + "Combining these estimates yields the separator x ≤ 5(z − y) for every family "
                            + "state with z ≥ 14/11 and z − y ≤ 2/209.")),
                    Paragraph(Text(
                        "Now take the normalized vector "
                            + "(5|000⟩ + 3|101⟩ + |202⟩ + t|110⟩ + 5t|220⟩)/√(35 + 26t²) "
                            + "at t = 1/100. Its squared normalization factor is 175013/5000. "
                            + "Unitary trace certificates give lower bounds for x and y, and its three "
                            + "Schmidt coefficients give lower and upper bounds for z. Rational bounds "
                            + "on the square roots then show z ≥ 14/11, z − y ≤ 2/209 and x > 5(z − y). "
                            + "A family state with this triple would satisfy both opposing inequalities. "
                            + "Therefore this vector's negativity triple is absent from the family."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("allen-meyer-2017-negativity-region-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("allen-meyer-negativity-region-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula FinThree() => Call("Fin", D(3));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula PairType() => Product(FinThree(), FinThree());
    private static Formula TripleType() => Product(FinThree(), Parenthesized(PairType()));
    private static Formula Vectors() => Parenthesized(new Formula.TypeArrow(TripleType(), Complexes()));
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(variable), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(variable), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Coordinate(string name, byte index) => new Formula.Subscript(V(name), D(index));
    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));
    private static Formula Tuple(Formula first, Formula second, Formula third) =>
        Parenthesized(Seq(first, Comma, Sp, second, Comma, Sp, third));
    private static Formula Ket(Formula first, Formula second, Formula third) =>
        Seq(Bar, first, Thin, second, Thin, third, Rangle);
    private static Formula SumOver(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(variable), type)), Sp, Parenthesized(body));
    private static Formula RealParameters(Formula body) =>
        All("a", Reals(), All("b", Reals(), All("c", Reals(), All("d", Reals(), body))));
    private static Formula Family() => Call("familyState", V("a"), V("b"), V("c"), V("d"));
    private static Formula Normalization() => Equal(Add(Square(V("d")),
        Multiply(D(2), Parenthesized(Add(Add(Square(V("a")), Square(V("b"))), Square(V("c")))))), D(1));

    private static Formula PairFormula(bool traceC)
    {
        var index = traceC ? "c" : "b";
        Formula Address(string name) => traceC
            ? Tuple(Coordinate(name, 1), Coordinate(name, 2), V(index))
            : Tuple(Coordinate(name, 1), V(index), Coordinate(name, 2));
        var amplitude = Parenthesized(Seq(
            Typed(Parenthesized(Seq(V("r"), Comma, Sp, V(index))),
                Product(Parenthesized(PairType()), FinThree())), Sp, Mapsto, Sp,
            At(V("psi"), Address("r"))));
        var reduced = Call("partialTraceRight", Call("rankOneDensity", amplitude));
        return All("psi", Vectors(), All("p", PairType(), All("q", PairType(),
            Seq(Equal(Call(traceC ? "pairAB" : "pairAC", V("psi"), V("p"), V("q")),
                    At(reduced, V("p"), V("q"))), Sp, Eq, Sp,
                SumOver(index, FinThree(), Multiply(At(V("psi"), Address("p")),
                    Conjugate(At(V("psi"), Address("q")))))))));
    }

    private static Formula Negativity(Formula matrix) => new Formula.Fraction(
        Subtract(new Formula.Subscript(new Formula.Norm(new Formula.Power(Parenthesized(matrix), Gamma)), D(1)),
            D(1)), D(2));

    private static Formula TripleFormula() => All("psi", Vectors(),
        And(Equal(Call("negativityTriple", V("psi")),
                Tuple(Negativity(Call("pairAB", V("psi"))), Negativity(Call("pairAC", V("psi"))),
                    Negativity(Call("rankOneDensity", V("psi"))))),
            All("p", TripleType(), All("q", TripleType(),
                Equal(Call("rankOneDensity", V("psi"), V("p"), V("q")),
                    Multiply(At(V("psi"), V("p")), Conjugate(At(V("psi"), V("q")))))))));

    private static Formula FamilyFormula()
    {
        var summand = Add(Add(Multiply(V("a"), Ket(V("j"), D(0), V("j"))),
            Multiply(V("b"), Ket(V("j"), V("j"), D(0)))),
            Multiply(V("c"), Ket(V("j"), V("j"), V("j"))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(V("j"), Sp, InMacro, Sp,
            new Formula.SetLiteral([D(1), D(2)]))), Sp, Parenthesized(summand));
        return RealParameters(Equal(Family(), Add(Multiply(V("d"), Ket(D(0), D(0), D(0))), sum)));
    }

    private static Formula ClaimFormula()
    {
        var coefficients = Some("a", Reals(), Some("b", Reals(), Some("c", Reals(), Some("d", Reals(),
            And(LE(D(0), V("a")), And(LE(D(0), V("b")), And(LE(D(0), V("c")), And(LE(D(0), V("d")),
                And(Normalization(), Equal(Call("negativityTriple", Family()),
                    Call("negativityTriple", V("psi"))))))))))));
        var unit = Equal(SumOver("i", TripleType(), Square(new Formula.Absolute(At(V("psi"), V("i"))))), D(1));
        return Iff(Typed(Named("claim"), V("Prop")), All("psi", Vectors(), Imp(unit, coefficients)));
    }
}
