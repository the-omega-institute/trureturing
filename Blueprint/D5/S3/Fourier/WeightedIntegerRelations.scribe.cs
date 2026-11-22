using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class WeightedIntegerRelationsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/WeightedIntegerRelations";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer relations impose a weighted deficit on finite sine sums.",
        H("Weighted integer-character bounds"),
        Blocks(
            Paragraph(Text("Let C and R be finite sets of column and row indices in arbitrary types J "
                + "and A. A phase vector takes values in Circle, the complex numbers of modulus one. "
                + "Products of integer powers are taken in Circle and their differences and norms "
                + "are taken in the complex numbers. The notation χ(C,z,k) denotes the character "
                + "given by the product of z(j) raised to k(j) over j in C.")),
            Describe.Lean(DescribeId.Create("product-character-chord"),
                DeclarationHandle.Create(Owner + ".chord_prod_zpow"),
                H("Chord bound for one character"), StatementSource.FromAuthor(ProductChord()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chord of two products is bounded by the sum of the "
                    + "factor chords because multiplication by a unit complex number preserves "
                    + "norm. Nonnegative powers have chord bounded by the power times the original "
                    + "chord. Inversion on Circle is complex conjugation, so the bound for negative "
                    + "powers has the absolute integer exponent. "),
                    Ref("D5/S3/AnalyticClosure/ComplexPowerDifference"))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-character-chord"),
                DeclarationHandle.Create(Owner + ".weighted_character_chord"),
                H("Simultaneous weighted character chords"),
                StatementSource.FromAuthor(WeightedChord()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write kₐ for the integer vector in row a. Sum the chord "
                    + "bounds with nonnegative multipliers λ(a) and collect all the terms from "
                    + "each column. Weighted Cauchy–Schwarz gives the square bound, including "
                    + "overlaps through the column sums taken before squaring."))),
                DescribeRole.Theorem),
            Paragraph(Text("For real frequencies γ and weights w positive on C, write W(C,w) "
                + "for the sum of w(j) over C. At each real v let S(v) be the sum of "
                + "w(j) sin(γ(j)v) over C. For positive W(C,w), D(C,γ,w) is "
                + "1 − sup over real v of S(v) divided by W(C,w). Each relation row "
                + "has zero weighted frequency sum with coefficients k(a,j), and "
                + "δ(C,kₐ) is the norm of the difference between 1 and the power of i whose exponent "
                + "is the sum of the row's integer coefficients.")),
            Describe.Lean(DescribeId.Create("weighted-phase-deficit"),
                DeclarationHandle.Create(Owner + ".weighted_phase_deficit"),
                H("Phase deficit from nonnegative multipliers"),
                StatementSource.FromAuthor(MultiplierBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the orbit exp(iγ(j)v), each relation character is one. "
                    + "At the constant quarter phase i, its value is i raised to the coefficient "
                    + "sum. The weighted sum of squared coordinate chords to i is exactly "
                    + "2(W − S(v)). The character estimate bounds S(v) uniformly in v, so its "
                    + "supremum satisfies the same upper bound. The multiplier inequality "
                    + "uses positive total mass and positive column energy."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("disjoint-weighted-phase-deficit"),
                DeclarationHandle.Create(Owner + ".weighted_phase_deficit_disjoint"),
                H("Additive deficit for disjoint nonzero rows"),
                StatementSource.FromAuthor(DisjointBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero row has positive energy, defined as the "
                    + "sum over j in C of k(a,j)²/w(j). Use the multiplier δ divided by "
                    + "that energy in each row. Disjoint supports eliminate all cross terms "
                    + "from each squared column load. This makes both the numerator before "
                    + "squaring and the column energy equal to the sum of squared defects "
                    + "divided by row energies. When that sum is zero, including an empty "
                    + "row family, the bound follows from S(v) ≤ W."))),
                DescribeRole.Theorem))));

    private static Formula Reals => Field("R");
    private static Formula Integers => Field("Z");
    private static Formula Circle => Id("Circle");
    private static Formula Columns => Id("C");
    private static Formula Rows => Id("R");
    private static Formula J => Id("J");
    private static Formula A => Id("A");
    private static Formula Gamma => Id("gamma");
    private static Formula W => Call("W", Columns, Id("w"));
    private static Formula D => Call("D", Columns, Gamma, Id("w"));

    private static Formula Field(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula AllMember(string name, Formula type, Formula set, Formula body) =>
        All(name, type, Imp(Member(Id(name), set), body));
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Sum(string index, Formula set, Formula body) =>
        F.Seq(F.Sum, F.Underscore, F.Grp(F.Id(index), F.InMacro, F.Sp, set), F.Sp, body);
    private static Formula Square(Formula body) => new Formula.Power(body, Num(2));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Abs(Formula body) => new Formula.Absolute(body);
    private static Formula Norm(Formula body) => F.Seq(F.Vert, F.Sp, F.Vert, F.Sp, body, F.Vert, F.Sp, F.Vert);
    private static Formula K(string row, string col) => Call("k", Id(row), Id(col));
    private static Formula Weight() => Call("w", Id("j"));
    private static Formula Multiplier() => Call("lambda", Id("a"));
    private static Formula Row(string row) => Call("k", Id(row));
    private static Formula Chord(Formula z, Formula q) => Norm(Subtract(z, q));
    private static Formula Character(string phase, Formula k) => Call("chi", Columns, Id(phase), k);
    private static Formula Delta() => F.Seq(F.DeltaLower, F.Sp, F.Open, Columns, F.Comma, Row("a"), F.Close);

    private static Formula Family(Formula body) =>
        All("J", Id("Type"), All("A", Id("Type"), All("C", Call("Finset", J),
            All("R", Call("Finset", A), body))));
    private static Formula Phases(Formula body) =>
        All("z", Arrow(J, Circle), All("q", Arrow(J, Circle), body));
    private static Formula WeightsAndRows(Formula body) =>
        All("w", Arrow(J, Reals), All("k", Arrow(A, Arrow(J, Integers)), body));
    private static Formula PositiveWeights() => AllMember("j", J, Columns, Lt(Num(0), Weight()));
    private static Formula NonnegativeMultipliers() =>
        AllMember("a", A, Rows, Le(Num(0), Multiplier()));
    private static Formula ColumnEnergy() =>
        Sum("j", Columns, Div(Square(Sum("a", Rows,
            Multiply(Multiplier(), Abs(K("a", "j"))))), Weight()));
    private static Formula Relations() => AllMember("a", A, Rows, Equal(
        Sum("j", Columns, Multiply(K("a", "j"), Call("gamma", Id("j")))), Num(0)));
    private static Formula NonzeroRows() => AllMember("a", A, Rows, Exists("j", J,
        new Formula.Logic(Member(Id("j"), Columns), FormulaLogicOperator.And, Ne(K("a", "j"), Num(0)))));
    private static Formula DisjointRows() => AllMember("a", A, Rows, AllMember("b", A, Rows,
        Imp(Ne(Id("a"), Id("b")), AllMember("j", J, Columns,
            Or(Equal(K("a", "j"), Num(0)), Equal(K("b", "j"), Num(0))))));

    private static Formula ProductChord()
    {
        var row = Id("k");
        var sum = Sum("j", Columns, Multiply(Abs(Call("k", Id("j"))),
            Chord(Call("z", Id("j")), Call("q", Id("j")))));
        var bound = Le(Chord(Character("z", row), Character("q", row)), sum);
        return F.Disp(All("J", Id("Type"), All("C", Call("Finset", J),
            Phases(All("k", Arrow(J, Integers), bound)))));
    }

    private static Formula WeightedChord()
    {
        var total = Sum("a", Rows, Multiply(Multiplier(),
            Chord(Character("z", Row("a")), Character("q", Row("a")))));
        var energy = Sum("j", Columns, Multiply(Weight(),
            Square(Chord(Call("z", Id("j")), Call("q", Id("j"))))));
        var bound = Le(Square(total), Multiply(ColumnEnergy(), energy));
        return F.Disp(Family(Phases(WeightsAndRows(All("lambda", Arrow(A, Reals),
            Imp(PositiveWeights(), Imp(NonnegativeMultipliers(), bound)))))));
    }

    private static Formula MultiplierBound()
    {
        var energy = ColumnEnergy();
        var total = Sum("a", Rows, Multiply(Multiplier(), Delta()));
        var bound = Le(Div(Square(total), Multiply(Multiply(Num(2), W), energy)), D);
        return F.Disp(Family(All("gamma", Arrow(J, Reals), WeightsAndRows(All("lambda", Arrow(A, Reals),
            Imp(PositiveWeights(), Imp(NonnegativeMultipliers(), Imp(Relations(),
                Imp(Lt(Num(0), W), Imp(Lt(Num(0), energy), bound)))))))));
    }

    private static Formula DisjointBound()
    {
        var rowEnergy = Sum("j", Columns, Div(Square(K("a", "j")), Weight()));
        var total = Sum("a", Rows, Div(Square(Delta()), rowEnergy));
        var bound = Le(Multiply(Div(Num(1), Multiply(Num(2), W)), total), D);
        return F.Disp(Family(All("gamma", Arrow(J, Reals), WeightsAndRows(Imp(PositiveWeights(),
            Imp(Relations(), Imp(NonzeroRows(), Imp(DisjointRows(), Imp(Lt(Num(0), W), bound)))))))));
    }
}
