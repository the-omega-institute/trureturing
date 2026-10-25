using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CyclicPowerLatticeDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Dvd(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula N(Formula d) => Call("dimension", d);
    private static Formula A(Formula d) => Call("leadingCoeff", Call("relationPolynomial", d));
    private static Formula AbsA(Formula d) => Call("natAbs", A(d));
    private static Formula V(Formula d, Formula j) => Call("power", d, j);
    private static Formula Lattice(Formula d, Formula l) => Call("lattice", d, l);
    private static Formula Quotient(Formula d, Formula l) => Call("SuccessiveQuotient", d, l);

    private static Formula CompleteStatement()
    {
        var d = I("d");
        var j = I("j");
        var p = I("p");
        var l = I("l");
        var n = I("n");
        var length = I("L");
        var low = All(Equal(V(d, Call("value", j)), Call("standard", N(d), j)),
            B("j", Call("Fin", N(d))));
        var whole = All(Iff(Equal(Call("evaluation", d, p), Num(0)),
            Dvd(Call("relationPolynomial", d), p)), B("p", Call("Polynomial", I("Int"))));
        var initial = Equal(Lattice(d, N(d)), Call("coordinateZ", N(d)));
        var kernel = All(Iff(Mem(Call("zsmul", n, V(d, l)), Lattice(d, l)), Dvd(A(d), n)),
            B("n", I("Int")));
        var successive = All(Imp(Le(N(d), l), And(kernel,
            And(Equal(Call("addOrderOf", Call("quotientGenerator", d, l)), AbsA(d)),
            And(Call("Finite", Quotient(d, l)),
                Equal(Call("NatCard", Quotient(d, l)), AbsA(d)))))), B("l", I("Nat")));
        var total = All(Imp(Le(N(d), length),
            And(Call("Finite", Call("RelativeQuotient", d, length)),
                Equal(Call("relIndex", Call("coordinateZ", N(d)), Lattice(d, length)),
                    Call("pow", AbsA(d), Call("natSub", length, N(d)))))), B("L", I("Nat")));
        return All(And(low, And(whole, And(initial, And(successive, total)))),
            B("d", I("Data")));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The whole primitive relation determines exact finite growth of every rational cyclic power lattice.",
        H("Integral growth in rational cyclic power coordinates"),
        Blocks(
            Paragraph(Text("Let N be any positive natural number and T any N by N rational matrix. "
                + "The vector b=root(N) has coordinate one at zero and zero elsewhere. "
                + "For i and j in Fin N, powerMatrix(T)(i,j) is coordinate i of T raised to j applied to b. "
                + "Write K=powerMatrix(T), and assume det K is nonzero. "
                + "Let q be a primitive integer polynomial with positive leading coefficient A. "
                + "Assume its coefficientwise rational image is C(A) times the characteristic polynomial of T. "
                + "These are exactly the fields of Data: dimension N, positivity, T, the determinant condition, "
                + "q, primitivity, positive leading coefficient and the displayed polynomial relation. "
                + "Primitivity means that the coefficients generate the unit ideal. The whole polynomial may "
                + "be reducible. No symmetry, sign, spectral stability or irreducibility premise is imposed, "
                + "and A=1 is included. The dimension is the full dimension of T.")),
            Paragraph(Math(Disp(All(Equal(Call("mapToRat", Call("relationPolynomial", I("d"))),
                Multiply(Call("C", A(I("d"))), Call("charpoly", Call("matrix", I("d"))))),
                B("d", I("Data")))))),
            Paragraph(Text("For d in Data define time(d)=K inverse times T times K and "
                + "power(d,j)=time(d) raised to j applied to root(N), for every natural j. "
                + "The inverse and the coordinate changes are rational matrix operations on this same K. "
                + "For a rational polynomial p, rationalEvaluation(d,p) is K inverse applied to p(T)b. "
                + "For an integer polynomial p, evaluation(d,p) first maps every coefficient to the rationals "
                + "and then uses rationalEvaluation. It is an integer linear map into the rational vector space. "
                + "In particular evaluation of the monomial c X raised to j is c times power(d,j).")),
            Paragraph(Text("For every natural L, lattice(d,L) is the integer span of power(d,j) "
                + "for j less than L inside the single additive group of rational N-vectors. "
                + "The notation coordinateZ(N) means the image of all integer N-vectors under "
                + "coordinatewise inclusion into rational N-vectors. It is defined independently of the powers. "
                + "SuccessiveQuotient(d,l) is lattice(d,l+1) modulo the subgroup of its elements "
                + "that belong to lattice(d,l). Its distinguished quotientGenerator is the class of power(d,l). "
                + "RelativeQuotient(d,L) similarly denotes lattice(d,L) modulo its subgroup of elements "
                + "belonging to coordinateZ(N). All quotients therefore use subgroups of their actual larger "
                + "lattices. The relative index has the smaller subgroup as its first argument. "
                + "Neither an index in the ambient rational space nor a zero cardinality convention "
                + "is used as evidence of finiteness.")),
            Describe.Lean(DescribeId.Create("cyclic-power-integral-growth"),
                DeclarationHandle.Create("D5/S1/Recurrence/CyclicPowerLattice.cyclic_power_lattice"),
                H("Whole relation kernel, successive orders and finite relative index"),
                StatementSource.FromAuthor(Disp(CompleteStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here dimension(d)=d.N, matrix(d)=d.T, relationPolynomial(d)=d.q, "
                        + "and standard(N,j) is the rational vector with one at j and zero elsewhere. "
                        + "Fin(N) is the set of indices less than N and value(j) is its natural index. "
                        + "zsmul is multiplication by an integer, NatCard is natural cardinality, "
                        + "Finite asserts finite type cardinality, and natSub is natural subtraction. "
                        + "The quotient order and cardinality are natAbs(A); since A is positive this is A. "
                        + "Every l and L at least N is included. In particular L=N gives index one. "
                        + "The theorem also identifies every integral polynomial annihilating the actual "
                        + "input with an integral multiple of the whole q, rather than a polynomial "
                        + "vanishing at only one chosen root.")),
                    Paragraph(Text("The conjugacy calculation gives power(d,j)=K inverse applied to T raised "
                        + "to j times b. For j less than N the corresponding column of K therefore gives "
                        + "the jth standard vector. A rational polynomial of degree below N evaluates "
                        + "to its coefficient vector in these coordinates. Divide an arbitrary rational "
                        + "polynomial by the monic characteristic polynomial. Cayley-Hamilton removes "
                        + "the multiple, while low-degree coordinate independence forces a vanishing "
                        + "remainder to be zero. Scaling by the nonzero A and applying the supplied "
                        + "primitive-divisibility theorem over the fraction field gives exactly the "
                        + "integral multiples of q. The Gauss step is Polynomial.IsPrimitive."
                        + "dvd_of_fraction_map_dvd_fraction_map, with coefficient domain Int and "
                        + "fraction field Rat. It needs primitivity of q, without irreducibility.")),
                    Paragraph(Text("For l at least N the polynomial q times X raised to l-N has degree l "
                        + "and leading coefficient A. Its lower terms show that A times power(d,l) "
                        + "belongs to lattice(d,l). Conversely an integer n times that new power lying "
                        + "in the earlier lattice gives an annihilator n X raised to l minus a polynomial "
                        + "of degree below l. If n is nonzero its leading coefficient is n, so the whole "
                        + "integral annihilator characterization forces A to divide n. The n=0 case "
                        + "is included directly. Thus the next quotient generator has exactly order A.")),
                    Paragraph(Text("The successor lattice is the sum of the earlier lattice and the "
                        + "integer span of the new power. Hence that generator spans the entire "
                        + "successive quotient. Its positive finite order gives an explicit equivalence "
                        + "between a finite index set and its cyclic subgroup, proving quotient finiteness "
                        + "and cardinality A. The first N powers span coordinateZ(N). Multiplying the "
                        + "successive relative indices with AddSubgroup.relIndex_mul_relIndex yields "
                        + "A raised to L-N at every later length. Its nonzero value also gives finiteness "
                        + "of the full relative quotient."))),
                DescribeRole.Theorem),
            Paragraph(Text("For an acquired positive-link path the retained origin is x_star=T raised "
                + "to 2N applied to b. This result supplies the algebraic lattice "
                + "part of the finite-menu chronology argument once its actual K is proved invertible "
                + "and its earned whole q has the stated normalization. Deriving that native invertibility "
                + "from the path remains a separate correspondence. The positive stable vector s, "
                + "the rational coordinate bound R, the integer C, bounded lattice-point counting, "
                + "word reversal and the same affine baseline are additional steps. This theorem alone "
                + "does not assert the all-length H less than A threshold or the equal-length collision "
                + "at N+A C. The retained acquired phase, actual observation calls, historical versus "
                + "advanced current field, continued service rights, archives and simultaneous numerical "
                + "resources likewise require their own hypotheses and proofs. Removing an old length "
                + "input in a different chronology task does not alter the retained-length assertion.")))));
}
