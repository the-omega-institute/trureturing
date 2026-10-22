using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class StabilizerBatteryDegreeDifferenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/ghoshkonarfrancicapalsende2025stabilizer");
    private static readonly Formula N = F.Id("N"), K = F.Id("K"), i = F.Id("i"), j = F.Id("j");
    private static readonly Formula g = F.Id("g"), t = F.Id("t");
    private static readonly Formula Nat = Blackboard("N"), Real = Blackboard("R"), Complex = Blackboard("C"), Int = Blackboard("Z");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourteen-qubit circulant stabilizer batteries with degree pairs (4,8) and (2,6) have the same degree difference but store different work at time π/4.",
        H("Equal degree differences do not determine stored work"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stabilizer-battery-degree-difference-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The degree-difference assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Equations (1) and (2) define the periodic circulant generators and their Hamiltonian sum. "
                        + "The mathematical symbols A, S and H denote the neighbourhood relation, its Pauli generators and that sum. "
                        + "The centre carries X, each neighbour carries Z, and every other site carries the identity. "
                        + "The maximum even degree is M(N). All arithmetic on natural degrees, including subtraction, is natural arithmetic; K/2 is the integer quotient.")),
                    Paragraph(Text(
                        "A State N is a complex vector on binary functions on Fin N, and an Operator N is a matrix on those indices. "
                        + "G(N,H,g) says that g has squared norm one and minimizes the real energy among all vectors v of squared norm one. "
                        + "The initial density is the outer product of g and its complex conjugate. The charging exponential and the real trace expression W are the unitary evolution and work of Section II, Figures of merit. "
                        + "Complex.ofReal explicitly embeds a real scalar into the complex numbers. The star on a vector is coordinatewise conjugation; the superscript H on a matrix is conjugate transpose.")),
                    Paragraph(Text(
                        "The Section III remark reports unchanged work at fixed degree difference for the investigated sizes N at most ten outside multiples of four, and leaves the larger-size conclusion unresolved. "
                        + "The assertion displayed here quantifies over all sizes N greater than two not divisible by four, all four positive interior even degrees, all ground states g and h, and every nonnegative real time t. "
                        + "Interior means K + 2 at most M(N). Nat.dist is the absolute difference of two natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stabilizer-battery-degree-difference-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A fourteen-qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Call("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take N = 14, battery-charger pairs (Kb,Kc) = (4,8) and (Lb,Lc) = (2,6), and t = π/4. "
                        + "The maximum degree is 12, all four degrees are positive and interior, and both differences equal four. "
                        + "For each battery choose the negative-eigenvalue graph-state vector below. In its exponent, val is the natural representative of a binary residue. "
                        + "The linear term changes every graph-generator eigenvalue to minus one. Its normalization and the Hermitian-involution energy bound make it a ground state of the corresponding battery.")),
                    Display(GroundVectorFormula()),
                    Paragraph(Text(
                        "For each degree K the generators commute and square to the identity. Thus their charging exponential factors as follows, with factors in increasing Fin N order. "
                        + "The real cosine and sine are explicitly embedded into the complex scalars.")),
                    Display(EvolutionFormula()),
                    Paragraph(Text(
                        "At time π/4 each factor is (I - i S)/sqrt(2). Let J be the increasing list of charger indices whose generators anticommute with the battery generator at i. "
                        + "The conjugated generator Qᵢ is the battery generator multiplied by the factors -i S at indices in J. "
                        + "For both degree pairs, J has four elements at every i.")),
                    Display(QuarterFormula()),
                    Paragraph(Text(
                        "Write a Pauli word as a scalar times X to a binary vector x followed by Z to a binary vector z, and let the binary adjacency matrix of the battery be Γ. "
                        + "Its graph-state expectation is a binary character sum. It vanishes unless the Z-part equals Γ applied to the X-part, that is z = Γx. "
                        + "For (4,8), every Qᵢ passes this test and its phase gives expectation -1. For (2,6), every Qᵢ fails the test and has expectation zero. "
                        + "The work is the sum over i of one plus the real part of this expectation, so the two work values are 0 and 14. "
                        + "Equal degree difference therefore does not suffice, even with both endpoint degrees excluded."))),
                DescribeRole.Theorem)
        )));

    private static Formula ClaimFormula()
    {
        Formula Kb = F.Id("Kb"), Kc = F.Id("Kc"), Lb = F.Id("Lb"), Lc = F.Id("Lc"), h = F.Id("h");
        Formula conclusion = All("g", State(N), All("h", State(N),
            Arrow(Call("G", N, Call("H", N, Kb), g),
                Arrow(Call("G", N, Call("H", N, Lb), h),
                    All("t", Real, Arrow(Leq(D(0), t),
                        Equal(Call("W", N, Kb, Kc, g, t), Call("W", N, Lb, Lc, h, t))))))));
        Formula degrees = All("Kb", Nat, All("Kc", Nat, All("Lb", Nat, All("Lc", Nat,
            Arrow(Interior(Kb), Arrow(Interior(Kc), Arrow(Interior(Lb), Arrow(Interior(Lc),
                Arrow(NotEqual(Kb, Kc), Arrow(NotEqual(Lb, Lc),
                    Arrow(Equal(Qualified("Nat", "dist", Kc, Kb), Qualified("Nat", "dist", Lc, Lb)),
                        conclusion)))))))))));
        Formula assertion = All("N", Nat, Arrow(Less(D(2), N),
            Arrow(new Formula.Not(Parenthesized(Seq(D(4), Sp, Mid, Sp, N))), degrees)));
        return Geometry(Hamiltonian(MaximumDegree(GroundCondition(WorkDefinition(
            Equivalence(Call("claim"), assertion))))));
    }

    private static Formula Geometry(Formula body)
    {
        Formula d = F.Id("d");
        Formula neighbours = And(NotEqual(i, j), Some("d", Nat,
            And(Mem(d, Qualified("Finset", "range", Quotient(K, D(2)))),
                Or(Equal(Property(j, "val"), Mod(Add(Property(i, "val"), Parenthesized(Add(d, D(1)))), N)),
                    Equal(Property(i, "val"), Mod(Add(Property(j, "val"), Parenthesized(Add(d, D(1)))), N))))));
        Formula relation = LambdaOf("N", Nat, LambdaOf("K", Nat,
            LambdaOf("i", Fin(N), LambdaOf("j", Fin(N), neighbours))));
        Formula label = LambdaOf("j", Fin(N), Letter(K, i, j));
        Formula generator = LambdaOf("N", Nat, LambdaOf("K", Nat,
            LambdaOf("i", Fin(N), Call("wordOp", label))));
        return Let("A", All("N", Nat, Arrow(Nat, Arrow(Fin(N), Arrow(Fin(N), F.Id("Prop"))))), relation,
            Let("S", All("N", Nat, Arrow(Nat, Arrow(Fin(N), Operator(N)))), generator, body));
    }

    private static Formula Hamiltonian(Formula body) =>
        Let("H", All("N", Nat, Arrow(Nat, Operator(N))),
            LambdaOf("N", Nat, LambdaOf("K", Nat, SumOf("i", Fin(N), Call("S", N, K, i)))), body);

    private static Formula MaximumDegree(Formula body) => Let("M", Arrow(Nat, Nat),
        LambdaOf("N", Nat, If(Call("Even", N), Subtract(N, D(2)), Subtract(N, D(1)))), body);

    private static Formula Interior(Formula degree) =>
        And(Call("Even", degree), And(Leq(D(2), degree), Leq(Add(degree, D(2)), Call("M", N))));

    private static Formula GroundCondition(Formula body)
    {
        Formula H = F.Id("H"), v = F.Id("v");
        Formula condition = And(Equal(NormSquareSum(g), D(1)),
            All("v", State(N), Arrow(Equal(NormSquareSum(v), D(1)), Leq(Energy(H, g), Energy(H, v)))));
        return Let("G", All("N", Nat, Arrow(Operator(N), Arrow(State(N), F.Id("Prop")))),
            LambdaOf("N", Nat, LambdaOf("H", Operator(N), LambdaOf("g", State(N), condition))), body);
    }

    private static Formula WorkDefinition(Formula body)
    {
        Formula Kb = F.Id("Kb"), Kc = F.Id("Kc"), U = F.Id("U"), density = new Formula.Subscript(Rho, D(0));
        Formula expression = Qualified("Complex", "re", Qualified("Matrix", "trace",
            Mul(Parenthesized(Subtract(Mul(Mul(U, density), Adjoint(U)), density)), Call("H", N, Kb))));
        Formula value = Let(density, Operator(N), Qualified("Matrix", "vecMulVec", g, Call("star", g)),
            Let("U", Operator(N), Evolution(N, Kc, t), expression));
        return Let("W", All("N", Nat, Arrow(Nat, Arrow(Nat, Arrow(State(N), Arrow(Real, Real))))),
            LambdaOf("N", Nat, LambdaOf("Kb", Nat, LambdaOf("Kc", Nat,
                LambdaOf("g", State(N), LambdaOf("t", Real, value))))), body);
    }

    private static Formula GroundVectorFormula()
    {
        Formula b = F.Id("b");
        Formula exponent = Add(SumOf("i", Fin(N), Property(At(b, i), "val")),
            SumOf("i", Fin(N), SumOverSet("j",
                Qualified("Finset", "filter", LambdaOf("j", Fin(N),
                    And(Less(i, j), Call("A", N, K, i, j))), Qualified("Finset", "univ")),
                Mul(Property(At(b, i), "val"), Property(At(b, j), "val")))));
        Formula coefficient = Pow(Parenthesized(OfReal(Qualified("Real", "sqrt", Pow(Typed(D(2), Real), N)))), Negate(D(1)));
        Formula vector = LambdaOf("b", Arrow(Fin(N), Call("ZMod", D(2))),
            Mul(coefficient, Pow(Typed(Negate(D(1)), Complex), exponent)));
        Formula properties = And(Call("G", N, Call("H", N, K), g),
            All("i", Fin(N), Equal(Qualified("Matrix", "mulVec", Call("S", N, K, i), g), Negate(g))));
        return Geometry(Hamiltonian(GroundCondition(All("N", Nat, All("K", Nat,
            Let("g", State(N), vector, properties))))));
    }

    private static Formula EvolutionFormula()
    {
        Formula factor = Subtract(Smul(OfReal(Qualified("Real", "cos", t)), Typed(D(1), Operator(N))),
            Smul(Mul(Qualified("Complex", "I"), OfReal(Qualified("Real", "sin", t))), Call("S", N, K, j)));
        Formula product = Qualified("List", "prod", Qualified("List", "ofFn", LambdaOf("j", Fin(N), factor)));
        return Geometry(Hamiltonian(All("N", Nat, All("K", Nat, All("t", Real,
            Equal(Evolution(N, K, t), product))))));
    }

    private static Formula QuarterFormula()
    {
        Formula Kb = F.Id("Kb"), Kc = F.Id("Kc"), U = F.Id("U"), J = F.Id("J");
        Formula battery = Call("S", N, Kb, i), charger = Call("S", N, Kc, j);
        Formula k = F.Id("k");
        Formula sign = Seq(Prod, Underscore, Grp(k, Colon, Sp, Fin(N)), Sp,
            Parenthesized(Call("sgn", Letter(Kb, i, k), Letter(Kc, j, k))));
        Formula indices = Qualified("List", "filter", LambdaOf("j", Fin(N),
            Call("decide", Equal(sign, Typed(Negate(D(1)), Int)))),
            Qualified("List", "ofFn", LambdaOf("j", Fin(N), j)));
        Formula product = Qualified("List", "prod", Qualified("List", "map",
            LambdaOf("j", Fin(N), Smul(Negate(Qualified("Complex", "I")), charger)), J));
        return Geometry(Hamiltonian(All("N", Nat, All("Kb", Nat, All("Kc", Nat, All("i", Fin(N),
            Let("U", Operator(N), Evolution(N, Kc, Quotient(Pi, D(4))),
                Let("J", Call("List", Fin(N)), indices,
                    Equal(Mul(Mul(Adjoint(U), battery), U), Mul(battery, product))))))))));
    }

    private static Formula NormSquareSum(Formula vector) => SumOf("b", Arrow(Fin(N), Fin(D(2))),
        Pow(Seq(Vert, Sp, At(vector, F.Id("b")), Sp, Vert), D(2)));
    private static Formula Letter(Formula degree, Formula centre, Formula coordinate) =>
        If(Equal(coordinate, centre), Qualified("Pauli", "X"),
            If(Call("A", N, degree, centre, coordinate), Qualified("Pauli", "Z"), Qualified("Pauli", "I")));
    private static Formula Energy(Formula H, Formula vector) => Qualified("Complex", "re",
        Call("dotProduct", Call("star", vector), Qualified("Matrix", "mulVec", H, vector)));
    private static Formula Evolution(Formula size, Formula degree, Formula time) => Qualified("NormedSpace", "exp",
        Smul(Negate(Parenthesized(Mul(Qualified("Complex", "I"), OfReal(time)))), Call("H", size, degree)));
    private static Formula OfReal(Formula value) => Typed(Qualified("Complex", "ofReal", Typed(value, Real)), Complex);
    private static Formula Blackboard(string letter) => Seq(Mathbb, Grp(F.Id(letter)));
    private static Formula State(Formula size) => Call("State", size);
    private static Formula Operator(Formula size) => Call("Operator", size);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(F.Id(name)))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) => Seq(F.Id(owner), Dot, Call(name, args));
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(F.Id(name), type), Comma, Sp, body);
    private static Formula Arrow(Formula domain, Formula codomain) => Parenthesized(Seq(domain, Sp, To, Sp, codomain));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, body);
    private static Formula Let(string name, Formula type, Formula value, Formula body) => Let(F.Id(name), type, value, body);
    private static Formula Let(Formula name, Formula type, Formula value, Formula body) =>
        Seq(F.Id("let"), Sp, Typed(name, type), Sp, Colon, Eq, Sp, Parenthesized(value), Semi, Sp, body);
    private static Formula If(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(F.Id("if"), Sp, test, Sp, F.Id("then"), Sp, yes, Sp, F.Id("else"), Sp, no));
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Lor, Sp, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => Seq(left, Sp, Iff, Sp, Parenthesized(right));
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Mul(Formula left, Formula right) => Multiply(left, right);
    private static Formula Negate(Formula value) => new Formula.Negate(value);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Quotient(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Mod(Formula value, Formula modulus) => Qualified("Nat", "mod", value, modulus);
    private static Formula Smul(Formula scalar, Formula value) => Qualified("SMul", "smul", scalar, value);
    private static Formula Adjoint(Formula value) => Qualified("Matrix", "conjTranspose", value);
    private static Formula Property(Formula value, string name) => Seq(Parenthesized(value), Dot, F.Id(name));
    private static Formula SumOf(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula SumOverSet(string name, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, set), Sp, Parenthesized(body));
    private static DocumentBlock Display(Formula formula) => new DocumentBlock.DisplayFormula(formula);
}
