using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBMinimalEnvironmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three actor moments determine a minimal invertible Hermitian environment.",
        H("Exact realization of the three PB moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("pb-three-moment-minimal-realization"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Algebra/PBMinimalEnvironment.pb_three_moment_minimal_realization"),
            H("Feasibility, minimal dimension, labelled Gram quotient, and physical blocks"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix three complex two by two matrices M0, M1 and M2. " +
                    "The four by four block Gram matrix Gamma has block rows (M0,M1) and (M1,M2). " +
                    "Write r for rank M0 and k for rank Gamma. The actor coordinates remain the two " +
                    "original complex coordinates. For any natural number m, an actual realization " +
                    "uses a Hermitian m by m matrix D and a two by m coupling V, with ker D contained " +
                    "in ker V. The inverse used in the moments is the actual Moore–Penrose inverse " +
                    "D dagger, including for singular D. The three equalities are M0=V V*, " +
                    "M1=V D dagger V*, and M2=V (D dagger)^2 V*. Every actual realization " +
                    "automatically makes all three moments Hermitian. All kernels are complex.")),
                Paragraph(Text("An actual realization exists exactly when Gamma is positive " +
                    "semidefinite and the kernels of M0 and M2 coincide. Under these conditions an " +
                    "actual realization exists with D invertible on exactly k coordinates. In " +
                    "every actual realization k is at most rank D, which is at most m. Moreover " +
                    "rank M2=r and r <= k <= 2r <= 4. The result includes m=0 and k=0; on the zero " +
                    "space the unique endomorphism is the identity and its own inverse.")),
                Paragraph(Text("For every actual realization set F=V* and G=(D dagger) F. The " +
                    "quotient by ker Gamma has dimension k. The unique labelled identification " +
                    "with ran F plus ran G sends the class of (a,b) to F a + G b. On every pair " +
                    "of representatives its target inner product is exactly z* Gamma w. " +
                    "Consequently the quotient form descends, is positive definite, and makes " +
                    "this identification unitary. It keeps both actor labels and does not assert " +
                    "uniqueness of the environment inverse or an intertwining on the whole space.")),
                Paragraph(Text("For the minimal witness, take any Hermitian B, two real diagonal " +
                    "entries s1 and s2, and either original orientation sigma=1 or sigma=-1. " +
                    "On the direct sum of the actor and environment, t has block rows (B,V) " +
                    "and (V*,D), c is diag(1,2) plus a zero block, and s is diag(s1,s2) plus a " +
                    "zero block. These are Hermitian, as is the original response matrix " +
                    "g=(sigma i/2)(ct-tc)+s. A specified Schur block H equals the actual Schur " +
                    "expression precisely when H=B-M1.")),
                Paragraph(Text("The Penrose identities identify the original support and place " +
                    "both column families inside ran D. For sufficiency a positive Gram factor " +
                    "gives the two column families on their joint span. Equal end kernels give " +
                    "an injective partial operator carrying the first family to the second. " +
                    "Its prescribed block is symmetric by the Hermitian mixed moment. Add the " +
                    "orthogonal complement projection with an imaginary coefficient: the " +
                    "imaginary part of the quadratic form detects every complement component of " +
                    "a kernel vector. The remaining vector vanishes by injectivity of the " +
                    "partial operator. The determinant polynomial is therefore nonzero, so a " +
                    "real coefficient gives an invertible Hermitian extension. Its inverse and " +
                    "the first family give the actual matrix witness in an orthonormal basis.")),
                Paragraph(Text("This is the three-moment result in PB continuation §30.1. The " +
                    "Gram factor and orthogonal projection are standard finite linear algebra, " +
                    "and the actual inverse uses the repository's finite Penrose construction. " +
                    "The result makes no claim about P2 or PB transfer or classification."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula m0 = Id("M0"), m1 = Id("M1"), m2 = Id("M2"), d = Id("D"), v = Id("V");
        Formula m = Id("m"), r = Id("r"), k = Id("k");
        var gamma = Call("momentGram", m0, m1, m2);
        var actorMatrix = Call("Matrix", Num(2), Num(2), Id("Complex"));
        Formula Dims(Formula n) => Call("Matrix", n, n, Id("Complex"));
        Formula Coupling(Formula n) => Call("Matrix", Num(2), n, Id("Complex"));
        Formula Rank(Formula x) => Call("rank", x);
        Formula KerOf(Formula x) => Call("ker", x);
        Formula Realizes() => Call("Realizes", d, v, m0, m1, m2);
        Formula Rel(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
        Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
        Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
        Formula All(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
        Formula Ex(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
        var admissible = And(Call("PosSemidef", gamma), Equal(KerOf(m0), KerOf(m2)));
        var arbitrary = Ex("m", Id("Nat"), Ex("D", Dims(m), Ex("V", Coupling(m), Realizes())));
        var witness = Ex("D", Dims(k), Ex("V", Coupling(k),
            And(Call("IsUnit", d), And(Realizes(), Call("PhysicalCompatibility", d, v, m1)))));
        var ranks = And(Equal(Rank(m2), r),
            And(Rel(r, k), And(Rel(k, Multiply(Num(2), r)), Rel(Multiply(Num(2), r), Num(4)))));
        var lower = All("m", Id("Nat"), All("D", Dims(m), All("V", Coupling(m), Imp(Realizes(),
            And(And(Call("IsHermitian", m0), And(Call("IsHermitian", m1), Call("IsHermitian", m2))),
                And(Rel(k, Rank(d)), And(Rel(Rank(d), m), Call("LabeledGramIdentification", d, v, m0, m1, m2))))))));
        var laws = And(new Formula.Logic(arbitrary, FormulaLogicOperator.Iff, admissible),
            And(Imp(admissible, And(witness, ranks)), lower));
        var indices = Imp(And(Equal(r, Rank(m0)), Equal(k, Rank(gamma))), laws);
        return All("M0", actorMatrix, All("M1", actorMatrix, All("M2", actorMatrix,
            All("r", Id("Nat"), All("k", Id("Nat"), indices)))));
    }
}
