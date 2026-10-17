using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ConditionalDomainSubalgebraRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/parzygnat2021conditionaldistributions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit density matrix with invertible marginals has a conditional domain that is not closed under multiplication.",
        H("Two-qubit conditional domains need not be subalgebras"), Blocks(
            Paragraph(Text(
                "The first tensor factor is A and the second is B, both equal to the complex two-by-two matrix algebra. "
                    + "Fin(2) consists of 0 and 1; pairs index the computational basis (00, 01, 10, 11). "
                    + "Matrix multiplication and the Kronecker product act in this order of factors, and 1 is the identity matrix. "
                    + "Every sum below ranges over Fin(2). The partial trace over B has (a,c)-entry "
                    + "the sum of X((a,b),(c,b)) over b; the partial trace over A has (b,d)-entry "
                    + "the sum of X((a,b),(a,d)) over a. The displayed lambda expressions give these matrices explicitly. "
                    + "Commute(X,Y) means XY = YX. DensityState consists of positive semidefinite complex matrices "
                    + "of trace one, and nu.1 is the underlying matrix. IsUnit means invertible. "
                    + "StarSubalgebra denotes a complex unital subalgebra closed under conjugate transpose; "
                    + "its cast to Set is its carrier.")),
            Node("conditionalDomainB", "The conditional domain in B", ConditionalDomainBFormula(),
                "Definition 5.5 defines B_nu as the set of B for which tr_B(nu(1 tensor B)) "
                    + "commutes with the marginal rho = tr_B(nu). The first lambda expression is rho, "
                    + "and the second is tr_B(nu(1 tensor B)). This definition applies to any joint matrix nu, "
                    + "without positivity or invertibility assumptions."),
            Node("conditionalDomainA", "The conditional domain in A", ConditionalDomainAFormula(),
                "Definition 5.5 defines A_nu as the set of A for which tr_A((A tensor 1)nu) "
                    + "commutes with the marginal sigma = tr_A(nu). The first lambda expression is sigma, "
                    + "and the second is tr_A((A tensor 1)nu). The multiplication order agrees with Definition 5.5, "
                    + "and the definition applies to every joint matrix nu."),
            Node("claim", "The two-qubit subalgebra suspicion", ClaimFormula(),
                "Footnote 13, following Example 5.10, suspects that both conditional domains of a four-by-four "
                    + "density matrix are C*-subalgebras. With two nontrivial factors, both factors are two-by-two matrix algebras. "
                    + "The setting of Corollary 4.5 requires both marginals to be invertible. Thus the statement "
                    + "quantifies over every two-qubit density state with both marginal invertibility conditions "
                    + "and asks for a unital star subalgebra with carrier B_nu and another with carrier A_nu. "
                    + "In finite dimension every linear subspace is norm closed, so these unital star subalgebras "
                    + "are C*-subalgebras. Lemma 5.8 already gives the operator-system properties of the domains."),
            Describe.Lean(
                DescribeId.Create("conditional-domain-subalgebra-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Failure of multiplication closure with invertible marginals"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In the basis (00, 01, 10, 11), take nu = (1/32) [[11,1,1,0], [1,7,0,-1], "
                            + "[1,0,9,-1], [0,-1,-1,5]]. Let v_0 = (1,1,0,0)^T, v_1 = (1,0,1,0)^T, "
                            + "v_2 = (0,1,0,-1)^T and v_3 = (0,0,1,-1)^T. Then nu equals "
                            + "(diag(9,5,7,3) + v_0 v_0^dagger + v_1 v_1^dagger + v_2 v_2^dagger "
                            + "+ v_3 v_3^dagger)/32. Each of the four outer products is positive semidefinite "
                            + "and has rank one. The diagonal term is positive semidefinite as well. "
                            + "Consequently nu is positive semidefinite, and its trace is (11+7+9+5)/32 = 1.")),
                    Paragraph(Text(
                        "The marginal rho = tr_B(nu) is diag(9/16,7/16), and sigma = tr_A(nu) "
                            + "is diag(5/8,3/8). Their diagonal entries are nonzero, so both marginals are invertible.")),
                    Paragraph(Text(
                        "For B = [[a,b],[c,d]], the matrix tr_B(nu(1 tensor B)) equals "
                            + "(1/32) [[11a+b+c+7d,a-d], [a-d,9a-b-c+5d]]. "
                            + "The matrix units E_01 = [[0,1],[0,0]] and E_10 = [[0,0],[1,0]] "
                            + "both give diag(1/32,-1/32), which commutes with rho. Thus both belong to B_nu. "
                            + "Their product is E_00 = [[1,0],[0,0]]. For E_00 the transformed matrix "
                            + "has off-diagonal entries 1/32, so it does not commute with rho, whose diagonal "
                            + "entries are distinct. Hence E_00 does not belong to B_nu.")),
                    Paragraph(Text(
                        "A subalgebra containing E_01 and E_10 must contain their product E_00. "
                            + "Therefore no unital star subalgebra has carrier B_nu for this density state. "
                            + "This contradicts the first of the two carrier equalities in claim, "
                            + "while both marginal invertibility hypotheses hold."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("parzygnat-2021-two-qubit-conditional-domain-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("conditional-domain-subalgebra-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => name == "nu" ? Nu : F.Id(name);
    private static Formula Named(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp([.. items]));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), FinTwo())), Sp, Parenthesized(body));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinTwo() => Call("Fin", D(2));
    private static Formula JointIndices() => Product(FinTwo(), FinTwo());
    private static Formula MatrixOf(Formula indices) => Call("Matrix", indices, indices, Complexes());
    private static Formula QubitMatrices() => MatrixOf(FinTwo());
    private static Formula JointMatrices() => MatrixOf(JointIndices());
    private static Formula Subalgebras() => Call("StarSubalgebra", Complexes(), QubitMatrices());
    private static Formula Carrier(Formula subalgebra) => Typed(subalgebra, Call("Set", QubitMatrices()));
    private static Formula Value(Formula state) => Seq(state, Dot, D(1));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Kronecker(Formula left, Formula right) => Call("Matrix.kronecker", left, right);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula ConditionalDomain(string name, Formula predicate) =>
        Seq(OpenBrace, V(name), Colon, Sp, QubitMatrices(), Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula TraceB(Formula matrix) =>
        LambdaOf("a", FinTwo(), LambdaOf("c", FinTwo(), SumOver("b",
            At(matrix, Pair(V("a"), V("b")), Pair(V("c"), V("b"))))));

    private static Formula TraceA(Formula matrix) =>
        LambdaOf("b", FinTwo(), LambdaOf("d", FinTwo(), SumOver("a",
            At(matrix, Pair(V("a"), V("b")), Pair(V("a"), V("d"))))));

    private static Formula ConditionalDomainBFormula() => All("nu", JointMatrices(),
        EqTo(Call("conditionalDomainB", V("nu")), ConditionalDomain("B",
            Call("Commute", TraceB(V("nu")),
                TraceB(Mul(V("nu"), Kronecker(Typed(D(1), QubitMatrices()), V("B"))))))));

    private static Formula ConditionalDomainAFormula() => All("nu", JointMatrices(),
        EqTo(Call("conditionalDomainA", V("nu")), ConditionalDomain("A",
            Call("Commute", TraceA(V("nu")),
                TraceA(Mul(Kronecker(V("A"), Typed(D(1), QubitMatrices())), V("nu")))))));

    private static Formula ClaimFormula()
    {
        Formula matrix = Value(V("nu"));
        Formula carriers = And(
            EqTo(Carrier(V("S")), Call("conditionalDomainB", matrix)),
            EqTo(Carrier(V("T")), Call("conditionalDomainA", matrix)));
        return IffTo(Named("claim"), All("nu", Call("DensityState", JointIndices()),
            Imp(Call("IsUnit", TraceB(matrix)), Imp(Call("IsUnit", TraceA(matrix)),
                Some("S", Subalgebras(), Some("T", Subalgebras(), carriers))))));
    }
}
