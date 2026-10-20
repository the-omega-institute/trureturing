using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class SpinThreeHalvesClassicalBasisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rudzinski2024extremequantumness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every orthonormal basis of spin 3/2 has mean one-qubit anticoherence at least 1/9, attained by an explicit classical basis.",
        H("The most classical orthonormal basis of spin 3/2"),
        Blocks(
            Node("dicke", "The normalized three-qubit Dicke embedding", "dicke", DickeFormula(),
                "Index the angular-momentum basis by k = 0,1,2,3, with magnetic quantum number 3/2 - k. "
                    + "The map dicke sends its kth vector to the normalized uniform superposition of three-qubit bit strings with k ones. "
                    + "Thus a bit string with k ones has amplitude psi_k/sqrt(binom(3,k)). "
                    + "The binomial coefficient counts distinct bit strings, and val denotes the natural value of a bit index. "
                    + "This is the normalized Dicke identification of Eqs. (6)-(8)."),
            Node("reduced-state", "The one-qubit reduced state", "reducedState", ReducedStateFormula(),
                "Write rho_1(psi) for reducedState(psi). The indices a and b are the first two qubits; c and d index the remaining qubit. "
                    + "The sum traces out the first two qubits from the outer product of dicke(psi) with its adjoint, as in Eq. (12). "
                    + "The definition applies to every vector psi; for a unit vector it is a density matrix."),
            Node("anticoherence", "One-qubit anticoherence", "anticoherence", AnticoherenceFormula(),
                "Denote anticoherence(psi) by A_1(psi). It is twice one minus the purity of rho_1(psi), the t = 1 case of Eqs. (13)-(14). "
                    + "The real part is explicit in the definition; rho_1(psi) is Hermitian, so the trace of its square is real. "
                    + "No normalization hypothesis is imposed on the definition."),
            Node("basis-anticoherence", "Mean anticoherence of the columns", "basisAnticoherence", BasisAnticoherenceFormula(),
                "Denote basisAnticoherence(U) by B_1(U). The vector U e_i is the ith column, where e_i is the standard coordinate vector. "
                    + "The definition takes the arithmetic mean of the four column anticoherences, as in Eq. (15). "
                    + "It is defined for every complex four-by-four matrix; when U is unitary, its columns form an orthonormal basis."),
            Node("classical-basis", "The attaining matrix of Eq. (21)", "classicalBasis", ClassicalBasisFormula(),
                "The matrix classicalBasis is the matrix U_4^c of Eq. (21). The displayed local constants are complex numbers, "
                    + "with positive real square roots embedded in the complex field and i the imaginary unit. "
                    + "The algebraic value of omega is exp(2 pi i/3). Columns are ordered in the angular-momentum coordinates used by the Dicke embedding."),
            Node("claim", "The minimum and its attainment", "claim", ClaimDefinitionFormula(),
                "Every orthonormal basis of the spin-3/2 space has mean one-qubit anticoherence at least 1/9. "
                    + "The matrix of Eq. (21) is unitary and attains 1/9. These are the three parts of claim, "
                    + "expressing Conjecture 1 with the columns of a unitary matrix as the basis vectors."),
            Result()),
        []));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("spin-three-halves-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Result() =>
        Describe.Lean(
            DescribeId.Create("spin-three-halves-result"), DeclarationHandle.Create(Prefix + "result"),
            H("The sharp lower bound and the classical basis"),
            StatementSource.FromAuthor(Disp(Named("claim"))), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For a unit vector psi, let p(psi) be its spin expectation vector, with components the real expectations of the spin-3/2 operators J_x, J_y and J_z. "
                        + "The Dicke reduction gives A_1(psi) = 1 - 4|p(psi)|^2/9. Consequently, for a unitary U, "
                        + "B_1(U) = 1 - S(U)/9, where S(U) is the sum of the squared lengths of the four column polarizations. "
                        + "Multiplying the first column by the inverse determinant changes neither its reduced state nor its spin expectations, "
                        + "and reduces the bound to matrices of determinant one.")),
                Paragraph(Text(
                    "The six-by-six matrix of two-by-two minors acts on the second exterior power of C^4. "
                        + "Its unitarity and its preservation of the signed form coupling complementary two-element subsets make it real orthogonal in a fixed exterior basis. "
                        + "Its columns therefore give a real orthonormal six-frame, grouped into three pairs x_k,y_k. "
                        + "An isometry identifies this real space with R plus the traceless real symmetric three-by-three matrices; "
                        + "write x_k = (s_k,X_k) and y_k = (t_k,Y_k) in these coordinates. "
                        + "The spin action becomes a commutator action, and the zero sum of the column polarizations yields "
                        + "S(U) = 2 sum_{k=1}^3 ||[X_k,Y_k]||_F^2, where [X,Y] = XY - YX and the norm is Frobenius.")),
                Paragraph(Text(
                    "Subtracting the component of Y along X in the Böttcher-Wenzel inequality gives the refinement "
                        + "||[X,Y]||_F^2 <= 2(||X||_F^2 ||Y||_F^2 - <X,Y>_F^2). "
                        + "The frame identities are ||X_k||_F^2 = 1 - s_k^2, ||Y_k||_F^2 = 1 - t_k^2, "
                        + "<X_k,Y_k>_F = -s_k t_k, and sum_{k=1}^3(s_k^2 + t_k^2) = 1. "
                        + "They give S(U) <= 4 sum_{k=1}^3(1 - s_k^2 - t_k^2) = 8, hence B_1(U) >= 1/9.")),
                Paragraph(Text(
                    "For the matrix of Eq. (21), exact evaluation proves unitarity and gives the four spin polarizations "
                        + "(4/3,0,sqrt(2)/3), (-2/3,2sqrt(3)/3,sqrt(2)/3), "
                        + "(-2/3,-2sqrt(3)/3,sqrt(2)/3), and (0,0,-sqrt(2)). "
                        + "Their squared lengths are 2 and their pairwise inner products are -2/3, so they are the vertices of a regular tetrahedron. "
                        + "Thus S = 8 and B_1 = 1/9. This proves the minimum asserted in Conjecture 1."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("rudzinski-burchardt-zyczkowski-2024-spin-three-halves-classical-basis"),
                ResolutionKind.Proved));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula SumOver(string variable, byte size, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Member(F.Id(variable), Fin(size)))), Sp, Parenthesized(body));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula StateType() => new Formula.TypeArrow(Fin(4), Complexes());
    private static Formula MatrixType() => Call("Matrix", Fin(4), Fin(4), Complexes());
    private static Formula UnitaryMatrices() => Call("unitaryGroup", Fin(4), Complexes());
    private static Formula Reduced(Formula psi) => App(new Formula.Subscript(Rho, D(1)), psi);
    private static Formula Anticoherence(Formula psi) =>
        App(new Formula.Subscript(Seq(Mathcal, Grp(F.Id("A"))), D(1)), psi);
    private static Formula BasisAnticoherence(Formula matrix) =>
        App(new Formula.Subscript(Seq(Mathcal, Grp(F.Id("B"))), D(1)), matrix);
    private static Formula Tuple(params Formula[] entries) => Parenthesized(Join(Comma, entries));
    private static Formula Join(Formula separator, Formula[] entries) =>
        Seq([.. entries.SelectMany((entry, index) => index == 0
            ? new[] { entry } : new[] { separator, entry })]);
    private static Formula Entries(params Formula[][] rows) =>
        Seq(Begin, Grp(F.Id("pmatrix")), Join(RowBreak, [.. rows.Select(row => Join(Amp, row))]),
            End, Grp(F.Id("pmatrix")));
    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(Named("let"), Sp, variable, Sp, Colon, Sp, Complexes(), Sp, Colon, Eq, Sp, value,
            Sp, Named("in"), Sp, body);

    private static Formula DickeFormula()
    {
        Formula psi = new Formula.Psi(), a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula k = Add(Add(Call("val", a), Call("val", b)), Call("val", c));
        Formula amplitude = new Formula.Fraction(new Formula.Subscript(psi, k), Root(Call("binom", D(3), k)));
        return Disp(All(psi, StateType(), All(a, Fin(2), All(b, Fin(2), All(c, Fin(2),
            Equal(Call("dicke", psi, Tuple(a, b, c)), amplitude))))));
    }

    private static Formula ReducedStateFormula()
    {
        Formula psi = new Formula.Psi(), a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula term = Mul(Call("dicke", psi, Tuple(a, b, c)),
            Seq(Overline, Grp(Call("dicke", psi, Tuple(a, b, d)))));
        return Disp(All(psi, StateType(), All(c, Fin(2), All(d, Fin(2),
            Equal(new Formula.Subscript(Reduced(psi), Seq(c, d)), SumOver("a", 2, SumOver("b", 2, term)))))));
    }

    private static Formula AnticoherenceFormula()
    {
        Formula psi = new Formula.Psi();
        Formula purity = Call("Re", Call("tr", new Formula.Power(Parenthesized(Reduced(psi)), D(2))));
        return Disp(All(psi, StateType(), Equal(Anticoherence(psi),
            Mul(D(2), Parenthesized(Subtract(D(1), purity))))));
    }

    private static Formula BasisAnticoherenceFormula()
    {
        Formula u = F.Id("U"), i = F.Id("i");
        Formula column = Mul(u, new Formula.Subscript(F.Id("e"), i));
        return Disp(All(u, MatrixType(), Equal(BasisAnticoherence(u),
            Mul(new Formula.Fraction(D(1), D(4)), SumOver("i", 4, Anticoherence(column))))));
    }

    private static Formula ClassicalBasisFormula()
    {
        Formula nu = Nu, tau = Tau, omega = Omega;
        Formula rootTwo = Root(D(2)), rootThree = Root(D(3));
        Formula tauValue = Subtract(D(3), Mul(D(2), rootTwo));
        Formula omegaSquared = new Formula.Power(omega, D(2));
        Formula matrix = Entries(
            [D(1), D(1), D(1), Mul(tau, rootThree)],
            [nu, Mul(nu, omega), Mul(nu, omegaSquared), D(0)],
            [nu, Mul(nu, omegaSquared), Mul(nu, omega), D(0)],
            [tau, tau, tau, new Formula.Negate(rootThree)]);
        Formula value = Mul(new Formula.Fraction(D(1), Root(Mul(D(1, 8), Parenthesized(tauValue)))), matrix);
        return Disp(Let(nu, Mul(rootThree, Parenthesized(Subtract(D(2), rootTwo))),
            Let(tau, tauValue, Let(omega, new Formula.Fraction(Add(new Formula.Negate(D(1)),
                Mul(F.Id("i"), rootThree)), D(2)), Equal(Named("classicalBasis"), value)))));
    }

    private static Formula ClaimBody()
    {
        Formula u = F.Id("U"), classical = Named("classicalBasis");
        Formula bound = All(u, MatrixType(), Implies(Member(u, UnitaryMatrices()),
            AtMost(new Formula.Fraction(D(1), D(9)), BasisAnticoherence(u))));
        return And(bound, And(Member(classical, UnitaryMatrices()),
            Equal(BasisAnticoherence(classical), new Formula.Fraction(D(1), D(9)))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
