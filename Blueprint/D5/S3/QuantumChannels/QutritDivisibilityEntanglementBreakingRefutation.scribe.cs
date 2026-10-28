using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class QutritDivisibilityEntanglementBreakingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/QutritDivisibilityEntanglementBreakingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/davaloszimanpineda2019divisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A divisible qutrit channel lies outside the closure of P-divisible dynamical endpoints and is not entanglement breaking.",
        H("Divisibility does not force entanglement breaking for qutrits"),
        Blocks(
            Definition("unitary-channel", "IsUnitaryChannel", "Unitary conjugation", UnitaryFormula(),
                "A complex-linear map on three by three matrices is unitary when one unitary matrix U conjugates every input X. "
                    + "Subtype.val explicitly includes U in the ambient complex matrix space. "
                    + "This is the unitary-channel definition in Section 2.1, TeX lines 252–254.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("divisible", "IsDivisible", "Two nonunitary channel factors", DivisibleFormula(),
                "The map t factors as t1 after t2, where both factors are completely positive and trace preserving and neither is a unitary conjugation. "
                    + "Section 2.1, TeX lines 256–261, defines indivisibility by the absence of such a factorization. "
                    + "The displayed predicate requires two nonunitary factors; it does not include the source's separate convention about unitary channels in lines 262–263.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("positive-tp", "IsPositiveTP", "Positive trace-preserving maps", PositiveTPFormula(),
                "A positive trace-preserving map sends every positive semidefinite matrix to a positive semidefinite matrix and preserves the complex trace of every input. "
                    + "Positivity and trace preservation are the conditions in Section 2.1, TeX lines 235–240; complete positivity is not required here.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("p-divisible-map", "IsPDivisibleMap", "P-divisible dynamics", DynamicsFormula(),
                "The family e starts at the identity, is a channel at every nonnegative real time, and is continuous on the nonnegative half-line in matrix-unit coordinates. "
                    + "For every pair of times with 0 ≤ t < s, a positive trace-preserving map v carries e(t) to e(s) by composition. "
                    + "The coordinate matrix is LinearMap.toMatrix in the standard matrix basis on both sides. "
                    + "Section 2.2, TeX lines 281–295, gives the dynamical-map and P-divisibility notions. "
                    + "The composition condition also applies at singular times, without requiring an inverse.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("p-divisible-set", "pDivisibleSet", "Limits of dynamical endpoints", EndpointSetFormula(),
                "A map T belongs to this set when its matrix-unit coordinate matrix lies in the topological closure of the coordinate matrices of all nonnegative-time endpoints of P-divisible families E. "
                    + "Thus finite endpoints and their limits are included. Section 2.2, TeX lines 336–339, expresses membership through approximation to a dynamical endpoint, including infinite time. "
                    + "The displayed set uses the preceding composition condition even when an endpoint is singular.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("entanglement-breaking", "IsEntanglementBreaking", "Destruction of bipartite entanglement", EntanglementBreakingFormula(),
                "For every natural ancillary dimension n and every positive semidefinite matrix rho of complex trace one on the product of Fin n and Fin 3, "
                    + "the identity amplification of t sends rho into the separable cone. The identity acts on the ancillary factor and t on the qutrit factor. "
                    + "The source's Theorem 6, TeX lines 1237–1241, uses entanglement breaking in its qubit conclusion; its proof starts from the associated bipartite state in lines 1244–1249.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "claim", "The qutrit assertion", ClaimFormula(),
                "Every completely positive trace-preserving qutrit map with two nonunitary channel factors and outside the displayed endpoint closure is asserted to be entanglement breaking. "
                    + "This is a precise qutrit reading of the higher-dimensional question in the abstract, TeX lines 162–164. "
                    + "The source's Theorem 6, lines 1237–1241, concerns qubits.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A divisible qutrit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write Eᵢⱼ for the matrix units and I for the three by three identity. "
                            + "Use the three matrices (E₀₁ − E₁₀)/√2, (E₀₂ − E₂₀)/√2 and (E₁₂ − E₂₁)/√2 as Kraus operators for W. "
                            + "Use I/√2 together with all nine Eᵢⱼ/√6 as Kraus operators for D. "
                            + "Expanding their Kraus sums gives W(X) = (Tr(X)I − Xᵀ)/2 and D(X) = X/2 + Tr(X)I/6. "
                            + "Their composition is T(X) = 5Tr(X)I/12 − Xᵀ/4.")),
                    Paragraph(Text(
                        "For each of these two Kraus families, the sum of K†K is I. Hence W and D are completely positive and trace preserving. "
                            + "The products of a Kraus operator of D with one of W form a Kraus family for T, proving its complete positivity; successive trace preservation proves that T preserves trace. "
                            + "A Kraus representation of an arbitrary completely positive map also shows that it commutes with conjugate transpose.")),
                    Paragraph(Text(
                        "Unitary conjugation preserves the trace of the square of E₀₀, which equals one. "
                            + "But W(E₀₀) has diagonal (0,1/2,1/2), and D(E₀₀) has diagonal (2/3,1/6,1/6); in each case the trace of the square is 1/2. "
                            + "Thus neither W nor D is a unitary channel, and T = D ∘ W is divisible.")),
                    Paragraph(Text(
                        "For a Hermiticity-preserving map, conjugating its matrix-unit coordinate matrix exchanges the two indices within each row and each column. "
                            + "This simultaneous reindexing preserves the determinant. Its determinant therefore equals its complex conjugate and is real.")),
                    Paragraph(Text(
                        "For a P-divisible family E, the determinant is continuous on nonnegative times and starts at one. "
                            + "If its real part were negative at a time u, the intermediate value theorem would give an earlier nonnegative time z with zero real part. "
                            + "Reality makes the determinant itself zero at z. The factorization E(u) = v ∘ E(z) makes the coordinate determinant at u a product with this zero factor, a contradiction. "
                            + "Every endpoint consequently has real nonnegative determinant. The set of coordinate matrices with zero imaginary part of the determinant and nonnegative real part is closed, "
                            + "so the same constraint holds throughout the endpoint closure.")),
                    Paragraph(Text(
                        "To calculate the determinant of T, reorder the nine matrix units as three diagonal units followed by the pairs (E₀₁,E₁₀), (E₀₂,E₂₀) and (E₁₂,E₂₁). "
                            + "The diagonal block has diagonal entries 1/6 and off-diagonal entries 5/12, with determinant 1/16. "
                            + "Each of the three remaining blocks is the two by two matrix with zero diagonal and both off-diagonal entries −1/4. "
                            + "Their combined determinant is −(1/4)⁶, and the full determinant is −(1/4)⁸. "
                            + "It is negative, so T is outside the endpoint closure.")),
                    Paragraph(Text(
                        "Let a = (e₀ ⊗ e₀ + e₁ ⊗ e₁ + e₂ ⊗ e₂)/√3 and let Ω = aa†. "
                            + "This maximally entangled density matrix is positive semidefinite and has trace one. "
                            + "Direct expansion of the matrix entries gives real quadratic value −1/9 on a for the partial transpose of (id ⊗ T)(Ω). "
                            + "If T were entanglement breaking, that output would lie in the separable cone. Every member of this cone has positive semidefinite partial transpose, "
                            + "whose real quadratic values are nonnegative. The value −1/9 is a contradiction.")),
                    Paragraph(Text(
                        "Applying the asserted implication to the channel T, its nonunitary factorization and its exclusion from the endpoint closure would make T entanglement breaking. "
                            + "The preceding negative quadratic value disproves that conclusion, and therefore negates the assertion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula UnitaryFormula()
    {
        Formula ambient = Typed(At(Qualified("Subtype", "val"), X("U")), QutritMatrix());
        return All("t", QutritMap(), IffOf(LocalCall("IsUnitaryChannel", X("t")),
            Some("U", At(Qualified("Matrix", "unitaryGroup"), FinOf(D(3)), Complexes()),
                All("X", QutritMatrix(), Equal(At(X("t"), X("X")),
                    Multiply(Multiply(ambient, X("X")), At(Qualified("Matrix", "conjTranspose"), ambient)))))));
    }

    private static Formula DivisibleFormula() => All("t", QutritMap(),
        IffOf(LocalCall("IsDivisible", X("t")), Some("t1", QutritMap(), Some("t2", QutritMap(),
            AndOf(CPTP(X("t1")), AndOf(CPTP(X("t2")),
                AndOf(Equal(X("t"), At(Qualified("LinearMap", "comp"), X("t1"), X("t2"))),
                    AndOf(NotOf(LocalCall("IsUnitaryChannel", X("t1"))),
                        NotOf(LocalCall("IsUnitaryChannel", X("t2")))))))))));

    private static Formula PositiveTPFormula() => All("v", QutritMap(),
        IffOf(LocalCall("IsPositiveTP", X("v")), AndOf(
            All("X", QutritMatrix(), Arrow(PSD(X("X")), PSD(At(X("v"), X("X"))))),
            At(Qualified("MatrixMap", "IsTracePreserving"), X("v")))));

    private static Formula DynamicsFormula()
    {
        Formula channels = All("t", Reals(), Arrow(LE(Typed(D(0), Reals()), X("t")), CPTP(At(X("e"), X("t")))));
        Formula continuity = At(Qualified("ContinuousOn"),
            LambdaOf("t", Reals(), CoordinateMatrix(At(X("e"), X("t")))),
            At(Qualified("Set", "Ici"), Typed(D(0), Reals())));
        Formula propagators = All("t", Reals(), All("s", Reals(),
            Arrow(LE(Typed(D(0), Reals()), X("t")), Arrow(LT(X("t"), X("s")),
                Some("v", QutritMap(), AndOf(LocalCall("IsPositiveTP", X("v")),
                    Equal(At(X("e"), X("s")), At(Qualified("LinearMap", "comp"), X("v"), At(X("e"), X("t"))))))))));
        return All("e", DynamicsType(), IffOf(LocalCall("IsPDivisibleMap", X("e")),
            AndOf(Equal(At(X("e"), Typed(D(0), Reals())), Typed(Qualified("LinearMap", "id"), QutritMap())),
                AndOf(channels, AndOf(continuity, propagators)))));
    }

    private static Formula EndpointSetFormula()
    {
        Formula endpoints = SetOf("M", CoordinateMatrixType(),
            Some("E", DynamicsType(), AndOf(LocalCall("IsPDivisibleMap", X("E")),
                Some("t", Reals(), AndOf(LE(Typed(D(0), Reals()), X("t")),
                    Equal(X("M"), CoordinateMatrix(At(X("E"), X("t")))))))));
        return Equal(Local("pDivisibleSet"), SetOf("T", QutritMap(),
            Member(CoordinateMatrix(X("T")), At(Qualified("closure"), endpoints))));
    }

    private static Formula EntanglementBreakingFormula()
    {
        Formula product = Product(FinOf(X("n")), FinOf(D(3)));
        Formula output = At(Qualified("MatrixMap", "kron"),
            Typed(Qualified("LinearMap", "id"), MatrixMapType(FinOf(X("n")), FinOf(X("n")))),
            X("t"), X("rho"));
        return All("t", QutritMap(), IffOf(LocalCall("IsEntanglementBreaking", X("t")),
            All("n", Naturals(), All("rho", MatrixType(product, product),
                Arrow(PSD(X("rho")), Arrow(Equal(At(Qualified("Matrix", "trace"), X("rho")), Typed(D(1), Complexes())),
                    At(Qualified("D5", "S3", "Resource", "CompositeCones", "separableCone"), output)))))));
    }

    private static Formula ClaimFormula() => IffOf(Local("claim"), All("t", QutritMap(),
        Arrow(CPTP(X("t")), Arrow(LocalCall("IsDivisible", X("t")),
            Arrow(NotOf(Member(X("t"), Local("pDivisibleSet"))), LocalCall("IsEntanglementBreaking", X("t")))))));

    private static Formula CoordinateMatrix(Formula map)
    {
        Formula basis = At(Qualified("Matrix", "stdBasis"), Complexes(), FinOf(D(3)), FinOf(D(3)));
        return At(Qualified("LinearMap", "toMatrix"), basis, basis, map);
    }

    private static Formula CoordinateMatrixType() => MatrixType(Product(FinOf(D(3)), FinOf(D(3))), Product(FinOf(D(3)), FinOf(D(3))));
    private static Formula QutritMatrix() => MatrixType(FinOf(D(3)), FinOf(D(3)));
    private static Formula QutritMap() => MatrixMapType(FinOf(D(3)), FinOf(D(3)));
    private static Formula DynamicsType() => Arrow(Reals(), QutritMap());
    private static Formula MatrixType(Formula rows, Formula columns) => At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula MatrixMapType(Formula input, Formula output) => At(Qualified("MatrixMap"), input, output, Complexes());
    private static Formula PSD(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula CPTP(Formula map) => At(Qualified("D5", "S3", "QuantumChannels", "CoPRelativeQuantumnessRefutation", "IsCPTP"), map);
    private static Formula Local(string name) => Qualified("D5", "S3", "QuantumChannels", "QutritDivisibilityEntanglementBreakingRefutation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula NotOf(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula AndOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula element, Formula set) => new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
}
