using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SpacetimeDensitySchattenSubadditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/milekhinadamskapreskill2025observable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational pure state of three qubits violates Schatten subadditivity for a qubit observed at two times.",
        H("Temporal Schatten subadditivity is false"), Blocks(
            Paragraph(Text(
                "All Fin indices are zero based. Matrix multiplication is written with a star, conjugate transpose with a superscript H (ᴴ), "
                    + "and Matrix.kronecker denotes ⊗ₖ. Matrix.trace is the ordinary trace. A matrix numeral one is the identity on its stated index type. "
                    + "The symbols !![a,b;c,d] and ![a,b] denote a two-by-two matrix and a two-entry vector, respectively. "
                    + "Complex casts and function types are displayed explicitly.")),
            Node("claim", "Conjecture 1: temporal Schatten subadditivity", ClaimFormula(),
                "Section IV, item 9, Conjecture 1, equation (25), asserts the displayed inequality for every finite-dimensional spacetime density matrix and every real p > 1. "
                    + "The correlation antecedent is equation (9), with the operator order of equation (4). U is the whole-system evolution from the factorization a × abar at time 0 to b × bbar at time t; "
                    + "the two adjoint equations express its unitarity. The matrix rho is positive semidefinite with trace one. No positivity or Hermiticity is required of T. "
                    + "The operation schattenNorm is footnote a's Schatten norm: the trace of (Mᴴ M)^(p/2), raised to 1/p. "
                    + "PartialTraceMutualInformation.partialTraceLeft traces out a, and PartialTraceMutualInformation.partialTraceRight traces out b.",
                AssessedProvenance.FromLiterature(Source)),
            Node("witnessPsi", "A rational qubit vector", PsiFormula(),
                "The vector has real rational coordinates in the computational basis and squared norm (63² + 16²)/65² = 1. It supplies the qubit amplitudes for the temporal correlation in equations (4) and (9).",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessV", "A rational qubit rotation", VFormula(),
                "The real matrix is orthogonal because 4² + 3² = 5² and its columns are orthogonal. Acting on witnessPsi gives the vector (12/13, −5/13).",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessJointPsi", "The initial three-qubit vector", JointPsiFormula(),
                "The first coordinate is the observed qubit Q; the other coordinates are the control qubits R and S. For x = (q,(r,s)), the amplitude is (Z^r witnessPsi)_q/2, "
                    + "where D5.S3.Quantum.FiniteDimensional.qubitZ is the diagonal matrix with entries 1 and −1. Summing over the four control sectors gives a unit vector.",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessRho", "The pure initial density matrix", RhoFormula(),
                "PureStateHandshake.rankOneDensity takes the outer product of a vector with its conjugate. Thus this density matrix is positive semidefinite and has trace one on Q × (R × S).",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessBlock", "The controlled rotation blocks", BlockFormula(),
                "For the control values c = (r,s), the block is Z^s witnessV Z^r. The phase before the rotation depends on R, and the phase after it depends on S. Every block is unitary.",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessU", "The whole-system controlled evolution", UFormula(),
                "Matrix.blockDiagonal acts on Q × (R × S), with one qubit block for each pair of control values. It leaves both control coordinates fixed and applies the corresponding block to Q.",
                AssessedProvenance.FromRepo(Source)),
            Node("witnessT", "The diagonal spacetime matrix", TFormula(),
                "The row and column index is the pair of observed qubit values at times 0 and t. The four diagonal entries, in order (0,0), (0,1), (1,0), (1,1), are 3024/4225, 945/4225, 576/4225 and −320/4225. "
                    + "Their sum is one. The negative last entry prevents this spacetime matrix from being a positive density matrix.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("temporal-schatten-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The three-qubit example contradicts Conjecture 1"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A and B are the same qubit Q at times 0 and t, with R and S as its complement at both times. The two control qubits dephase the observable insertions at both ends of the correlation. "
                        + "Writing psi = witnessPsi and V = witnessV, the resulting Kirkwood–Dirac weights are q(i,j) = psi(i) V(j,i) (V psi)(j). They are the four diagonal entries of witnessT. "
                        + "The initial density matrix and the controlled evolution satisfy equation (9) for all qubit observables in the order of equation (4). "
                        + "The left partial trace is diag(144/169,25/169), and the right partial trace is diag(3969/4225,256/4225). "
                        + "At p = 2, schattenNorm(witnessT,2) = sqrt(10471777/17850625), the left marginal norm is sqrt(21361/28561), and the right marginal norm is sqrt(15818497/17850625). "
                        + "Consequently 1 + schattenNorm(witnessT,2) ≤ 177/100 < 180/100 ≤ sqrt(21361/28561) + sqrt(15818497/17850625), contradicting the proposed inequality."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("milekhin-adamska-preskill-2025-spacetime-schatten-subadditivity"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("temporal-schatten-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ClaimFormula()
    {
        Formula a = F.Id("a"), abar = F.Id("abar"), b = F.Id("b"), bbar = F.Id("bbar"),
            rho = F.Id("rho"), u = F.Id("U"), t = F.Id("T"), p = F.Id("p"),
            oa = F.Id("OA"), ob = F.Id("OB");
        Formula input = Product(a, abar), output = Product(b, bbar), temporal = Product(a, b);
        Formula correlation = All("OA", MatrixOf(a, a), All("OB", MatrixOf(b, b),
            Equal(Trace(Mul(t, Kronecker(oa, ob))),
                Trace(Mul(Mul(Mul(Mul(rho, Kronecker(oa, Identity(abar))), Adjoint(u)),
                    Kronecker(ob, Identity(bbar))), u)))));
        Formula inequality = LeqTo(
            Add(Call("schattenNorm", Call("PartialTraceMutualInformation.partialTraceLeft", t), p),
                Call("schattenNorm", Call("PartialTraceMutualInformation.partialTraceRight", t), p)),
            Add(D(1), Call("schattenNorm", t, p)));
        Formula body = All("rho", MatrixOf(input, input), All("U", MatrixOf(output, input),
            All("T", MatrixOf(temporal, temporal), All("p", Reals,
                Imp(Call("Matrix.PosSemidef", rho), Imp(Equal(Trace(rho), D(1)),
                    Imp(Equal(Mul(Adjoint(u), u), D(1)), Imp(Equal(Mul(u, Adjoint(u)), D(1)),
                        Imp(correlation, Imp(Less(D(1), p), inequality))))))))));
        return IffTo(Named("claim"), All("a", Named("Type"), All("abar", Named("Type"),
            All("b", Named("Type"), All("bbar", Named("Type"), Instances(body, a, abar, b, bbar))))));
    }

    private static Formula PsiFormula() => Equal(
        Typed(Named("witnessPsi"), Arrow(Qubit, Complexes)),
        Vector(ComplexRatio(D(6, 3), D(6, 5)), ComplexRatio(D(1, 6), D(6, 5))));

    private static Formula VFormula() => Equal(Typed(Named("witnessV"), MatrixOf(Qubit, Qubit)),
        MatrixLiteral(ComplexRatio(D(4), D(5)), ComplexRatio(D(3), D(5)),
            ComplexRatio(new Formula.Negate(D(3)), D(5)), ComplexRatio(D(4), D(5))));

    private static Formula JointPsiFormula()
    {
        Formula x = F.Id("x"), controls = Call("Prod.snd", x);
        Formula r = Call("Fin.val", Call("Prod.fst", controls));
        Formula value = new Formula.Fraction(
            Apply(Call("Matrix.mulVec", Power(QubitZ, r), Named("witnessPsi")), Call("Prod.fst", x)), D(2));
        return Equal(Typed(Named("witnessJointPsi"), Arrow(ThreeQubits, Complexes)),
            LambdaOf("x", ThreeQubits, value));
    }

    private static Formula RhoFormula() => Equal(Typed(Named("witnessRho"), MatrixOf(ThreeQubits, ThreeQubits)),
        Call("PureStateHandshake.rankOneDensity", Named("witnessJointPsi")));

    private static Formula BlockFormula()
    {
        Formula c = F.Id("c"), r = Call("Fin.val", Call("Prod.fst", c)),
            s = Call("Fin.val", Call("Prod.snd", c));
        return Equal(Typed(Named("witnessBlock"), Arrow(TwoQubits, MatrixOf(Qubit, Qubit))),
            LambdaOf("c", TwoQubits, Mul(Mul(Power(QubitZ, s), Named("witnessV")), Power(QubitZ, r))));
    }

    private static Formula UFormula() => Equal(Typed(Named("witnessU"), MatrixOf(ThreeQubits, ThreeQubits)),
        Call("Matrix.blockDiagonal", Named("witnessBlock")));

    private static Formula TFormula()
    {
        Formula x = F.Id("x");
        Formula entries = MatrixLiteral(Typed(D(3, 0, 2, 4), Complexes), D(9, 4, 5),
            D(5, 7, 6), new Formula.Negate(D(3, 2, 0)));
        Formula value = new Formula.Fraction(
            Apply(Parenthesized(entries), Call("Prod.fst", x), Call("Prod.snd", x)), D(4, 2, 2, 5));
        return Equal(Typed(Named("witnessT"), MatrixOf(TwoQubits, TwoQubits)),
            Call("Matrix.diagonal", LambdaOf("x", TwoQubits, value)));
    }

    private static Formula Named(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (string part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Qubit => Call("Fin", D(2));
    private static Formula TwoQubits => Product(Qubit, Qubit);
    private static Formula ThreeQubits => Product(Qubit, TwoQubits);
    private static Formula QubitZ => Named("D5.S3.Quantum.FiniteDimensional.qubitZ");
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula MatrixOf(Formula rows, Formula cols) => Call("Matrix", rows, cols, Complexes);
    private static Formula Identity(Formula index) => Typed(D(1), MatrixOf(index, index));
    private static Formula Trace(Formula matrix) => Call("Matrix.trace", matrix);
    private static Formula Adjoint(Formula matrix) => Power(matrix, Named("H"));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Kronecker(Formula a, Formula b) => Call("Matrix.kronecker", a, b);
    private static Formula ComplexRatio(Formula numerator, Formula denominator) =>
        new Formula.Fraction(Typed(numerator, Complexes), denominator);
    private static Formula Vector(Formula a, Formula b) => Seq(Bang, OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula MatrixLiteral(Formula a, Formula b, Formula c, Formula d) =>
        Seq(Bang, Bang, OpenBracket, a, Comma, Sp, b, Semi, Sp, c, Comma, Sp, d, CloseBracket);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instances(Formula body, params Formula[] carriers)
    {
        for (int i = carriers.Length - 1; i >= 0; i--)
            body = Seq(OpenBracket, Call("Fintype", carriers[i]), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", carriers[i]), CloseBracket, Sp, body);
        return body;
    }
    private static Formula Mul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
