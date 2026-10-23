using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class MarginalApproximationWorstFidelityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/sudmarshallwangrieffelwudarski2022dual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of single-site process marginals has squared fidelity at least four to the minus N, with equality for cyclic wire permutations on at least two qubits.",
        H("The sharp fidelity bound for marginal process approximations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("process-cptp"),
                DeclarationHandle.Create(Module + ".IsProcessCPTP"),
                H("Completely positive trace-preserving process matrices"),
                StatementSource.FromAuthor(Disp(ProcessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A Pauli string a assigns one of the four Pauli matrices to each qubit. "
                    + "The operator tensorOp assembles their tensor product. The matrix χ, written chi in the formulas, "
                    + "is completely positive and trace preserving when it is positive semidefinite and "
                    + "the sum of χ(a,b) times the ordered Pauli products P_b P_a is the identity on the qubits. "
                    + "This is the process representation of main.tex lines 234–249, extended to Pauli strings. "
                    + "The Pauli basis is unnormalized; taking the trace of this identity gives trace χ equal to one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-site-marginal"),
                DeclarationHandle.Create(Module + ".marginal"),
                H("The partial trace onto one process coordinate"),
                StatementSource.FromAuthor(Disp(MarginalFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a site k, the entry (i,j) of marginal χ k sums the entries whose row has value i "
                    + "at k and whose column agrees with that row away from k and has value j at k. "
                    + "Function.update changes precisely that coordinate. This is the single-site partial trace "
                    + "used in MATEN, main.tex lines 226–232, and for process matrices in lines 284–287. "
                    + "Each retained coordinate has dimension four. The definition applies to every complex matrix, "
                    + "without a positivity or normalization assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-shift-coefficients"),
                DeclarationHandle.Create(Module + ".shiftCoeff"),
                H("Pauli coefficients of the cyclic wire permutation"),
                StatementSource.FromAuthor(Disp(ShiftCoeffFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The permutation finRotate N cyclically rotates the qubit positions. "
                    + "The coefficient shiftCoeff N a is the trace pairing of the Pauli string a with "
                    + "the transpose of qubitPermutation (finRotate N), divided by two to the power N. "
                    + "The transpose fixes the direction of the wire permutation in this convention. "
                    + "Both the power of two and its inverse are complex numbers. "
                    + "These coefficients specify the pure process matrix used to attain the bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("worst-fidelity-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The universal lower bound and cyclic-shift attainment"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The source conjectures the worst-case fidelity value in main.tex lines 284–290 "
                        + "and computes four to the minus N for a pure process with maximally mixed marginals "
                        + "in lines 292–296. The first conjunct asserts this lower bound for every "
                        + "CPTP process matrix on every positive number N of qubits.")),
                    Paragraph(Text(
                        "The second conjunct specifies an attaining family: for every N at least two, "
                        + "the Pauli expansion with coefficients shiftCoeff N equals the transposed cyclic "
                        + "wire permutation, its rank-one process matrix is CPTP, every marginal is "
                        + "one quarter of the four-dimensional identity, and its squared fidelity with "
                        + "the product of its marginals is exactly four to the minus N. "
                        + "The cyclic-shift construction supplies this attainment assertion. "
                        + "Here productMap forms the tensor product of its matrix arguments, "
                        + "rankOneDensity v has entries v(a) times the complex conjugate of v(b), "
                        + "and sqFidelity is the square of the real part of the trace of "
                        + "the positive square root of √ρ σ √ρ. Its values and the bound are real."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("worst-fidelity-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The lower bound is sharp"),
                StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First consider a probability distribution p on the Pauli strings and write "
                        + "q(k,j) for its marginal at site k. Weighted arithmetic–geometric mean applied "
                        + "with weights q(k,j) and values q(k,j)⁻¹ bounds the reciprocal of "
                        + "the product of q(k,j) to the powers q(k,j) by four. Zero weights contribute "
                        + "zero to the arithmetic sum and one to the geometric product. Consequently "
                        + "each such geometric product is at least one quarter. Factoring the product "
                        + "over strings by their k-th coordinates and applying weighted "
                        + "arithmetic–geometric mean again, now with weights p(x) and values "
                        + "the product of q(k,x(k)) over k, gives an overlap of at least four to the minus N.")),
                    Paragraph(Text(
                        "For a CPTP process χ, tracing its trace-preservation identity and using "
                        + "Pauli trace orthogonality gives trace χ equal to one. Splitting a string "
                        + "into its k-th coordinate and the remaining coordinates identifies marginal χ k "
                        + "with a partial trace and proves its positivity. The product of these "
                        + "marginals is positive: its entries are products of the marginal entries, "
                        + "so induction over sites expresses it as successive Hadamard products of "
                        + "positive matrices pulled back along coordinate maps. Denote this product by χ_MA.")),
                    Paragraph(Text(
                        "Tensor products preserve matrix multiplication, adjoints, diagonal matrices "
                        + "and identities, hence products of unitary matrices are unitary. "
                        + "Splitting off site k also expresses a product unitary as a Kronecker product; "
                        + "the partial trace therefore transforms by conjugation with its k-th factor. "
                        + "Choose a unitary U(k) diagonalizing each marginal, let V be their tensor "
                        + "product, and put Ψ = Vᴴ χ V. Positivity and trace one make p(x) = Re Ψ(x,x) "
                        + "a probability distribution. The marginals of p are exactly the eigenvalues "
                        + "of the corresponding marginals of χ. In this basis the product of the "
                        + "marginals is diagonal, with diagonal entries the products of those "
                        + "eigenvalues. Cyclic invariance of trace then identifies the classical "
                        + "overlap with Re tr(χ χ_MA), proving the same lower bound for this trace.")),
                    Paragraph(Text(
                        "For positive matrices ρ and σ, put A = √ρ σ √ρ and S = √A. "
                        + "These matrices are positive. Cyclic invariance gives tr A = tr(ρσ), "
                        + "and S² = A. For a positive matrix the real trace of its square is at "
                        + "most the square of its real trace. Thus Re tr(ρσ) is at most "
                        + "(Re tr S)², which is sqFidelity ρ σ. Applying this inequality with "
                        + "ρ = χ and σ = χ_MA completes the universal lower bound.")),
                    Paragraph(Text(
                        "For attainment, Pauli trace orthogonality expands the transposed cyclic "
                        + "wire permutation with precisely the coefficients shiftCoeff N. "
                        + "It is a permutation matrix and hence unitary. Hermiticity of the Pauli "
                        + "strings turns the conjugated coefficient sum into its adjoint. "
                        + "Multiplying the two expansions proves trace preservation of the "
                        + "positive rank-one matrix χ = rankOneDensity (shiftCoeff N).")),
                    Paragraph(Text(
                        "To compute its k-th marginal, expand the trace pairing as a sum over "
                        + "qubit strings x of the product, over sites l, of the entry of σ indexed by a(l) "
                        + "in row x(l) and column x(finRotate N l). "
                        + "Split a into its value i at k and a string z on the other N−1 sites. "
                        + "In the product of this sum and its complex conjugate, summing each "
                        + "coordinate of z uses Pauli completeness: the sum of σ_a(u,v) times "
                        + "the conjugate of σ_a(u′,v′) is two when both pairs agree and zero otherwise. "
                        + "The resulting constraints identify x(l) with y(l) and the rotated "
                        + "coordinates for every l other than k. Since N is at least two, the "
                        + "predecessor of k differs from k, so these constraints also identify "
                        + "x(k) with y(k). Only x = y remains, with factor two to the power N−1. "
                        + "The two coordinates k and finRotate N k are distinct. Summing them "
                        + "uses Pauli orthogonality, giving two for i = j and zero otherwise; "
                        + "the remaining N−2 coordinates contribute two to the power N−2. "
                        + "The full contraction is therefore (2ᴺ)² times one quarter of the "
                        + "Kronecker delta. Multiplication by the squared coefficient normalization "
                        + "gives marginal χ k = I₄/4.")),
                    Paragraph(Text(
                        "Finally let c = 1/4ᴺ as a real number. The product of the marginals "
                        + "is (c : ℂ) times the identity. Trace one normalizes the coefficient "
                        + "vector, so its rank-one density χ satisfies χ² = χ and √χ = χ. "
                        + "The positive square root of (c : ℂ)χ is (√c : ℂ)χ. Substituting "
                        + "these identities into sqFidelity, taking the trace and using trace χ = 1 "
                        + "gives (√c)² = c. This supplies all four attainment assertions for every N at least two."))),
                DescribeRole.Theorem))));

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula N => F.Id("N");
    private static Formula Chi => F.Id("chi");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Strings => new Formula.TypeArrow(Fin(N), Fin(D(4)));
    private static Formula Qubits => new Formula.TypeArrow(Fin(N), Fin(D(2)));
    private static Formula ProcessMatrices => Call("Matrix", Parenthesized(Strings), Parenthesized(Strings), Complexes);
    private static Formula WireMatrices => Call("Matrix", Parenthesized(Qubits), Parenthesized(Qubits), Complexes);
    private static Formula SiteMatrices => Call("Matrix", Fin(D(4)), Fin(D(4)), Complexes);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        Multiply(Parenthesized(left), Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound => new Formula.Fraction(Typed(D(1), Reals), Power(Typed(D(4), Reals), N));
    private static Formula PauliString(Formula a) => Call("tensorOp",
        LambdaOf(F.Id("k"), Fin(N), Call("sigma", App(a, F.Id("k")))));
    private static Formula Shift => App(Qualified("Matrix", "transpose"), Call("qubitPermutation", Call("finRotate", N)));
    private static Formula ShiftDensity => Call("rankOneDensity", Call("shiftCoeff", N));
    private static Formula MarginalProduct(Formula matrix) => Call("productMap",
        App(Qualified("Function", "const"), Fin(N), Fin(D(4))), Call("marginal", matrix));

    private static Formula ProcessFormula() => All(N, Naturals, All(Chi, ProcessMatrices,
        IffTo(Call("IsProcessCPTP", Chi), And(App(Qualified("Matrix", "PosSemidef"), Chi),
            Equal(SumOver(F.Id("a"), Strings, SumOver(F.Id("b"), Strings,
                    Smul(App(Chi, F.Id("a"), F.Id("b")),
                        Mul(PauliString(F.Id("b")), PauliString(F.Id("a")))))),
                Typed(D(1), WireMatrices))))));

    private static Formula MarginalFormula() => All(N, Naturals, All(Chi, ProcessMatrices,
        All(F.Id("k"), Fin(N), All(F.Id("i"), Fin(D(4)), All(F.Id("j"), Fin(D(4)),
            Equal(Call("marginal", Chi, F.Id("k"), F.Id("i"), F.Id("j")),
                SumOver(F.Id("y"), Strings, Call("ite", Equal(App(F.Id("y"), F.Id("k")), F.Id("i")),
                    App(Chi, F.Id("y"), App(Qualified("Function", "update"), F.Id("y"), F.Id("k"), F.Id("j"))),
                    Typed(D(0), Complexes)))))))));

    private static Formula ShiftCoeffFormula() => All(N, Naturals, All(F.Id("a"), Strings,
        Equal(Typed(Call("shiftCoeff", N, F.Id("a")), Complexes),
            Mul(App(Qualified("Inv", "inv"), Power(Typed(D(2), Complexes), N)),
                App(Qualified("Matrix", "trace"), Mul(PauliString(F.Id("a")), Shift))))));

    private static Formula ClaimFormula()
    {
        Formula lowerBound = All(N, Naturals, Imp(LE(Typed(D(1), Naturals), N),
            All(Chi, ProcessMatrices, Imp(Call("IsProcessCPTP", Chi),
                LE(Bound, Call("sqFidelity", Chi, MarginalProduct(Chi)))))));
        Formula expansion = Equal(SumOver(F.Id("a"), Strings,
            Smul(Call("shiftCoeff", N, F.Id("a")), PauliString(F.Id("a")))), Shift);
        Formula marginals = All(F.Id("k"), Fin(N), Equal(Call("marginal", ShiftDensity, F.Id("k")),
            Smul(new Formula.Fraction(Typed(D(1), Complexes), Typed(D(4), Complexes)), Typed(D(1), SiteMatrices))));
        Formula attainment = All(N, Naturals, Imp(LE(Typed(D(2), Naturals), N),
            And(expansion, And(Call("IsProcessCPTP", ShiftDensity), And(marginals,
                Equal(Call("sqFidelity", ShiftDensity, MarginalProduct(ShiftDensity)), Bound))))));
        return IffTo(Seq(Operatorname, Grp(F.Id("claim"))), And(lowerBound, attainment));
    }
}
