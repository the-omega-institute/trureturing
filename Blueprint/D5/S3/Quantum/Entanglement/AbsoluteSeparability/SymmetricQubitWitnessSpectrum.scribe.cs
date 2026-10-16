using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class SymmetricQubitWitnessSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/champagnejohnstonmacdonaldpipes2022spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The spectra of symmetric two-qubit entanglement witnesses are characterized "
            + "by two sharp inequalities on their three ordered eigenvalues.",
        H("Spectra of symmetric two-qubit witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-qubit-witness-coherent"),
                DeclarationHandle.Create(Prefix + "coherent"),
                H("Coherent vectors in Dicke coordinates"),
                StatementSource.FromAuthor(Disp(CoherentFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In the orthonormal Dicke basis e00, (e01 + e10)/sqrt(2), e11 "
                        + "of the symmetric subspace of C2 tensor C2, the vector "
                        + "v tensor v has these three coordinates. The factor sqrt(2) "
                        + "comes from the normalization of the middle basis vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-qubit-witness-predicate"),
                DeclarationHandle.Create(Prefix + "IsSymmetricWitness"),
                H("Nonnegative expectation on coherent vectors"),
                StatementSource.FromAuthor(Disp(WitnessFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A symmetric witness is a Hermitian operator on this three-dimensional "
                        + "space whose expectation on every coherent vector is nonnegative, "
                        + "as in Section 2.3. Hermiticity makes the expectation real, so "
                        + "taking its real part preserves the inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-qubit-witness-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The spectral characterization"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The conjecture following Theorem 3 and in Section 6(c) asks whether "
                        + "mu2 >= 0 and mu3 >= -sqrt(mu1 mu2) characterize all symmetric "
                        + "witness spectra. Here eigenvalues mu1 >= mu2 >= mu3 mean that "
                        + "the characteristic polynomial is the displayed product over C, "
                        + "so multiplicities, repeated eigenvalues and zero eigenvalues "
                        + "are included. Positive semidefinite witnesses are included, "
                        + "as stipulated in footnote 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-qubit-witness-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The exact spectrum theorem"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The coherent vectors are exactly the null cone "
                            + "x^T ((0,0,-1),(0,1,0),(-1,0,0)) x = 0; explicitly the "
                            + "equation is x1^2 - 2 x0 x2 = 0. Diagonalizing the Hermitian "
                            + "matrix by a unitary U transports this cone to the eigenbasis: "
                            + "G = U^T ((0,0,-1),(0,1,0),(-1,0,0)) U is symmetric "
                            + "and unitary, and the quadratic "
                            + "expectation is diagonal there.")),
                    Paragraph(Text(
                        "Suppose the third eigenvalue is -c with c > 0. Write A for "
                            + "the upper-left 2 by 2 submatrix (Gij) with i,j in {0,1}, "
                            + "and t = |G22|. Nonnegativity on the cone forces t > 0. "
                            + "For each u = (u0,u1), the two roots, counted with "
                            + "multiplicity, of G22 z^2 + 2(G02 u0 + G12 u1)z + u^T A u "
                            + "= 0 give c |u^T A u| <= t(mu1 |u0|^2 + mu2 |u1|^2).")),
                    Paragraph(Text(
                        "The 2 by 2 bilinear determinant bound says that a complex "
                            + "symmetric matrix B satisfying |u^T B u| <= p |u0|^2 "
                            + "+ q |u1|^2 for every u has p,q >= 0 and |det B| <= pq. "
                            + "Polarization bounds the bilinear form by the two "
                            + "corresponding quadratic weights. Applied to cA, this "
                            + "bound combines with the unitary submatrix identity "
                            + "|det A| = |G22| <= 1 to give mu1,mu2 >= 0 and "
                            + "c^2 <= t mu1 mu2 <= mu1 mu2. This yields the required "
                            + "lower bound for mu3; when mu3 >= 0 both inequalities "
                            + "follow directly from the ordering.")),
                    Paragraph(Text(
                        "For sufficiency, the diagonal matrix diag(mu1,mu3,mu2) "
                            + "in the Dicke basis has the required characteristic "
                            + "polynomial. Its coherent expectation is "
                            + "(sqrt(mu1)|v0|^2 - sqrt(mu2)|v1|^2)^2 "
                            + "+ 2(mu3 + sqrt(mu1 mu2))|v0|^2|v1|^2, which is "
                            + "nonnegative under the two spectral inequalities. "
                            + "This is the diagonal construction underlying the "
                            + "sufficient direction of Theorem 3."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("champagne-johnston-macdonald-pipes-2022-symmetric-witness-spectrum"),
                    ResolutionKind.Proved))
        )));

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Entanglement", "AbsoluteSeparability", "SymmetricQubitWitnessSpectrum", name);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula RealType() => Seq(Mathbb, Grp(X("R")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinType(byte size) => At(Qualified("Fin"), D(size));
    private static Formula VectorType(byte size) => new Formula.TypeArrow(FinType(size), ComplexType());
    private static Formula MatrixType() => At(Qualified("Matrix"), FinType(3), FinType(3), ComplexType());
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula MuAt(byte index) => new Formula.Subscript(Mu, D(index));
    private static Formula SqrtOf(Formula value) => At(Qualified("Real", "sqrt"), value);

    private static Formula CoherentFormula()
    {
        var first = At(X("v"), D(0));
        var second = At(X("v"), D(1));
        var coordinates = Seq(Bang, OpenBracket,
            new Formula.Power(first, D(2)), Comma, Sp,
            Multiply(Multiply(Typed(SqrtOf(D(2)), ComplexType()), first), second), Comma, Sp,
            new Formula.Power(second, D(2)), CloseBracket);
        return All(X("v"), VectorType(2), Equal(LocalCall("coherent", X("v")), coordinates));
    }

    private static Formula WitnessFormula()
    {
        var vector = LocalCall("coherent", X("v"));
        var expectation = At(Qualified("dotProduct"), At(Qualified("star"), vector),
            At(Qualified("Matrix", "mulVec"), X("W"), vector));
        return All(X("W"), MatrixType(), Iff(LocalCall("IsSymmetricWitness", X("W")),
            And(At(Qualified("Matrix", "IsHermitian"), X("W")),
                All(X("v"), VectorType(2), Le(D(0), At(Qualified("Complex", "re"), expectation))))));
    }

    private static Formula ClaimFormula()
    {
        Formula Factor(Formula value) => Parenthesized(Subtract(Qualified("Polynomial", "X"),
            At(Qualified("Polynomial", "C"), Typed(value, ComplexType()))));
        var characteristic = Equal(At(Qualified("Matrix", "charpoly"), X("W")),
            Multiply(Multiply(Factor(MuAt(1)), Factor(MuAt(2))), Factor(MuAt(3))));
        var exists = Some("W", MatrixType(), And(LocalCall("IsSymmetricWitness", X("W")), characteristic));
        var inequalities = And(Le(D(0), MuAt(2)),
            Le(new Formula.Negate(SqrtOf(Multiply(MuAt(1), MuAt(2)))), MuAt(3)));
        return Iff(Local("claim"), All(MuAt(1), RealType(), All(MuAt(2), RealType(),
            All(MuAt(3), RealType(), Implies(Le(MuAt(2), MuAt(1)),
                Implies(Le(MuAt(3), MuAt(2)), Iff(exists, inequalities)))))));
    }
}
