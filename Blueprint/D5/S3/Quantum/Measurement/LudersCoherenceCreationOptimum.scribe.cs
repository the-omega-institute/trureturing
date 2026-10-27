using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class LudersCoherenceCreationOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mohantysharmasazimpradhanpati2022coherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every qubit density matrix has an attained maximum of output coherence under finite nonselective measurements, with exact zero and maximal gain criteria.",
        H("The optimal coherence created by qubit measurements"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("luders"),
                DeclarationHandle.Create(Prefix + "luders"),
                H("The nonselective Luders action"),
                StatementSource.FromAuthor(Disp(LudersFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a family e of n complex two by two matrices, apply the square-root functional calculus to each member "
                    + "and sum its sandwiches with the input matrix. The function unreadState denotes precisely this sum. "
                    + "For positive semidefinite effects these are their positive square roots, giving the nonselective measurement rule in Section 2, "
                    + "coh-measure.tex, lines 127–130. The displayed definition itself accepts every family and every input matrix; "
                    + "positivity and completeness are imposed when discussing measurements."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bloch-norm"),
                DeclarationHandle.Create(Prefix + "blochNorm"),
                H("The Bloch length"),
                StatementSource.FromAuthor(Disp(BlochNormFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a Hermitian qubit matrix, the squared Bloch length is the squared real diagonal difference "
                    + "plus four times the squared modulus of the upper off-diagonal entry. Taking its nonnegative square root "
                    + "gives the length used in the source's Bloch representation and coherence maximum, "
                    + "coh-measure.tex, lines 212 and 228–235. The same expression defines a real number for every complex "
                    + "two by two matrix, without a density hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The attained maximum and both extremal gain criteria"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                ResultProof(),
                DescribeRole.Theorem))));

    private static Formula LudersFormula() => All("n", Naturals(),
        All("e", Effects(), All("ρ", QubitMatrix(),
            Equal(Typed(LocalCall("luders", X("e"), Rho), QubitMatrix()),
                At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"),
                    LambdaOf("i", FinOf(X("n")), At(Qualified("CFC", "sqrt"), At(X("e"), X("i")))),
                    Rho)))));

    private static Formula BlochNormFormula() => All("ρ", QubitMatrix(),
        Equal(Typed(LocalCall("blochNorm", Rho), Reals()),
            At(Qualified("Real", "sqrt"),
                Add(Square(At(Qualified("Complex", "re"),
                        Sub(Entry(D(0), D(0)), Entry(D(1), D(1))))),
                    Multiply(Typed(D(4), Reals()), Square(new Formula.Norm(Entry(D(0), D(1)))))))));

    private static Formula ResultFormula()
    {
        Formula outputs = Seq(OpenBrace, X("c"), Colon, Sp, Reals(), Sp, Mid, Sp,
            Some("e", Effects(), Conjunction(IsPOVM(X("e")),
                Equal(X("c"), Coherence(LocalCall("luders", X("e"), Rho))))), CloseBrace);
        Formula greatest = At(Qualified("IsGreatest"), outputs, Optimum());
        Formula zeroGain = Equivalence(Equal(Gain(), Typed(D(0), Reals())),
            Equal(Entry(D(0), D(0)), Entry(D(1), D(1))));
        Formula half = new Formula.Fraction(Typed(D(1), Reals()), Typed(D(2), Reals()));
        Formula extremeGain = Equivalence(Equal(Gain(), half), Disjunction(
            Equal(Rho, Diagonal(D(1), D(0))), Equal(Rho, Diagonal(D(0), D(1)))));
        return All("ρ", QubitMatrix(), Implication(IsDensity(Rho),
            All("n", Naturals(), Implication(LE(Typed(D(2), Naturals()), X("n")),
                Conjunction(greatest, Conjunction(zeroGain,
                    Conjunction(LE(Gain(), half), extremeGain)))))));
    }

    private static BlockSequence ResultProof() => Blocks(
        Paragraph(Text(
            "IsDensity means positive semidefinite with trace one; IsPOVM means that every effect is positive semidefinite "
            + "and their sum is the identity. The coherence l1Coherence is the sum of the moduli of all off-diagonal entries, "
            + "as in coh-measure.tex, line 109. The maximum ranges over every family indexed by Fin n, including zero effects. "
            + "The four conclusions give the greatest output coherence, the exact condition for zero optimal gain, "
            + "the upper bound one half for optimal gain, and its equality cases. "
            + "The source gives the maximum for a restricted one-parameter family at lines 230–231; "
            + "the general two-outcome question is stated at line 298 and the finite-outcome question at line 505.")),
        Paragraph(Text(
            "First, Hermitian matrices have real diagonal entries and conjugate off-diagonal entries, so their coherence "
            + "is twice the modulus of the upper off-diagonal entry. Put c = ρ₀₁, r = Re(ρ₀₀ − ρ₁₁), "
            + "s = 2|c| and R = √(r² + s²). For an arbitrary measurement, write its positive square roots as "
            + "mᵢ = ((pᵢ, zᵢ), (conjugate(zᵢ), qᵢ)), with real pᵢ and qᵢ. Define "
            + "vᵢ = (pᵢ − qᵢ)/2 and kᵢ = pᵢqᵢ − |zᵢ|². "
            + "Nonnegativity of the determinants gives kᵢ ≥ 0. Completeness gives ∑ᵢ mᵢ² = I; "
            + "its trace yields ∑ᵢ(kᵢ + 2(|zᵢ|² + vᵢ²)) = 1, and its upper off-diagonal entry gives "
            + "∑ᵢ((pᵢ + qᵢ)/2)zᵢ = 0. Expanding the sandwiches and using trace one therefore shows that the output "
            + "is Hermitian and its upper off-diagonal entry is "
            + "∑ᵢ[kᵢc + (2Re(conjugate(zᵢ)c) + vᵢr)zᵢ].")),
        Paragraph(Text(
            "For real s, r, t and v, the larger eigenvalue of the real symmetric matrix with diagonal (s, 0) "
            + "and off-diagonal |r|/2 is (s + √(r² + s²))/2. Its quadratic-form bound gives "
            + "st² + |r|tv ≤ ((s + √(r² + s²))/2)(t² + v²). "
            + "The inequalities |Re(conjugate(z)c)| ≤ |z||c| and the triangle inequality, "
            + "followed by this bound with t = |z| and v replaced by |v|, imply "
            + "2|(2Re(conjugate(z)c) + vr)z| ≤ (|z|² + v²)(2|c| + √(r² + 4|c|²)).")),
        Paragraph(Text(
            "The Bloch length satisfies R² = r² + s², with 0 ≤ s ≤ R. "
            + "Its equality with the Euclidean norm of the Bloch vector follows by expanding the three real coordinates. "
            + "Positive semidefiniteness bounds this norm by the real trace, hence R ≤ 1 for a density matrix. "
            + "Set l = (s + R)/2, so s ≤ l. For each term of the output entry, the triangle inequality, "
            + "kᵢ ≥ 0 and the preceding quadratic bound give "
            + "2|kᵢc + (2Re(conjugate(zᵢ)c) + vᵢr)zᵢ| ≤ (kᵢ + 2(|zᵢ|² + vᵢ²))l. "
            + "Summing, applying the triangle inequality to the sum, and using that the coefficients sum to one "
            + "proves that every output coherence is at most l.")),
        Paragraph(Text(
            "To attain this bound, first choose a complex phase a with |a| = 1 and conjugate(a)c = |c|. "
            + "Seek a complex z and real v with |z|² + v² = 1 and |(2Re(conjugate(z)c) + vr)z| = l. "
            + "If R = 0, then c = 0 and r = 0, and z = 1, v = 0 suffice. "
            + "Otherwise R > 0 and l > 0. Put t = √(l/R), v = rt/(2l), and z = ta. "
            + "The identity 4l(l − s) = r² gives t² = l/R and v² = (l − s)/R, "
            + "so |z|² + v² = 1. The phase choice gives Re(conjugate(z)c) = t|c|, "
            + "whence 2Re(conjugate(z)c) + vr = Rt and |(2Re(conjugate(z)c) + vr)z| = Rt² = l.")),
        Paragraph(Text(
            "Form the matrix p with rows ((1 + v)/2, z/2) and (conjugate(z)/2, (1 − v)/2). "
            + "The unit-length equation makes p self-adjoint and idempotent. Thus p and q = I − p are positive "
            + "semidefinite complementary projections. For n ≥ 2, write n = m + 2 and take the effects "
            + "p, q followed by m zero matrices. They form a POVM. The positive square roots of these projections "
            + "are themselves, and the square root of zero is zero, so the output is pρp + qρq. "
            + "Expanding its upper off-diagonal entry gives (2Re(conjugate(z)c) + vr)z/2. "
            + "The output is Hermitian, so its coherence is |(2Re(conjugate(z)c) + vr)z| = l. "
            + "This supplies an attaining measurement for every allowed n.")),
        Paragraph(Text(
            "The optimal gain is l − s = (R − s)/2. It vanishes exactly when R = s. "
            + "The squared-radius identity then forces r = 0; conversely r = 0 gives R = s by nonnegativity. "
            + "Since both diagonal entries of ρ are real, r = 0 is equivalent to ρ₀₀ = ρ₁₁.")),
        Paragraph(Text(
            "Finally, R ≤ 1 and s ≥ 0 give l − s ≤ 1/2. Equality forces s = 0 and R = 1. "
            + "Thus c = 0, its conjugate lower entry also vanishes, and r² = 1. "
            + "Together with the real trace equation ρ₀₀ + ρ₁₁ = 1, the alternatives r = 1 and r = −1 "
            + "give exactly diag(1, 0) and diag(0, 1). Conversely each of these matrices has coherence zero "
            + "and Bloch length one, so each attains gain one half. The attaining measurement puts l in the set "
            + "of output coherences, and the bound for every measurement makes it the greatest element of that set.")));

    private static Formula X(string name) => name == "ρ" ? Rho : F.Id(name);
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
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "LudersCoherenceCreationOptimum", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula QubitMatrix() => At(Qualified("Matrix"), FinOf(D(2)), FinOf(D(2)), Complexes());
    private static Formula Effects() => new Formula.TypeArrow(FinOf(X("n")), QubitMatrix());
    private static Formula Entry(Formula i, Formula j) => At(Rho, Typed(i, FinOf(D(2))), Typed(j, FinOf(D(2))));
    private static Formula Coherence(Formula matrix) => At(Qualified("D5", "S3", "Quantum", "Information",
        "CorrelatedCoherenceMonogamyRefutation", "l1Coherence"), matrix);
    private static Formula IsDensity(Formula matrix) => At(Qualified("D5", "S3", "Quantum", "Information",
        "SLDSpectralEnergy", "IsDensity"), matrix);
    private static Formula IsPOVM(Formula effects) => At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "ConcealmentKernelNecessityRefutation", "IsPOVM"), effects);
    private static Formula Optimum() => new Formula.Fraction(Add(Coherence(Rho), LocalCall("blochNorm", Rho)),
        Typed(D(2), Reals()));
    private static Formula Gain() => Sub(Optimum(), Coherence(Rho));
    private static Formula Diagonal(Formula a, Formula b) => At(Qualified("Matrix", "diagonal"),
        Seq(Bang, OpenBracket, Typed(a, Complexes()), Comma, Sp, Typed(b, Complexes()), CloseBracket));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), Typed(D(2), Naturals()));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
