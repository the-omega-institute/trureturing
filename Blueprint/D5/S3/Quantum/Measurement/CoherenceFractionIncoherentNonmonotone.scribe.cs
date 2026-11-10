using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class CoherenceFractionIncoherentNonmonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/yaolisun2019coherencefraction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-dimensional density matrix and two diagonal Kraus matrices give a strict increase of the quantum coherence fraction.",
        H("The quantum coherence fraction can increase under incoherent operations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherence-fraction-incoherent-operation"),
                DeclarationHandle.Create(Prefix + "IsIncoherentOperation"),
                H("Incoherent operations in Kraus form"),
                StatementSource.FromAuthor(Disp(IncoherentOperationFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For natural dimensions d and m, a family of m complex d by d Kraus matrices is incoherent "
                    + "when its adjoint products sum to the identity and each individual Kraus sandwich preserves diagonality. "
                    + "The diagonal test ranges over all complex diagonal matrices. "
                    + "This expresses the source's condition on the individual branches without dividing by their traces, "
                    + "and includes branches of trace zero. The source states its normalized condition for diagonal density "
                    + "operators in Section II, CF.tex, lines 122–131."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherence-fraction-definition"),
                DeclarationHandle.Create(Prefix + "coherenceFraction"),
                H("The coherence fraction"),
                StatementSource.FromAuthor(Disp(CoherenceFractionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every vector whose coordinates have norm one, divide the real quadratic form by the dimension "
                    + "and take the supremum of the resulting values. The dimension is explicitly cast from a natural number to a real number. "
                    + "For a density matrix in positive dimension, dividing such a vector by the square root of d gives "
                    + "a maximally coherent unit vector. Thus this is the overlap optimized in equation (QCF), "
                    + "CF.tex, lines 141–151. The real-supremum formula itself is defined for every natural dimension "
                    + "and every complex square matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherence-fraction-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Monotonicity under incoherent operations"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural dimension d, every natural number m of Kraus matrices, every density matrix "
                    + "and every incoherent Kraus family, the coherence fraction of the sum of all output branches "
                    + "is at most the input coherence fraction. IsDensity means positive semidefinite with trace one. "
                    + "The source conjectures failure of this monotonicity in Section V, CF.tex, lines 422–425; "
                    + "the proposition displayed here is the universal monotonicity assertion whose negation answers that question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherence-fraction-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A strict increase in dimension four"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                ResultProof(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yao-li-sun-2019-coherence-fraction-incoherent-nonmonotone"),
                    ResolutionKind.Refuted)))));

    private static BlockSequence ResultProof() => Blocks(
        Paragraph(Text(
            "Use coordinates 0, 1, 2, 3 and write i for the imaginary unit. Let P be 1/2163 times the matrix "
            + "with rows (1425, −300−300i, 615−240i, 615+240i), "
            + "(−300+300i, 1075, 680+180i, −180−680i), "
            + "(615+240i, 680−180i, 913, 225−400i), "
            + "and (615−240i, −180+680i, 225+400i, 913). "
            + "Entrywise rational arithmetic gives P† = P, P² = P and tr(P) = 2. "
            + "A self-adjoint idempotent is positive semidefinite. Therefore R = P/2 is positive semidefinite "
            + "and has trace one, so R is a density matrix.")),
        Paragraph(Text(
            "Choose K₀ = diag(1, 0, 3/5, 3/5) and K₁ = diag(0, 1, 4/5, −4i/5). "
            + "Their adjoint products sum to the identity: the last two diagonal entries are 9/25 + 16/25 = 1. "
            + "Each Kⱼ is diagonal, so sandwiching a diagonal matrix by Kⱼ and its adjoint again gives a diagonal matrix. "
            + "Consequently these two matrices define an incoherent operation Φ(X) = K₀XK₀† + K₁XK₁†.")),
        Paragraph(Text(
            "For every complex four by four matrix A, the set of values in its coherence-fraction supremum is bounded above. "
            + "Indeed, for a vector z with unit-modulus coordinates, expanding the dot product and applying "
            + "the triangle inequality gives |z†Az| ≤ ∑ⱼ∑ₗ |Aⱼₗ|. "
            + "The real part is at most the modulus, and division by four preserves an upper bound "
            + "by this nonnegative sum.")),
        Paragraph(Text(
            "Write a = (1, 0, 3/5, 3/5), b = (0, 1, 4/5, −4i/5), and Q = Φ(R). "
            + "Diagonal multiplication gives Qⱼₗ = Pⱼₗ(aⱼ conjugate(aₗ) + bⱼ conjugate(bₗ))/2. "
            + "Substituting the entries above and summing them gives Re(𝟙†Q𝟙)/4 = 1/2, "
            + "where 𝟙 has all four coordinates equal to one.")),
        Paragraph(Text(
            "To obtain a uniform bound for the input, first let u and w be complex numbers with |u| ≤ 7/5 "
            + "and |w| = 1. The reverse triangle inequality gives ||u| − 1| ≤ |w − u|. "
            + "Since (|u| + 1)² ≤ 144/25, factoring the difference of squares yields "
            + "(|u|² − 1)² ≤ (144/25)|w − u|².")),
        Paragraph(Text(
            "For complex numbers x, y, w, t of modulus one, set u = (3x + 4y)/5 and v = (3x + 4iy)/5. "
            + "Both |u| and |v| are at most 7/5. Expanding real and imaginary parts gives "
            + "|u|² − 1 = (24/25)(Re(x)Re(y) + Im(x)Im(y)) and "
            + "|v|² − 1 = (24/25)(Im(x)Re(y) − Re(x)Im(y)). "
            + "The sum of their squares is 576/625 because |x|²|y|² = 1. "
            + "Applying the preceding estimate to (u,w) and (v,t) therefore gives "
            + "4/25 ≤ |w − (3x + 4y)/5|² + |t − (3x + 4iy)/5|².")),
        Paragraph(Text(
            "For arbitrary complex a, b, c, d, the triangle inequality bounds "
            + "|c − (3a + 4b)/5| by |c| + (3|a| + 4|b|)/5. "
            + "Cauchy–Schwarz with coefficients (1, 3/5, 4/5), whose squared norm is two, "
            + "bounds its square by 2(|a|² + |b|² + |c|²). "
            + "The same argument bounds |d − (3a + 4ib)/5|² by 2(|a|² + |b|² + |d|²). "
            + "Adding and using nonnegativity gives an upper bound "
            + "4(|a|² + |b|² + |c|² + |d|²) for the sum of the two squared residuals.")),
        Paragraph(Text(
            "For any vector z, expand the squared Euclidean norm of z − Pz. "
            + "The identities P† = P and P² = P imply (Pz)†Pz = z†Pz. "
            + "Consequently Re(z†Pz) + ∑ⱼ |zⱼ − (Pz)ⱼ|² = ∑ⱼ |zⱼ|². "
            + "Direct multiplication by the displayed matrix also gives "
            + "(Pz)₂ = (3(Pz)₀ + 4(Pz)₁)/5 and (Pz)₃ = (3(Pz)₀ + 4i(Pz)₁)/5. "
            + "Thus the linear functionals F₁(z) = z₂ − (3z₀ + 4z₁)/5 and "
            + "F₂(z) = z₃ − (3z₀ + 4iz₁)/5 vanish on Pz. "
            + "By linearity F₁(z) = F₁(z − Pz) and F₂(z) = F₂(z − Pz).")),
        Paragraph(Text(
            "Now assume every coordinate of z has modulus one and put e = z − Pz. "
            + "The four-scalar lower bound and the residual upper bound give "
            + "4/25 ≤ |F₁(z)|² + |F₂(z)|² = |F₁(e)|² + |F₂(e)|² ≤ 4∑ⱼ |eⱼ|². "
            + "Hence ∑ⱼ |eⱼ|² ≥ 1/25. The projection identity and ∑ⱼ |zⱼ|² = 4 "
            + "give Re(z†Pz) ≤ 4 − 1/25. Since R = P/2, every value Re(z†Rz)/4 "
            + "is at most 1/2 − 1/200.")),
        Paragraph(Text(
            "The all-ones vector is admissible in the bounded output supremum, so coherenceFraction(Q) ≥ 1/2. "
            + "The input set is nonempty, again using the all-ones vector, and every one of its values satisfies "
            + "the preceding uniform estimate. Taking its supremum gives coherenceFraction(R) ≤ 1/2 − 1/200. "
            + "Applying universal monotonicity at d = 4, m = 2, the density matrix R and the two incoherent "
            + "Kraus matrices would give coherenceFraction(Q) ≤ coherenceFraction(R). "
            + "This contradicts coherenceFraction(R) ≤ 1/2 − 1/200 < 1/2 ≤ coherenceFraction(Q).")));

    private static Formula IncoherentOperationFormula()
    {
        Formula branch = At(X("k"), X("i"));
        Formula completeness = Equal(
            SumOver("i", FinOf(X("m")), Multiply(Adjoint(branch), branch)),
            Typed(D(1), MatrixType(X("d"))));
        Formula diagonalPreservation = All("i", FinOf(X("m")),
            All("ρ", MatrixType(X("d")), Implication(
                At(Qualified("Matrix", "IsDiag"), X("ρ")),
                At(Qualified("Matrix", "IsDiag"),
                    Multiply(Multiply(branch, X("ρ")), Adjoint(branch))))));
        return All("d", Naturals(), All("m", Naturals(),
            All("k", KrausType(), Equivalence(LocalCall("IsIncoherentOperation", X("k")),
                Conjunction(completeness, diagonalPreservation)))));
    }

    private static Formula CoherenceFractionFormula()
    {
        Formula unitCoordinates = All("j", FinOf(X("d")),
            Equal(new Formula.Norm(At(X("z"), X("j"))), Typed(D(1), Reals())));
        Formula quadratic = At(Qualified("Complex", "re"),
            At(Qualified("dotProduct"), At(Qualified("star"), X("z")),
                At(Qualified("Matrix", "mulVec"), X("ρ"), X("z"))));
        Formula value = new Formula.Fraction(quadratic,
            Typed(At(Qualified("Nat", "cast"), X("d")), Reals()));
        Formula values = Seq(OpenBrace, Typed(X("r"), Reals()), Sp, Mid, Sp,
            Some("z", Arrow(FinOf(X("d")), Complexes()),
                Conjunction(unitCoordinates, Equal(X("r"), value))), CloseBrace);
        return All("d", Naturals(), All("ρ", MatrixType(X("d")),
            Equal(Typed(LocalCall("coherenceFraction", X("ρ")), Reals()),
                At(Qualified("sSup"), values))));
    }

    private static Formula ClaimFormula()
    {
        Formula branch = At(X("k"), X("i"));
        Formula output = SumOver("i", FinOf(X("m")),
            Multiply(Multiply(branch, X("ρ")), Adjoint(branch)));
        Formula monotonicity = new Formula.Relation(LocalCall("coherenceFraction", output),
            FormulaRelationOperator.LessThanOrEqual, LocalCall("coherenceFraction", X("ρ")));
        return Equivalence(Local("claim"), All("d", Naturals(), All("m", Naturals(),
            All("ρ", MatrixType(X("d")), All("k", KrausType(),
                Implication(At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), X("ρ")),
                    Implication(LocalCall("IsIncoherentOperation", X("k")), monotonicity)))))));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "CoherenceFractionIncoherentNonmonotone", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula MatrixType(Formula size) => At(Qualified("Matrix"), FinOf(size), FinOf(size), Complexes());
    private static Formula KrausType() => Arrow(FinOf(X("m")), MatrixType(X("d")));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Adjoint(Formula value) => At(Qualified("Matrix", "conjTranspose"), value);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
