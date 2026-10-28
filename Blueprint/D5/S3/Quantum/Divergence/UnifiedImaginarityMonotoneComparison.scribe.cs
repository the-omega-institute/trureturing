using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UnifiedImaginarityMonotoneComparisonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Divergence/wuwu2025unifiedimaginarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unified imaginarity minimized over real states is bounded by conjugate divergence.",
        H("Comparison of the two unified imaginarity measures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unified-divergence"),
                DeclarationHandle.Create(Module + ".unifiedDivergence"),
                H("Unified relative entropy"),
                StatementSource.FromAuthor(Disp(DivergenceFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real parameters α and β and complex square matrices ρ and σ, take the real part "
                    + "of the trace of the product of their powers, raise that real number to β, subtract one, "
                    + "and divide by (α − 1)β. The matrix powers ρ ^ α and σ ^ (1 − α) use Mathlib's "
                    + "CFC.instPowReal, hence CFC.rpow from continuous functional calculus. "
                    + "These powers are not taken entry by entry. On positive semidefinite matrices they are "
                    + "spectral powers, including at zero eigenvalues. "
                    + "The outer real power is Real.rpow. Equation (7), TeX lines 164–166, gives this relative entropy "
                    + "on states in its parameter range. The displayed definition extends the expression to all real "
                    + "parameters and all complex square matrices; real division is zero when its denominator is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginarity-h"),
                DeclarationHandle.Create(Module + ".imaginarityH"),
                H("Divergence from the conjugate state"),
                StatementSource.FromAuthor(Disp(ConjugateFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The first imaginarity measure compares ρ with its entrywise complex conjugate, "
                    + "as in equation (13), TeX lines 203–205. "
                    + "D5.S3.Quantum.Tomography.MUB.MUBCompletionRelativeGramEquivalence.entrywiseConj "
                    + "conjugates each matrix entry in the fixed coordinate basis. "
                    + "For a Hermitian matrix this conjugate equals the transpose."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imaginarity-e"),
                DeclarationHandle.Create(Module + ".imaginarityE"),
                H("Infimum over real states"),
                StatementSource.FromAuthor(Disp(InfimumFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The second imaginarity measure is the real infimum of the divergence values obtained "
                    + "from states σ fixed by entrywise conjugation. "
                    + "D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity means positive semidefinite "
                    + "with complex trace equal to one. Thus the conjugation condition says that every entry of σ "
                    + "is real, as in Definition 1, TeX lines 119–126. Equation (20), lines 347–349, "
                    + "uses a minimum over these states; the displayed definition uses sInf, "
                    + "without asserting that the infimum is attained. The set of values is nonempty "
                    + "and bounded below under the hypotheses of the comparison theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The comparison in every positive finite dimension"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ComparisonFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural d at least one, every density matrix ρ, every α strictly between zero "
                    + "and one, and every β strictly positive and at most one, the infimum over real states "
                    + "is at most the divergence from the conjugate state. This is the all-dimension reading "
                    + "of the conjecture in TeX lines 573–579, with the second measure expressed as an infimum. "
                    + "Singular density matrices are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The real part gives a stronger comparison"),
                StatementSource.FromAuthor(Disp(ComparisonFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, the entrywise conjugate of ρ is a density matrix: Hermitian symmetry identifies "
                        + "it with the transpose, which preserves positive semidefiniteness and trace. "
                        + "Let τ = (1/2 : ℂ) • (ρ + entrywiseConj ρ). Adding the two positive semidefinite "
                        + "matrices and scaling by the nonnegative complex scalar gives positive semidefiniteness, "
                        + "and linearity of trace gives trace one. Conjugation interchanges the summands and fixes "
                        + "the scalar, so τ has real entries.")),
                    Paragraph(Text(
                        "The real trace of the product of two positive semidefinite matrices is nonnegative. "
                        + "Since continuous functional calculus gives positive semidefinite powers, every overlap "
                        + "Re tr(ρ ^ α * σ ^ (1 − α)) is nonnegative. To bound this overlap above by one for "
                        + "density matrices, set A = ρ ^ α and B = σ ^ (1 − α). "
                        + "Their nonnegative eigenvalues satisfy ∑ᵢ λᵢ ^ (1/α) = 1 and "
                        + "∑ⱼ μⱼ ^ (1/(1 − α)) = 1: spectral trace evaluation and composition of the positive "
                        + "powers reduce these sums to the traces of ρ and σ.")),
                    Paragraph(Text(
                        "Choose the eigenvector unitaries of A and B and put W equal to the adjoint of the first "
                        + "times the second. The squared moduli of the entries of W form a doubly stochastic matrix. "
                        + "The real trace of AB is the sum of λᵢμⱼ weighted by these squared moduli. "
                        + "Weighted arithmetic–geometric mean gives λᵢμⱼ ≤ α λᵢ ^ (1/α) "
                        + "+ (1 − α) μⱼ ^ (1/(1 − α)). Summing with the nonnegative weights and using "
                        + "both their row and column sums reduces the upper bound to α + (1 − α) = 1.")),
                    Paragraph(Text(
                        "Next put q = Re tr(ρ ^ α * (entrywiseConj ρ) ^ (1 − α)) and "
                        + "r = Re tr(ρ ^ α * τ ^ (1 − α)). Operator concavity of the power with exponent "
                        + "1 − α bounds τ ^ (1 − α) below by the average of ρ ^ (1 − α) and "
                        + "(entrywiseConj ρ) ^ (1 − α). The difference is positive semidefinite. "
                        + "Its product with ρ ^ α therefore has nonnegative real trace. The exponent addition "
                        + "law gives ρ ^ α * ρ ^ (1 − α) = ρ, including at zero eigenvalues, "
                        + "so trace linearity yields (1 + q)/2 ≤ r.")),
                    Paragraph(Text(
                        "Scalar concavity of the real β power on the nonnegative reals gives "
                        + "(1 + q ^ β)/2 ≤ ((1 + q)/2) ^ β. Its monotonicity then gives "
                        + "(1 + q ^ β)/2 ≤ r ^ β. For any two density matrices the overlap lies between "
                        + "zero and one, so its β power is at most one. The divergence is consequently "
                        + "nonnegative, because both its numerator and its denominator are nonpositive.")),
                    Paragraph(Text(
                        "The denominator (α − 1)β is strictly negative. Subtracting one from the midpoint "
                        + "power inequality and dividing reverses the inequality, giving "
                        + "unifiedDivergence α β ρ τ ≤ imaginarityH α β ρ / 2. "
                        + "All divergence values over real states are bounded below by zero, and τ supplies "
                        + "one such value. The infimum is therefore at most unifiedDivergence α β ρ τ. "
                        + "Finally imaginarityH α β ρ is nonnegative, by applying divergence nonnegativity "
                        + "to ρ and its conjugate. Combining these facts gives imaginarityE α β ρ "
                        + "≤ unifiedDivergence α β ρ τ ≤ imaginarityH α β ρ / 2 ≤ imaginarityH α β ρ."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wu-wu-2025-unified-imaginarity-monotone-comparison"),
                    ResolutionKind.Proved)))));

    private static Formula DivergenceFormula() => Parameters(All("σ", MatrixType(),
        Equal(Typed(LocalCall("unifiedDivergence", Alpha, Beta, Rho, SigmaLower), Reals()),
            new Formula.Fraction(
                Subtract(new Formula.Power(Parenthesized(Overlap(Rho, SigmaLower)), Beta), One()),
                Multiply(Subtract(Alpha, One()), Beta)))));

    private static Formula ConjugateFormula() => Parameters(Equal(
        Typed(LocalCall("imaginarityH", Alpha, Beta, Rho), Reals()),
        LocalCall("unifiedDivergence", Alpha, Beta, Rho, Conjugate(Rho))));

    private static Formula InfimumFormula()
    {
        Formula values = Seq(OpenBrace, Typed(X("x"), Reals()), Sp, Mid, Sp,
            Some("σ", MatrixType(), Conjunction(Density(SigmaLower),
                Conjunction(Equal(Conjugate(SigmaLower), SigmaLower),
                    Equal(X("x"), LocalCall("unifiedDivergence", Alpha, Beta, Rho, SigmaLower))))),
            CloseBrace);
        return Parameters(Equal(Typed(LocalCall("imaginarityE", Alpha, Beta, Rho), Reals()),
            At(Qualified("sInf"), values)));
    }

    private static Formula ComparisonFormula()
    {
        Formula comparison = LE(LocalCall("imaginarityE", Alpha, Beta, Rho),
            LocalCall("imaginarityH", Alpha, Beta, Rho));
        Formula beta = All("β", Reals(),
            Arrow(Member(Beta, At(Qualified("Set", "Ioc"), Zero(), One())), comparison));
        Formula alpha = All("α", Reals(),
            Arrow(Member(Alpha, At(Qualified("Set", "Ioo"), Zero(), One())), beta));
        return All("d", Naturals(), Arrow(LE(Typed(D(1), Naturals()), X("d")),
            All("ρ", MatrixType(), Arrow(Density(Rho), alpha))));
    }

    private static Formula Parameters(Formula body) => All("d", Naturals(),
        All("α", Reals(), All("β", Reals(), All("ρ", MatrixType(), body))));
    private static Formula Overlap(Formula left, Formula right) =>
        At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
            Multiply(new Formula.Power(Parenthesized(left), Alpha),
                new Formula.Power(Parenthesized(right), Parenthesized(Subtract(One(), Alpha))))));
    private static Formula Conjugate(Formula value) => At(Qualified("D5", "S3", "Quantum", "Tomography",
        "MUB", "MUBCompletionRelativeGramEquivalence", "entrywiseConj"), value);
    private static Formula Density(Formula value) => At(Qualified("D5", "S3", "Quantum", "Information",
        "SLDSpectralEnergy", "IsDensity"), value);
    private static Formula MatrixType() => At(Qualified("Matrix"),
        At(Qualified("Fin"), X("d")), At(Qualified("Fin"), X("d")), Complexes());
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Divergence",
        "UnifiedImaginarityMonotoneComparison", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
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
    private static Formula X(string name) => name switch
    {
        "α" => Alpha,
        "β" => Beta,
        "ρ" => Rho,
        "σ" => SigmaLower,
        _ => F.Id(name),
    };
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Zero() => Typed(D(0), Reals());
    private static Formula One() => Typed(D(1), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Arrow(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
