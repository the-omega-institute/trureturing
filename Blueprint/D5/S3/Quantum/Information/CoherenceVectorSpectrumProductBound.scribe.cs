using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CoherenceVectorSpectrumProductBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Entropy/alvarezlosadaportesibosyk2023complementarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every majorization upper bound of the coherence set has first component times largest eigenvalue at least one over the dimension.",
        H("A coherence-vector and spectrum product bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("decreasing-rearrangement"),
                DeclarationHandle.Create(Module + ".decreasingRearrangement"),
                H("Decreasing rearrangement"),
                StatementSource.FromAuthor(Disp(DecreasingRearrangementFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Sorting in the order dual of the reals permutes the coordinates into decreasing order. "
                    + "The permutation is viewed as a function before composition with x. "
                    + "Applied to the squared-amplitude vector of a pure state, this is the ordered vector "
                    + "used in Section 2.2, Eqs. (9)–(11), PDF p. 3. "
                    + "The definition also applies to arbitrary real vectors, including the empty vector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coherence-set"),
                DeclarationHandle.Create(Module + ".coherenceSet"),
                H("Averages over pure-state decompositions"),
                StatementSource.FromAuthor(Disp(CoherenceSetFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The set consists of all averages of decreasing pure-state coherence vectors over finite "
                    + "decompositions of ρ. In a decomposition, p is nonnegative and sums to one, every ψ j "
                    + "has squared norm one, and ρ is the sum of their rank-one density matrices weighted by "
                    + "the complex embeddings of p j. The coherence vector of ψ j has ith entry equal to "
                    + "the squared modulus of ψ j i. Thus this is Dᵖˢᵈ(ρ) from Section 2.2, "
                    + "Eqs. (9)–(11), PDF p. 3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("majorization-upper-bound"),
                DeclarationHandle.Create(Module + ".IsMajorizationUpperBound"),
                H("Majorization upper bounds of the coherence set"),
                StatementSource.FromAuthor(Disp(IsMajorizationUpperBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "An upper bound is a decreasing, nonnegative real vector with total mass one whose "
                    + "partial sums dominate those of the decreasing rearrangement of every member of the "
                    + "coherence set. Majorizes takes the dominating list first and also requires equality "
                    + "of the total sums. Section 2.2, Eq. (12), PDF pp. 3–4, defines ν(ρ) as the "
                    + "majorization supremum of Dᵖˢᵈ(ρ). The predicate requires only the upper-bound "
                    + "property and makes no leastness assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("max-eigenvalue"),
                DeclarationHandle.Create(Module + ".maxEigenvalue"),
                H("The largest spectral value"),
                StatementSource.FromAuthor(Disp(MaxEigenvalueFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a Hermitian matrix, take the real supremum of its finite set of eigenvalues. "
                    + "For a non-Hermitian matrix the value is defined to be zero. "
                    + "For a density matrix in positive dimension, this is the largest component λ₁(ρ) "
                    + "of the ordered spectrum in Section 2.3, PDF p. 4, and Section 3.4, "
                    + "Conjecture 5, Eq. (20), PDF p. 7."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The product bound in every positive dimension"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let d be positive, let ρ be a positive semidefinite complex matrix of trace one, "
                        + "and let ν be any majorization upper bound of its coherence set. "
                        + "Set a = √ρ and p j = Re(ρ j j). Positivity gives p j ≥ 0, and the trace condition "
                        + "gives Σⱼ p j = 1. The matrix a is Hermitian and a² = ρ, so the squared norm of "
                        + "its jth column is p j. If p j is nonzero, divide that column by the complex "
                        + "embedding of √(p j) to obtain ψ j. If p j is zero, every entry of that column "
                        + "vanishes; take ψ j to be the coordinate vector at the index ⟨0, hd⟩ instead. "
                        + "In both cases ψ j has squared norm one and "
                        + "p j |ψ j i|² = |a i j|² for every i and j. Multiplying the rank-one matrices "
                        + "by the complex embeddings of p j and summing gives aa* = ρ. "
                        + "Thus these d weighted vectors form a pure-state decomposition, including the zero weights.")),
                    Paragraph(Text(
                        "For any real vector x, every coordinate is at most the first coordinate of its "
                        + "decreasing rearrangement. This follows by monotonicity of the sorted vector in "
                        + "the order dual, comparing index zero with the inverse permutation's index of "
                        + "the chosen coordinate. Now let u i = Σⱼ p j decreasingRearrangement(coherenceVector(ψ j)) i. "
                        + "The decomposition places u in the coherence set. Majorization at partial-sum "
                        + "length one bounds the first coordinate of decreasingRearrangement u by ν ⟨0, hd⟩. "
                        + "For each column, (Re(a j j))² ≤ |a j j|² = p j |ψ j j|². "
                        + "Nonnegativity of p j and the rearrangement comparison bound their sum by "
                        + "u ⟨0, hd⟩, which is at most the first coordinate of decreasingRearrangement u. "
                        + "Consequently s = Σⱼ (Re(a j j))² satisfies s ≤ ν ⟨0, hd⟩.")),
                    Paragraph(Text(
                        "Cauchy–Schwarz applied to the d real diagonal entries gives "
                        + "t² ≤ (d : ℝ) s, where t = Re(trace a). "
                        + "The trace formula for the continuous functional calculus expresses t as "
                        + "Σᵢ √λᵢ, with λᵢ the Hermitian eigenvalues of ρ. "
                        + "Positivity makes these eigenvalues nonnegative, and their sum is one.")),
                    Paragraph(Text(
                        "Write L = maxEigenvalue ρ. Every λᵢ is at most L because L is the supremum "
                        + "of their finite range. Positive dimension supplies an eigenvalue, so L ≥ 0. "
                        + "If L were not positive, all the nonnegative eigenvalues would be zero, "
                        + "contradicting their sum being one. Thus L > 0. For each i, "
                        + "λᵢ = √λᵢ √λᵢ ≤ √λᵢ √L. Summing gives 1 ≤ t √L, hence 1/√L ≤ t.")),
                    Paragraph(Text(
                        "The last inequality makes t nonnegative. Squaring it and multiplying by L "
                        + "gives 1 ≤ L t². Combine the diagonal estimate and the first-coordinate bound "
                        + "to obtain 1 ≤ L t² ≤ L ((d : ℝ) s) ≤ L ((d : ℝ) ν ⟨0, hd⟩). "
                        + "Since the real embedding of d is positive, division by it yields the stated "
                        + "product inequality. In particular, the majorization supremum ν(ρ) of "
                        + "Eq. (12) is an upper bound, so this establishes Conjecture 5, Eq. (20), "
                        + "in Section 3.4, PDF pp. 6–7, without requiring a construction of that supremum."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alvarez-losada-portesi-bosyk-2023-coherence-spectrum-product-bound"),
                    ResolutionKind.Proved)))));

    private static Formula DecreasingRearrangementFormula()
    {
        Formula sorted = At(new Formula.Subscript(Qualified("Tuple", "sort"),
            At(Qualified("OrderDual"), Reals())), X("x"));
        return All("d", Naturals(), All("x", RealVector(X("d")),
            Equal(Typed(LocalCall("decreasingRearrangement", X("x")), RealVector(X("d"))),
                At(Qualified("Function", "comp"), X("x"), At(Qualified("Equiv", "toFun"), sorted)))));
    }

    private static Formula CoherenceSetFormula()
    {
        Formula average = LambdaOf("i", FinOf(X("d")), SumOver("j", FinOf(X("k")),
            Multiply(At(X("p"), X("j")), At(Local("decreasingRearrangement"),
                At(Coherence("coherenceVector"), At(X("ψ"), X("j"))), X("i")))));
        Formula membership = Some("k", Naturals(), Some("p", RealVector(X("k")),
            Some("ψ", Arrow(FinOf(X("k")), Arrow(FinOf(X("d")), Complexes())),
                Conjunction(At(Coherence("IsDecomposition"), X("ρ"), X("k"), X("p"), X("ψ")),
                    Equal(X("u"), average)))));
        Formula set = Seq(OpenBrace, Typed(X("u"), RealVector(X("d"))), Sp, Mid, Sp,
            Parenthesized(membership), CloseBrace);
        return MatrixBinders(Equal(Typed(LocalCall("coherenceSet", X("ρ")),
            At(Qualified("Set"), RealVector(X("d")))), set));
    }

    private static Formula IsMajorizationUpperBoundFormula()
    {
        Formula condition = Conjunction(At(Qualified("Antitone"), X("ν")),
            Conjunction(All("i", FinOf(X("d")), LE(Typed(D(0), Reals()), At(X("ν"), X("i")))),
                Conjunction(Equal(SumOver("i", FinOf(X("d")), At(X("ν"), X("i"))), Typed(D(1), Reals())),
                    All("u", RealVector(X("d")), Imp(Member(X("u"), LocalCall("coherenceSet", X("ρ"))),
                        At(Qualified("D5", "S3", "Quantum", "Matrix", "LinDTIMajorizationRefutation", "Majorizes"),
                            At(Qualified("List", "ofFn"), X("ν")),
                            At(Qualified("List", "ofFn"), LocalCall("decreasingRearrangement", X("u")))))))));
        return MatrixBinders(All("ν", RealVector(X("d")),
            Equivalence(LocalCall("IsMajorizationUpperBound", X("ρ"), X("ν")), condition)));
    }

    private static Formula MaxEigenvalueFormula()
    {
        Formula hermitian = At(Qualified("Matrix", "IsHermitian"), X("ρ"));
        Formula greatest = At(Qualified("D5", "S3", "Quantum", "Measurement",
            "AdvantageQuantumNonSimulability", "aqGreatestEigenvalue"), X("h"));
        Formula value = At(Qualified("dite"), hermitian, LambdaOf("h", hermitian, greatest),
            At(Qualified("Function", "const"), new Formula.Not(Parenthesized(hermitian)), Typed(D(0), Reals())));
        return MatrixBinders(Equal(Typed(LocalCall("maxEigenvalue", X("ρ")), Reals()), value));
    }

    private static Formula ResultFormula()
    {
        Formula bound = LE(new Formula.Fraction(Typed(D(1), Reals()),
                Typed(At(Qualified("Nat", "cast"), X("d")), Reals())),
            Multiply(At(X("ν"), At(Qualified("Fin", "mk"), D(0), X("hd"))),
                LocalCall("maxEigenvalue", X("ρ"))));
        Formula state = At(Qualified("D5", "S3", "Divergence", "CoherenceL1RelativeEntropyBound", "IsState"), X("ρ"));
        return All("d", Naturals(), All("hd", LE(D(1), X("d")), All("ρ", MatrixType(X("d")),
            Imp(state, All("ν", RealVector(X("d")),
                Imp(LocalCall("IsMajorizationUpperBound", X("ρ"), X("ν")), bound))))));
    }

    private static Formula MatrixBinders(Formula body) =>
        All("d", Naturals(), All("ρ", MatrixType(X("d")), body));
    private static Formula Coherence(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "CoherenceAssistanceRoofEquality", name);
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "CoherenceVectorSpectrumProductBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
        "ρ" => Rho,
        "ν" => Nu,
        "ψ" => Psi,
        _ => F.Id(name),
    };
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula RealVector(Formula d) => Arrow(FinOf(d), Reals());
    private static Formula MatrixType(Formula d) => At(Qualified("Matrix"), FinOf(d), FinOf(d), Complexes());
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
