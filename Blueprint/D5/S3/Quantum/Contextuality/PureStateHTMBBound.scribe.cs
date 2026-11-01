using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class PureStateHTMBBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/PureStateHTMBBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/Observer/tavakolizambrinicruzeirouolaabbott2021contextual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure preparations satisfying both trit parity equivalences have HTMB success probability at most two thirds in every finite complex dimension.",
        H("The pure-state HTMB bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("htmb-value"), DeclarationHandle.Create(Prefix + "htmbValue"),
                H("The average trit-guessing score"),
                StatementSource.FromAuthor(Disp(ValueDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The preparation label x is a pair of residues modulo three. The two matrix families m and n "
                        + "represent the measurements used to guess its first and second coordinates, respectively. "
                        + "For a vector v, projector v is the complex matrix with entries vᵤ times the conjugate of vᵥ. "
                        + "Each summand takes the real trace of this matrix multiplied by the effect for the correct outcome. "
                        + "The factor 1/18 averages over nine preparation labels and two measurement choices. "
                        + "This is the score in equation (33), lines 492–499 of Manuscript_infocontext_reresubmission.tex "
                        + "in arXiv:2010.04751v3. The function is defined for arbitrary vectors and matrices; "
                        + "unit length and measurement positivity and completeness are hypotheses of the bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The pure-state conjecture"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural dimension d, all nine preparation vectors have norm one and each of the two "
                        + "three-outcome measurements consists of positive semidefinite matrices summing to the identity. "
                        + "For each coefficient a equal to one or two, the sums of preparation projectors on the three "
                        + "fibres of x₁ + a x₂ are equal. Equality with the zero fibre expresses all these equalities; "
                        + "division by the common fibre size three gives equality of the uniform mixtures. "
                        + "Under both equivalences, the score is at most 2/3. This is the finite-dimensional "
                        + "unit-vector and POVM formulation of the conjecture stated at line 506, following the numerical "
                        + "pure-state bound at lines 502–505 of Manuscript_infocontext_reresubmission.tex in arXiv:2010.04751v3. "
                        + "There is no dimension lower bound or assumption that either measurement is projective."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Pure states obey the HTMB inequality"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix d, ψ, m and n satisfying the hypotheses, and write Pᵢⱼ for the projector of ψ(i,j). "
                            + "First the two parity equivalences force Pᵢⱼ = Pᵢ₀ + P₀ⱼ − P₀₀. "
                            + "To see this entry by entry, let Lₐₖ be the sum of Pᵢⱼ over i + a j = k, and put "
                            + "D₁ = L₁₁ − L₁₀, D₂ = L₁₂ − L₁₀, D₃ = L₂₁ − L₂₀ and D₄ = L₂₂ − L₂₀. "
                            + "All four differences vanish. For Rᵢⱼ = Pᵢⱼ − Pᵢ₀ − P₀ⱼ + P₀₀, expanding the fibre sums gives "
                            + "3R₁₁ = −2D₁ + D₂ − D₃ − D₄, "
                            + "3R₁₂ = −D₁ − D₂ − 2D₃ + D₄, "
                            + "3R₂₁ = −D₁ − D₂ + D₃ − 2D₄ and "
                            + "3R₂₂ = D₁ − 2D₂ − D₃ − D₄. "
                            + "Thus these four remainders are zero; those with a zero coordinate vanish directly.")),
                    Paragraph(Text(
                        "Define Dcol = ∑ᵢ Re tr(Pᵢ₀ mᵢ) and Drow = ∑ⱼ Re tr(P₀ⱼ nⱼ). "
                            + "Summing the additive formula over j gives ∑ⱼ Pᵢⱼ = 3Pᵢ₀ + T, "
                            + "where T = ∑ⱼ P₀ⱼ − 3P₀₀ has trace zero because every unit-vector projector has trace one. "
                            + "Since ∑ᵢ mᵢ is the identity, the total contribution of T is Re tr(T) = 0. "
                            + "The first-coordinate part of the score numerator is therefore 3Dcol. "
                            + "Summing in the other order and using ∑ⱼ nⱼ equal to the identity gives 3Drow for the second part. "
                            + "Consequently the score is (Dcol + Drow)/6.")),
                    Paragraph(Text(
                        "Positivity makes each unit-vector expectation against an effect nonnegative. "
                            + "The sum of the three expectations for a fixed unit vector is one, by measurement completeness, "
                            + "so each individual expectation is at most one. In particular Dcol and Drow are each at most three. "
                            + "If all Pᵢ₀ equal P₀₀, completeness of m gives Dcol = Re tr(P₀₀) = 1, "
                            + "and hence Dcol + Drow is at most four. If all P₀ⱼ equal P₀₀, "
                            + "completeness of n instead gives Drow = 1 and the same bound.")),
                    Paragraph(Text(
                        "Otherwise choose i and j with Pᵢ₀ different from P₀₀ and P₀ⱼ different from P₀₀. "
                            + "The key geometric fact is that if unit-vector projectors satisfy "
                            + "P(a) − P(b) = P(c) − P(e) ≠ 0, then a and b lie in the span of c and e. "
                            + "Indeed, a and b are linearly independent: a scalar relation between unit vectors would have "
                            + "a scalar of norm one and would make their projectors equal. For w orthogonal to c and e, "
                            + "applying the matrix equality to w gives ⟨a,w⟩a = ⟨b,w⟩b. Independence forces both coefficients "
                            + "to vanish. Taking the orthogonal complement twice in finite dimension puts a and b in the stated span.")),
                    Paragraph(Text(
                        "Take s to be the complex span of ψ(0,j) and ψ(0,0), whose dimension is at most two. "
                            + "For every k the additive identity gives Pₖⱼ − Pₖ₀ = P₀ⱼ − P₀₀ ≠ 0, "
                            + "so the geometric fact puts ψ(k,0) in s. Likewise "
                            + "Pᵢₖ − P₀ₖ = Pᵢ₀ − P₀₀ ≠ 0 puts ψ(0,k) in the span of ψ(i,0) and ψ(0,0). "
                            + "Both generators already lie in s. Thus all vectors on the two coordinate axes lie in the same s.")),
                    Paragraph(Text(
                        "For a unit vector v in s and an arbitrary w, orthogonal projection onto s followed by "
                            + "Cauchy–Schwarz bounds |⟨v,w⟩|² by the squared norm of that projection. "
                            + "Parseval expresses this squared norm as ∑ₖ |⟨eₖ,w⟩|² for an orthonormal basis of s. "
                            + "A positive semidefinite matrix is a finite sum of matrices z z*. Applying the overlap bound "
                            + "to each z and summing gives Re tr(P(v) A) ≤ ∑ₖ Re tr(P(eₖ) A) for every positive semidefinite A. "
                            + "Apply this to each of the three effects and its corresponding axis vector. Interchange the sums "
                            + "and use completeness: each basis vector contributes Re tr(P(eₖ)) = 1. "
                            + "The resulting discrimination sum is at most dim(s), hence at most two. "
                            + "Using m for the first axis and n for the second proves Dcol ≤ 2 and Drow ≤ 2. "
                            + "In every case Dcol + Drow ≤ 4, so the score is at most 4/6 = 2/3.")),
                    Paragraph(Text(
                        "The bound concerns all finite complex dimensions with both parity equivalences. "
                            + "It does not assert an infinite-dimensional extension or a bound for mixed preparations."))),
                DescribeRole.Theorem))));

    private static Formula ValueDefinition()
    {
        Formula first = RealTrace(Multiply(Projector(At(X("ψ"), X("x"))),
            At(X("m"), Coordinate(X("x"), 1))));
        Formula second = RealTrace(Multiply(Projector(At(X("ψ"), X("x"))),
            At(X("n"), Coordinate(X("x"), 2))));
        return Inputs(Equal(Typed(LocalCall("htmbValue", X("ψ"), X("m"), X("n")), Reals()),
            Multiply(new Formula.Fraction(RealNumeral(1), RealNumeral(1, 8)),
                SumOver("x", Labels(), Add(first, second)))));
    }

    private static Formula ClaimBody()
    {
        Formula unit = All("x", Labels(), Equal(new Formula.Norm(At(X("ψ"), X("x"))), RealNumeral(1)));
        Formula equivalences = All("a", Trits(), Implication(
            Member(X("a"), Typed(new Formula.SetLiteral([TritNumeral(1), TritNumeral(2)]),
                At(Qualified("Finset"), Trits()))),
            All("k", Trits(), Equal(ParitySum(X("a"), X("k")), ParitySum(X("a"), TritNumeral(0))))));
        Formula bound = new Formula.Relation(LocalCall("htmbValue", X("ψ"), X("m"), X("n")),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Fraction(RealNumeral(2), RealNumeral(3)));
        return Inputs(Implication(unit, Implication(Measurement(X("m")),
            Implication(Measurement(X("n")), Implication(equivalences, bound)))));
    }

    private static Formula Inputs(Formula body) => All("d", Naturals(),
        All("ψ", Arrow(Labels(), Space()), All("m", Arrow(Trits(), Matrices()),
            All("n", Arrow(Trits(), Matrices()), body))));

    private static Formula Measurement(Formula family) => Conjunction(
        All("b", Trits(), At(Qualified("Matrix", "PosSemidef"), At(family, X("b")))),
        Equal(SumOver("b", Trits(), At(family, X("b"))), Typed(D(1), Matrices())));

    private static Formula ParitySum(Formula a, Formula k)
    {
        Formula predicate = LambdaOf("x", Labels(), Equal(
            Add(Coordinate(X("x"), 1), Multiply(a, Coordinate(X("x"), 2))), k));
        Formula fibre = At(Qualified("Finset", "filter"), predicate,
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Labels())));
        return Seq(new Formula.Subscript(Sum, Member(Typed(X("x"), Labels()), fibre)),
            Sp, Parenthesized(Projector(At(X("ψ"), X("x")))));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality", "PureStateHTMBBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Projector(Formula vector) => At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "EntanglementBreakingOverlapPurity", "projector"), vector);
    private static Formula RealTrace(Formula matrix) => At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), matrix));
    private static Formula Coordinate(Formula pair, byte index) => Seq(pair, Dot, D(index));
    private static Formula X(string name) => name == "ψ" ? Psi : F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Trits() => At(Qualified("ZMod"), D(3));
    private static Formula Labels() => Parenthesized(Seq(Trits(), Sp, Times, Sp, Trits()));
    private static Formula Coordinates() => At(Qualified("Fin"), X("d"));
    private static Formula Space() => At(Qualified("EuclideanSpace"), Complexes(), Coordinates());
    private static Formula Matrices() => At(Qualified("Matrix"), Coordinates(), Coordinates(), Complexes());
    private static Formula RealNumeral(params byte[] digits) => Typed(D(digits), Reals());
    private static Formula TritNumeral(byte digit) => Typed(D(digit), Trits());
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Left, Open, value, Right, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
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
}
