using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class SpatiotemporalBornRuleDichotomyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Observer/fullwoodmawu2026spatiotemporalborn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A universal sequential Born representation exists exactly for a maximally mixed state or a discard-and-prepare channel.",
        H("The spatiotemporal Born rule dichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spatiotemporal-born-rule-exists"),
                DeclarationHandle.Create(Prefix + "BornRuleExists"),
                H("One operator for all sequential projective outcomes"),
                StatementSource.FromAuthor(Disp(BornRuleExistsFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "BornRuleExists asks for a single complex bipartite operator w whose trace against every tensor product p ⊗ q equals the Lüders–von Neumann sequential probability tr(ε(pρp)q). "
                    + "Here p and q are self-adjoint idempotents on the input and output spaces. Every such p occurs in the projective measurement {p, 1 − p}, and the same holds for q. "
                    + "Thus quantification over individual projections expresses the condition for all projective measurements. No positivity, self-adjointness or trace normalization is imposed on w. "
                    + "The predicate is defined for all natural dimensions, all complex matrices ρ and all complex linear maps ε; the state and channel assumptions enter the dichotomy below. "
                    + "The source gives the sequential distribution in PRA_rev.tex, lines 247–250, and this representation condition in lines 534–537 of arXiv:2507.16919v2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spatiotemporal-born-discard-prepare"),
                DeclarationHandle.Create(Prefix + "DiscardPrepare"),
                H("A fixed output density matrix"),
                StatementSource.FromAuthor(Disp(DiscardPrepareFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "DiscardPrepare means that there is one output density matrix σ such that ε(x) = tr(x)σ for every complex input matrix x. "
                    + "IsDensity requires positive semidefiniteness and trace one. The formula describes the map on all matrices, including matrices that are not states. "
                    + "This is the discard-and-prepare condition in Proposition 1, PRA_rev.tex, line 271 of arXiv:2507.16919v2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spatiotemporal-born-dichotomy-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The dichotomy in every positive finite dimension"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of positive natural dimensions d and e, every input density matrix ρ and every completely positive trace-preserving complex linear map ε, "
                    + "a universal sequential Born representation exists if and only if ρ is the identity divided by d or ε discards and prepares a fixed density matrix. "
                    + "The natural number d is cast to ℂ before division and scalar multiplication. The two alternatives may both hold. "
                    + "The necessity question appears in PRA_rev.tex, line 577 of arXiv:2507.16919v2; the displayed equivalence also includes both sufficient conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("spatiotemporal-born-dichotomy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The spectral argument and the two representations"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Assume a representing operator w exists. Complex linear combinations of self-adjoint projections span the full square matrix space: "
                        + "the spectral theorem writes each self-adjoint matrix as a real linear combination of unitary conjugates of coordinate projections, and self-adjoint matrices span the complex algebra. "
                        + "Consequently a matrix whose trace pairing with every projection is zero is itself zero.")),
                    Paragraph(Text(
                        "Fix an input projection p and an output projection q. The decomposition 1 = p + (1 − p) makes the trace pairing with w additive in the first projection. "
                        + "Substituting the sequential probabilities for p, 1 − p and 1 shows that tr(ε(ρ − pρp − (1 − p)ρ(1 − p))q) = 0. "
                        + "Trace separation and expansion of the two products give ε(pρ + ρp) = 2ε(pρp) for every projection p.")),
                    Paragraph(Text(
                        "Write |u⟩⟨v| for the rank-one matrix u v*. Products satisfy "
                        + "(|u⟩⟨v|)x(|w⟩⟨t|) = (v*xw)|u⟩⟨t|. "
                        + "If w*w = c with c a nonzero real number, then c⁻¹|w⟩⟨w| is a self-adjoint projection. "
                        + "Applying the preceding identity to this projection and clearing its scalar denominator yields "
                        + "c ε(|w⟩⟨w|ρ + ρ|w⟩⟨w|) = 2ε(|w⟩⟨w|ρ|w⟩⟨w|).")),
                    Paragraph(Text(
                        "Take orthonormal eigenvectors u and v of ρ with distinct real eigenvalues r and s. "
                        + "Set A = ε(|u⟩⟨u|), B = ε(|v⟩⟨v|), T = ε(|u⟩⟨v|) and S = ε(|v⟩⟨u|). "
                        + "For real a and b with a² + b² ≠ 0 and a complex phase z with conjugate(z)z = 1, use w = au + bzv and c = a² + b². "
                        + "Expanding its outer product and using the eigenvector equations gives an equality involving A, B, T and S. "
                        + "The choices (a,b,z) = (1,1,1), (3,4,1) and (3,4,i) first give (r − s)(A − B) = 0, "
                        + "then (r − s)(T + S) = 0 and (r − s)(−iT + iS) = 0. "
                        + "Since r ≠ s, these imply A = B and T = S = 0.")),
                    Paragraph(Text(
                        "Choose an orthonormal eigenbasis v indexed by Fin d, with real eigenvalues r. "
                        + "If every r i equals every r j, the spectral decomposition gives ρ = (r i₀)1 for any index i₀, which exists because d is positive. "
                        + "Taking traces and using tr(ρ) = 1 gives (r i₀)d = 1, hence ρ = (1/(d : ℂ))1.")),
                    Paragraph(Text(
                        "Otherwise choose i₀ and j₀ with r i₀ ≠ r j₀, and put σ = ε(|v i₀⟩⟨v i₀|). "
                        + "Comparing any basis vector with either v i₀ or v j₀ by the distinct-eigenvalue calculation shows ε(|v i⟩⟨v i|) = σ for every i. "
                        + "It also annihilates |v i⟩⟨v j| whenever their eigenvalues differ.")),
                    Paragraph(Text(
                        "For distinct i and j with the same eigenvalue, choose k with r i ≠ r k. "
                        + "For z equal to 1 and i, the vector (v i + z v j)/√2 is a unit eigenvector orthogonal to v k. "
                        + "Their eigenvalues differ, so the image of its rank-one projector equals σ. "
                        + "Expanding this projector and cancelling the already equal diagonal images gives "
                        + "conjugate(z) ε(|v i⟩⟨v j|) + z ε(|v j⟩⟨v i|) = 0. "
                        + "The two phase choices force both off-diagonal images to vanish, including within every degenerate eigenspace.")),
                    Paragraph(Text(
                        "Completeness of the eigenbasis gives the identity as the sum of |v i⟩⟨v i|. "
                        + "Multiplying an arbitrary matrix x on both sides by this sum expands x as the sum over i and j of "
                        + "((v i)*x(v j))|v i⟩⟨v j|. Applying ε leaves only the diagonal coefficients, whose sum is tr(x). "
                        + "Thus ε(x) = tr(x)σ for every x. Complete positivity makes σ positive semidefinite, and trace preservation gives tr(σ) = 1. "
                        + "This proves the discard-and-prepare alternative when the state is not scalar.")),
                    Paragraph(Text(
                        "Conversely, if ρ = (1/(d : ℂ))1, take w = (1/(d : ℂ)) times the sum over i,j in Fin d of "
                        + "Eᵢⱼ ⊗ ε(Eⱼᵢ), where Eᵢⱼ is the coordinate matrix with entry one at (i,j). "
                        + "The identity pρp = (1/(d : ℂ))p for a projection p, the coordinate-matrix expansion of ε(p), "
                        + "and the product rule for traces of tensor products give the required pairing with every p ⊗ q. "
                        + "If ε(x) = tr(x)σ, instead take w = ρ ⊗ σ. Cyclicity of trace and p² = p give tr(pρp) = tr(ρp), "
                        + "so this tensor product also has the required pairing. Both sufficient constructions use only complex linearity and the stated alternative."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fullwood-ma-wu-2026-spatiotemporal-born-dichotomy"),
                    ResolutionKind.Proved)))));

    private static Formula BornRuleExistsFormula()
    {
        Formula d = X("d"), e = X("e"), p = X("p"), q = X("q"), w = X("w");
        Formula pairs = Parenthesized(Seq(Fin(d), Sp, Times, Sp, Fin(e)));
        Formula equality = Equal(Trace(Multiply(w, At(Qualified("Matrix", "kronecker"), p, q))),
            Trace(Multiply(At(Varepsilon, Multiply(Multiply(p, Rho), p)), q)));
        Formula representation = Some(w, Matrix(pairs, pairs),
            All(p, Square(d), All(q, Square(e),
                Implication(At(Qualified("IsStarProjection"), p),
                    Implication(At(Qualified("IsStarProjection"), q), equality)))));
        return Dimensions(All(Rho, Square(d), All(Varepsilon, MatrixMap(d, e),
            Equivalence(At(Local("BornRuleExists"), Rho, Varepsilon), representation))));
    }

    private static Formula DiscardPrepareFormula()
    {
        Formula d = X("d"), e = X("e"), x = X("x");
        Formula replacement = Some(SigmaLower, Square(e),
            Conjunction(Density(SigmaLower), All(x, Square(d),
                Equal(At(Varepsilon, x), Scale(Trace(x), SigmaLower)))));
        return Dimensions(All(Varepsilon, MatrixMap(d, e),
            Equivalence(At(Local("DiscardPrepare"), Varepsilon), replacement)));
    }

    private static Formula ClaimBody()
    {
        Formula d = X("d"), e = X("e");
        Formula scalarState = Equal(Rho, Scale(
            new Formula.Fraction(Typed(D(1), Complexes()),
                Typed(At(Qualified("Nat", "cast"), d), Complexes())),
            Typed(D(1), Square(d))));
        Formula dichotomy = Equivalence(At(Local("BornRuleExists"), Rho, Varepsilon),
            Disjunction(scalarState, At(Local("DiscardPrepare"), Varepsilon)));
        return Dimensions(All(Rho, Square(d), All(Varepsilon, MatrixMap(d, e),
            Implication(Density(Rho), Implication(
                At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "ChannelAssemblageLOSRRefutation", "IsCPTP"), Varepsilon),
                Implication(LE(Typed(D(1), Naturals()), d),
                    Implication(LE(Typed(D(1), Naturals()), e), dichotomy)))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements", "SpatiotemporalBornRuleDichotomy", name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula size) => At(Qualified("Fin"), size);
    private static Formula Matrix(Formula rows, Formula columns) => At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula Square(Formula size) => Matrix(Fin(size), Fin(size));
    private static Formula MatrixMap(Formula d, Formula e) => At(
        Qualified("D5", "S3", "Quantum", "Foundation", "FiniteKrausChannel", "PhyslibLeaf", "MatrixMap"), Fin(d), Fin(e), Complexes());
    private static Formula Density(Formula value) => At(Qualified("D5", "S3", "Quantum", "Information", "SLDSpectralEnergy", "IsDensity"), value);
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula Dimensions(Formula body) => All(X("d"), Naturals(), All(X("e"), Naturals(), body));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Scale(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Conjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Disjunction(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
