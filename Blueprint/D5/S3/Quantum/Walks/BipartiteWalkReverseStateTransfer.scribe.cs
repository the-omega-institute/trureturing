using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Walks;

internal sealed class BipartiteWalkReverseStateTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/chenetal2024bipartitewalkhamiltonians");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neither seven-state matrix transfers the sixth coordinate state to the first at any natural step.",
        H("No reverse perfect state transfer in the seven-state bipartite walk"),
        Blocks(
            Definition("p", "P", "The first projection", PFormula(),
                "P is the complex matrix displayed in Hamiltonian_7.tex, lines 320–329. "
                    + "It averages coordinates within the cells {0,2,3}, {1,5}, {4} and {6}. "
                    + "Indices run from zero to six; source edge i has index i minus one.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("q", "Q", "The second projection", QFormula(),
                "Q is the complex matrix displayed in Hamiltonian_7.tex, lines 330–338. "
                    + "It averages coordinates within the cells {0,1}, {2,4}, {3} and {5,6}.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("u-disp", "Udisp", "The displayed transition matrix", UdispFormula(),
                "Udisp is the matrix printed in Hamiltonian_7.tex, lines 340–351, "
                    + "and repeated in the open questions at lines 1276–1287. "
                    + "Its entry at row 2, column 4 is positive one third.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("u-def", "Udef", "The product of the two reflections", UdefFormula(),
                "Udef is the product of the reflections associated with P and Q, "
                    + "as in Hamiltonian_7.tex, lines 154–163. The scalar two acts by natural scalar multiplication, "
                    + "and the subtracted one is the identity matrix. "
                    + "This product agrees with Udisp except that its entry at row 2, column 4 is negative one third.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("perfect-state-transfer", "PerfectStateTransfer", "Perfect state transfer", TransferFormula(),
                "For a complex matrix U on Fin n, perfect state transfer from a to b means that "
                    + "some natural power sends the coordinate vector at a to the coordinate vector at b "
                    + "times a complex phase of norm one. The evolution by powers is described in "
                    + "Hamiltonian_7.tex, lines 135–142, and the direction of transfer in line 1288. "
                    + "The predicate allows step zero and equal endpoints, and imposes no unitarity hypothesis on U.",
                AssessedProvenance.FromLiterature(Source)),
            Definition("claim", "claim", "No transfer from the sixth coordinate to the first", ClaimFormula(),
                "Neither the product of reflections nor the printed matrix admits perfect state transfer "
                    + "from index 5 to index 0. These are the source's sixth and first coordinate states. "
                    + "This states the suspicion in Hamiltonian_7.tex, line 1288, for both choices of matrix, "
                    + "including the discrepancy in their row 2, column 4 entries.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The modulo-three obstruction"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use zero-based coordinate vectors eⱼ. For an integer s, let Aₛ be the integer matrix "
                            + "whose entries are those of 3 Udisp, except that the entry at row 2, column 4 is s. "
                            + "Entrywise inclusion of integers into the complex numbers gives "
                            + "3 • Udef = A₋₁ and 3 • Udisp = A₁. Thus either matrix U has the form "
                            + "U = (1/3) • Aₛ for its corresponding s.")),
                    Paragraph(Text(
                        "Set x = (−1,0,2,2,0,0,0) and y = (2,0,0,−2,2,−1,0), as integer column vectors. "
                            + "Direct multiplication gives Aₛ e₁ = x and "
                            + "Aₛ x = (4,0,4,−2,6,−3,0) = 2 • x + 3 • y, independently of s. "
                            + "The same matrix entries and the scaling of U give U e₅ = e₆ and U e₆ = e₁.")),
                    Paragraph(Text(
                        "Reduce the integer matrix and vector entrywise to ZMod 3. The image of x is a "
                            + "nonzero eigenvector of the image of Aₛ with eigenvalue 2: its coordinate zero is −1. "
                            + "Taking the nth power of this eigenvector identity gives "
                            + "Aₛⁿ x = 2ⁿ • x in ZMod 3 for every natural n.")),
                    Paragraph(Text(
                        "Now include the integer vectors entrywise in the complex vector space. "
                            + "The first two steps and Aₛ e₁ = x give U³ e₅ = (1/3) • x. "
                            + "The equality U = (1/3) • Aₛ gives "
                            + "Uⁿ x = (1/3)ⁿ • Aₛⁿ x, hence "
                            + "Uⁿ⁺³ e₅ = (1/3)ⁿ⁺¹ • Aₛⁿ x. "
                            + "If aₙ is coordinate zero of the integer vector Aₛⁿ x, the zero coordinate "
                            + "of Uⁿ⁺³ e₅ is the complex inclusion of aₙ divided by 3ⁿ⁺¹.")),
                    Paragraph(Text(
                        "For any integer a with nonzero image in ZMod 3, the complex number "
                            + "a/3ⁿ⁺¹ cannot have norm one. Otherwise the complex norm identity gives "
                            + "|a| = 3ⁿ⁺¹ first in the reals and then in the integers. "
                            + "Since n + 1 is positive, 3 divides |a| and therefore a, contrary to its nonzero image.")),
                    Paragraph(Text(
                        "At steps zero, one and two, the zero coordinate of Uᵏ e₅ is zero. "
                            + "At step n + 3, the congruence gives aₙ = −2ⁿ in ZMod 3. "
                            + "Here 2 = −1 is a unit, so aₙ is nonzero modulo three. "
                            + "The preceding norm argument therefore excludes a unit-norm zero coordinate at every natural step.")),
                    Paragraph(Text(
                        "If perfect state transfer from index 5 to index 0 existed with phase γ, "
                            + "coordinate zero of Uᵏ e₅ = γ • e₀ would equal γ and would have norm one. "
                            + "This contradicts the coordinate bound. Applying the argument with s = −1 to Udef "
                            + "and with s = 1 to Udisp proves both exclusions."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chen-godsil-sobchuk-zhan-2024-bipartite-walk-reverse-state-transfer"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
        DescribeRole.Definition);

    private static Formula PFormula() => Equal(Typed(Local("P"), MatrixType(D(7))), MatrixLiteral(
        Row(Third, Zero, Third, Third, Zero, Zero, Zero),
        Row(Zero, Half, Zero, Zero, Zero, Half, Zero),
        Row(Third, Zero, Third, Third, Zero, Zero, Zero),
        Row(Third, Zero, Third, Third, Zero, Zero, Zero),
        Row(Zero, Zero, Zero, Zero, One, Zero, Zero),
        Row(Zero, Half, Zero, Zero, Zero, Half, Zero),
        Row(Zero, Zero, Zero, Zero, Zero, Zero, One)));

    private static Formula QFormula() => Equal(Typed(Local("Q"), MatrixType(D(7))), MatrixLiteral(
        Row(Half, Half, Zero, Zero, Zero, Zero, Zero),
        Row(Half, Half, Zero, Zero, Zero, Zero, Zero),
        Row(Zero, Zero, Half, Zero, Half, Zero, Zero),
        Row(Zero, Zero, Zero, One, Zero, Zero, Zero),
        Row(Zero, Zero, Half, Zero, Half, Zero, Zero),
        Row(Zero, Zero, Zero, Zero, Zero, Half, Half),
        Row(Zero, Zero, Zero, Zero, Zero, Half, Half)));

    private static Formula UdispFormula() => Equal(Typed(Local("Udisp"), MatrixType(D(7))), MatrixLiteral(
        Row(Zero, NegativeThird, Zero, TwoThirds, TwoThirds, Zero, Zero),
        Row(Zero, Zero, Zero, Zero, Zero, Zero, One),
        Row(Zero, TwoThirds, Zero, TwoThirds, Third, Zero, Zero),
        Row(Zero, TwoThirds, Zero, NegativeThird, TwoThirds, Zero, Zero),
        Row(Zero, Zero, One, Zero, Zero, Zero, Zero),
        Row(One, Zero, Zero, Zero, Zero, Zero, Zero),
        Row(Zero, Zero, Zero, Zero, Zero, One, Zero)));

    private static Formula UdefFormula() => Equal(Typed(Local("Udef"), MatrixType(D(7))),
        Multiply(
            Subtract(Smul(Typed(D(2), Naturals()), Local("P")), Typed(D(1), MatrixType(D(7)))),
            Subtract(Smul(Typed(D(2), Naturals()), Local("Q")), Typed(D(1), MatrixType(D(7))))));

    private static Formula TransferFormula()
    {
        Formula evolution = At(Qualified("Matrix", "mulVec"),
            new Formula.Power(Parenthesized(X("U")), X("k")),
            At(Qualified("Pi", "single"), X("a"), One));
        Formula target = Smul(GammaLower, At(Qualified("Pi", "single"), X("b"), One));
        return All("n", Naturals(), All("U", MatrixType(X("n")),
            All("a", FinOf(X("n")), All("b", FinOf(X("n")),
                Equivalence(At(Local("PerfectStateTransfer"), X("U"), X("a"), X("b")),
                    Some("k", Naturals(), Some("γ", Complexes(),
                        Conjunction(Equal(new Formula.Norm(GammaLower), Typed(D(1), Reals())),
                            Equal(evolution, target)))))))));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), Conjunction(
        NoTransfer("Udef"), NoTransfer("Udisp")));
    private static Formula NoTransfer(string matrix) => new Formula.Not(Parenthesized(
        At(Local("PerfectStateTransfer"), Local(matrix),
            Typed(D(5), FinOf(D(7))), Typed(D(0), FinOf(D(7))))));

    private static Formula Zero => Typed(D(0), Complexes());
    private static Formula One => Typed(D(1), Complexes());
    private static Formula Half => new Formula.Fraction(One, Typed(D(2), Complexes()));
    private static Formula Third => new Formula.Fraction(One, Typed(D(3), Complexes()));
    private static Formula NegativeThird => new Formula.Fraction(new Formula.Negate(One), Typed(D(3), Complexes()));
    private static Formula TwoThirds => new Formula.Fraction(Typed(D(2), Complexes()), Typed(D(3), Complexes()));
    private static Formula Row(params Formula[] entries) => Interleave(Amp, entries);
    private static Formula MatrixLiteral(params Formula[] rows) => Seq(
        Begin, Grp(F.Id("bmatrix")), Interleave(RowBreak, rows), End, Grp(F.Id("bmatrix")));
    private static Formula Interleave(Formula separator, params Formula[] values)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var value in values)
        {
            if (items.Count > 0) items.Add(separator);
            items.Add(value);
        }
        return Seq([.. items]);
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Walks",
        "BipartiteWalkReverseStateTransfer", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts) items.Add(F.Id(part));
        return Seq(Operatorname, Grp(Interleave(Dot, [.. items])));
    }
    private static Formula X(string name) => name == "γ" ? GammaLower : F.Id(name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula MatrixType(Formula n) => At(Qualified("Matrix"), FinOf(n), FinOf(n), Complexes());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
}
