using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class HoggarSicCompoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/HoggarSicCompoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/tavakolibengtssongisinrenes2020siccompounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight orthonormal fiducials generate a SIC-compound in complex dimension eight under the three-qubit Pauli action.",
        H("A SIC-compound from eight Hoggar SICs"), Blocks(
            Paragraph(Text(
                "Fin 8 indexes the integers 0 through 7, regarded as three-bit strings. "
                    + "The 64 Pauli labels are pairs in Fin 8 × Fin 8; for j = (x, z), j₁ = x and j₂ = z. "
                    + "The operation xor is bitwise addition modulo two, written ⊕, "
                    + "and val takes the integer represented by a bit string. "
                    + "The Hermitian inner product conjugates its first argument: "
                    + "⟨u, v⟩ = ∑ over b in Fin 8 of conjugate(u(b)) v(b). "
                    + "The symbol δ with indices j and l means 1 if j = l and 0 otherwise. "
                    + "Thus squared absolute values below are real, while inner products and vector entries are complex.")),
            Node("pauli", "The three-qubit Pauli action", PauliFormula(),
                "For bit strings z and a, z·a is the parity of the sum of the three products of "
                    + "corresponding bits. The displayed exponent writes that parity using integer remainders "
                    + "and floors. Thus (pauli x z u)(b) = (−1)^{z·(b ⊕ x)} u(b ⊕ x): "
                    + "the shift is applied before the sign. This is the three-qubit Pauli action used "
                    + "for the exceptional dimension-eight SICs in references [3], [51] and [52] of the source."),
            Node("IsSIC", "The SIC overlap condition in dimension eight", SicFormula(),
                "Equation (1), with d = 8, requires |⟨φ_j, φ_l⟩|² = (8δ_{jl} + 1)/9 "
                    + "for every pair of the 64 labels. The diagonal equations give unit vectors, "
                    + "and every off-diagonal squared overlap is 1/9."),
            Node("claim", "The negative answer to the exceptional-SIC question", ClaimFormula(),
                "The claim says that there are no eight vectors whose Pauli orbits are SICs and "
                    + "whose images under each Pauli operator form an orthonormal basis. "
                    + "Such vectors would give 512 states ψ_{j,k} = pauli(j.1, j.2, f(k)), "
                    + "with eight SICs as in property I and 64 orthonormal bases as in property II. "
                    + "They would therefore form a SIC-compound built from Hoggar SICs, the exceptional "
                    + "SICs of dimension eight. The paragraph on existence in dimensions 5, 6, 7 and 8 "
                    + "leaves this exceptional case open; the claim is its negative answer."),
            Describe.Lean(
                DescribeId.Create("hoggar-sic-compound-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Eight orthogonal Hoggar fiducials give a compound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Choose the following eight vectors with Gaussian-integer entries, with i² = −1:")),
                    Paragraph(Text("w₀ = (−1 + 2i, 1, 1, 1, 1, 1, 1, 1).")),
                    Paragraph(Text("w₁ = (1, i, i, i, 1 − i, 0, 0, 0).")),
                    Paragraph(Text("w₂ = (1, i, 1 − i, 0, i, i, 0, 0).")),
                    Paragraph(Text("w₃ = (1, 1 − i, i, 0, i, 0, i, 0).")),
                    Paragraph(Text("w₄ = (1, −1, −1, 1, −1, 1, 1, 1 + 2i).")),
                    Paragraph(Text("w₅ = (0, 0, 0, 1 + i, i, −i, −i, −1).")),
                    Paragraph(Text("w₆ = (0, 0, 1, −1, 0, 1 − i, −1, i).")),
                    Paragraph(Text("w₇ = (0, 1, 0, −1, 0, −1, 1 − i, i).")),
                    Paragraph(Text(
                        "Set (r₀, …, r₇) = (12, 6, 6, 6, 12, 6, 6, 6) and fₖ = wₖ/√rₖ. "
                            + "The Gram matrix of the eight vectors is diag(12, 6, 6, 6, 12, 6, 6, 6): "
                            + "for all k and l, ⟨wₖ, wₗ⟩ = rₖ if k = l and 0 otherwise. "
                            + "Consequently the normalized vectors f₀, …, f₇ are orthonormal. "
                            + "Every Pauli operator preserves inner products, so for each Pauli label "
                            + "the eight images of these vectors form an orthonormal basis.")),
                    Paragraph(Text(
                        "For every k and every non-identity Pauli label (x, z) ≠ (0, 0), "
                            + "|⟨wₖ, pauli(x, z, wₖ)⟩|² = rₖ²/9: the value is 16 for k = 0 or 4 "
                            + "and 4 for every other k. At (x, z) = (0, 0) the value is rₖ². "
                            + "After normalization, these squared self-overlaps are respectively 1/9 and 1.")),
                    Paragraph(Text(
                        "For all three-bit strings x, z, y and t and all complex vectors u, "
                            + "pauli(x, z, pauli(y, t, u)) = (−1)^{z·y} pauli(x ⊕ y, z ⊕ t, u). "
                            + "Together with preservation of inner products, this multiplication law gives "
                            + "|⟨pauli(x, z, u), pauli(y, t, u)⟩|² "
                            + "= |⟨u, pauli(x ⊕ y, z ⊕ t, u)⟩|². "
                            + "It reduces every pair overlap in each orbit to a self-overlap. "
                            + "Each orbit of fₖ therefore satisfies the SIC equations. The 512 states "
                            + "form a SIC-compound and answer the exceptional dimension-eight question positively."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tavakoli-bengtsson-gisin-renes-2020-hoggar-sic-compound-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("hoggar-sic-compound-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Index() => Call("Fin", D(8));
    private static Formula Labels() => Seq(Index(), Sp, Times, Sp, Index());
    private static Formula Vectors() => new Formula.TypeArrow(Index(), Complexes());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula XorOf(Formula left, Formula right) => Call("xor", left, right);
    private static Formula Value(Formula index) => Call("val", index);
    private static Formula Bit(Formula index, byte divisor) => Parenthesized(new Formula.Modulo(
        new Formula.Floor(new Formula.Fraction(Value(index), D(divisor))), D(2)));
    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula SquaredOverlap(Formula left, Formula right) =>
        new Formula.Power(new Formula.Absolute(Inner(left, right)), D(2));
    private static Formula Kronecker(Formula left, Formula right) =>
        new Formula.Subscript(DeltaLower, Seq(left, Comma, right));

    private static Formula PauliFormula()
    {
        Formula shifted = XorOf(V("b"), V("x"));
        Formula parity = new Formula.Modulo(Add(Add(
            Multiply(Bit(V("z"), 1), Bit(shifted, 1)),
            Multiply(Bit(V("z"), 2), Bit(shifted, 2))),
            Multiply(Bit(V("z"), 4), Bit(shifted, 4))), D(2));
        Formula sign = new Formula.Power(Parenthesized(new Formula.Negate(D(1))), parity);
        return All("x", Index(), All("z", Index(), All("u", Vectors(), All("b", Index(),
            Equal(Call("pauli", V("x"), V("z"), V("u"), V("b")),
                Multiply(sign, At(V("u"), shifted)))))));
    }

    private static Formula SicFormula() => All("phi", new Formula.TypeArrow(Labels(), Vectors()),
        IffOf(Call("IsSIC", V("phi")), All("j", Labels(), All("l", Labels(),
            Equal(SquaredOverlap(At(V("phi"), V("j")), At(V("phi"), V("l"))),
                new Formula.Fraction(Add(Multiply(D(8), Kronecker(V("j"), V("l"))), D(1)), D(9)))))));

    private static Formula PauliImage(Formula label, Formula vector) =>
        Call("pauli", new Formula.Subscript(label, D(1)), new Formula.Subscript(label, D(2)), vector);

    private static Formula ClaimFormula()
    {
        Formula orbit = Seq(LambdaLower, Sp, Typed(V("j"), Labels()), Sp, Mapsto, Sp,
            PauliImage(V("j"), At(V("f"), V("k"))));
        Formula sics = All("k", Index(), Call("IsSIC", orbit));
        Formula bases = All("j", Labels(), All("k", Index(), All("l", Index(),
            Equal(Inner(PauliImage(V("j"), At(V("f"), V("k"))),
                PauliImage(V("j"), At(V("f"), V("l")))), Kronecker(V("k"), V("l"))))));
        return IffOf(Named("claim"), new Formula.Not(Parenthesized(
            Some("f", new Formula.TypeArrow(Index(), Vectors()), And(sics, bases)))));
    }
}
