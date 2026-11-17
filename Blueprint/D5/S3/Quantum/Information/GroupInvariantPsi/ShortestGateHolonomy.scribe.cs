using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GroupInvariantPsi;

internal sealed class ShortestGateHolonomyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shortest qubit rotor gates and the return phase of a triangle of Bloch directions.",
        H("Shortest gates and the return phase of a Bloch triangle"), Blocks(
            Paragraph(Text(
                "A real three-vector r is represented by the Pauli combination r·σ = r₀σx + r₁σy + r₂σz "
                + "of the module C129QubitBargmann, and P_r = (1 + r·σ)/2 is its Bloch projector. In this "
                + "Pauli model of Cl(3,0) the geometric product of vectors is the matrix product and "
                + "reversion is the conjugate transpose. Unit vectors a and b are non-antipodal when "
                + "b ≠ −a; for unit vectors this is equivalent to 1 + a·b > 0.")),
            Definition("shortest-gate-rotor", "Rotor gate", "rotor",
                "rotor a b is the matrix (1 + (b·σ)(a·σ)) / √(2(1 + a·b)), the Pauli form of the "
                + "half-angle rotor (1 + ba)/√(2(1 + a·b)). The word shortest in the Lean names is a "
                + "label; no minimality statement is proved here."),
            Definition("shortest-gate-projection", "Normalized projection step", "shortestGate",
                "shortestGate b ψ is P_b ψ divided by the square root of the real part of ⟨ψ|P_b|ψ⟩. "
                + "For a unit spinor ψ with Bloch vector a, ⟨ψ|P_b|ψ⟩ is the real number (1 + a·b)/2, "
                + "which the proof of the rotor theorem establishes."),
            Definition("shortest-gate-triangle-s", "Triangle scalar", "triangleS",
                "S = 1 + a·b + b·c + c·a."),
            Definition("shortest-gate-triangle-d", "Triangle volume", "triangleD",
                "D = a·(b×c)."),
            Describe.Lean(DescribeId.Create("shortest-gate-rotor-properties"),
                DeclarationHandle.Create(Module + "rotor_shortest_gate"),
                H("The rotor gate between two Bloch directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/doran2003geometric")),
                Blocks(
                    Paragraph(Text(
                        "Let a and b be unit vectors with b ≠ −a and R = rotor a b. The theorem states "
                        + "three facts. (1) R R† = 1. (2) R (a·σ) R† = b·σ. (3) For every unit spinor ψ "
                        + "with P_a ψ = ψ, R ψ = P_b ψ / √⟨ψ|P_b|ψ⟩, so on a state with Bloch vector a the "
                        + "gate is the normalized projection onto b.")),
                    Paragraph(Text(
                        "Proof: the products (1 + (b·σ)(a·σ))(1 + (b·σ)(a·σ))† and "
                        + "(1 + (b·σ)(a·σ))(a·σ)(1 + (b·σ)(a·σ))† are computed entry by entry from the "
                        + "Pauli matrices, reducing with |a|² = |b|² = 1, and the scalar √(2(1 + a·b)) is "
                        + "positive by the non-antipodal hypothesis. For (3) the rank-one sandwich "
                        + "P_a X P_a = tr(P_a X) P_a gives ⟨ψ|X|ψ⟩ = tr(P_a X), so ⟨ψ|P_b|ψ⟩ = tr(P_a P_b) = "
                        + "(1 + a·b)/2, and R ψ = (ψ + (b·σ)ψ)/√(2(1 + a·b)) because (a·σ)ψ = ψ.")),
                    Paragraph(Text(
                        "The half-angle rotor and its Pauli representation are textbook geometric "
                        + "algebra, as in Doran and Lasenby. The repository's contribution is the formal "
                        + "statement and proof in this matrix model. Not formalized: the exponential "
                        + "forms of the end-point product and of R, the claim that conjugation by R "
                        + "preserves grade, inner products and the orthogonal complement of the rotation "
                        + "plane, and any minimality or uniqueness of R."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shortest-gate-triangle-gram"),
                DeclarationHandle.Create(Module + "triangle_gram"),
                H("Gram identity of three unit vectors"),
                StatementSource.FromAuthor(Disp(GramFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For unit vectors a, b, c the squared oriented volume is the Gram determinant "
                        + "of the three vectors. No non-antipodal hypothesis is needed.")),
                    Paragraph(Text(
                        "Proof: the general Gram identity D² = |a|²|b|²|c|² + 2(a·b)(b·c)(c·a) − "
                        + "|a|²(b·c)² − |b|²(c·a)² − |c|²(a·b)² is a polynomial identity in the "
                        + "coordinates; the unit hypotheses specialize it. This is classical linear "
                        + "algebra; the repository's contribution is the formal statement and proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("shortest-gate-triangle-holonomy"),
                DeclarationHandle.Create(Module + "shortest_gate_triangle_holonomy"),
                H("Return phase of the gates around a Bloch triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/pancharatnam1956interference"),
                    LibraryNoteRef.Create("D5/L/Quantum/samuel1988berry"),
                    LibraryNoteRef.Create("D5/L/Quantum/vanoosterom1983solid")),
                Blocks(
                    Paragraph(Text(
                        "Let a, b, c be unit vectors, pairwise non-antipodal (b ≠ −a, c ≠ −b, a ≠ −c), and "
                        + "write S = triangleS a b c and D = triangleD a b c. The theorem states four facts. "
                        + "(0) S² + D² = 2(1 + a·b)(1 + b·c)(1 + c·a), obtained from the Gram identity by "
                        + "expanding S². (1) S² + D² > 0. (2) The three gates along a → b → c → a compose to "
                        + "rotor c a · rotor b c · rotor a b = (S·1 − iD (a·σ)) / √(S² + D²). (3) For every "
                        + "unit spinor ψ with P_a ψ = ψ, the three normalized projections onto b, then c, "
                        + "then a return h ψ with h = (S − iD)/√(S² + D²).")),
                    Paragraph(Text(
                        "Fact (2) is the matrix form of the return phase; the octant e₃ → e₁ → e₂ → e₃ "
                        + "with S = D = 1 is an instance, where the product is (1 − iσz)/√2.")),
                    Paragraph(Text(
                        "Proof: expanding (1 + (a·σ)(c·σ))(1 + (c·σ)(b·σ))(1 + (b·σ)(a·σ)) with the unit "
                        + "hypotheses gives 2S·1 − 2iD(a·σ). The product of the three normalizers is "
                        + "√(8(1 + a·b)(1 + b·c)(1 + c·a)) = 2√(S² + D²) by the Gram identity. Each "
                        + "normalized projection step equals the corresponding rotor gate, which is "
                        + "unitary and carries the projector of its source onto that of its target, so "
                        + "the three steps compose to the gate product applied to ψ, and (a·σ)ψ = ψ.")),
                    Paragraph(Text(
                        "Classical context: the return phase of successive normalized projections is "
                        + "the Pancharatnam phase, placed in a general setting by Samuel and Bhandari. "
                        + "The scalar S and the oriented volume D are the real and imaginary parts of "
                        + "4 tr(P_a P_b P_c), the three-state Bargmann invariant proved in "
                        + "C129QubitBargmann, and Ω/2 = arg(S + iD) is half the solid angle of the "
                        + "triangle by the formula of Van Oosterom and Strackee. The repository's "
                        + "contribution is the formal statement and proof; the identification with the "
                        + "solid angle is not formalized here."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula GramFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula vector = Arrow(FinOf(D(3)), Reals());
        Formula ab = DotP(a, b), bc = DotP(b, c), ca = DotP(c, a);
        Formula d = At(Qualified("triangleD"), a, b, c);
        Formula one = D(1);
        Formula two = D(2);
        Formula gram = Subtract(Subtract(Subtract(
                Add(one, Multiply(Multiply(Multiply(two, ab), bc), ca)),
                Square(ab)), Square(bc)), Square(ca));
        Formula units = And(And(Equal(DotP(a, a), one), Equal(DotP(b, b), one)), Equal(DotP(c, c), one));
        Formula body = Implies(units, Equal(Square(d), gram));
        return All("a", vector, All("b", vector, All("c", vector, body)));
    }

    private static Formula DotP(Formula u, Formula v) => At(Qualified("dotProduct"), u, v);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Implies(Formula left, Formula right) => Seq(left, Sp, F.Implies, Sp, right);
    private static Formula Square(Formula value) => Seq(Parenthesized(value), Caret, Grp(D(2)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula value) => At(Qualified("Fin"), value);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(F.Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
