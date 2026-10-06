using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class CPFilterTransposeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CPFilterTransposeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/marquezgonzalez2026feasibility");
    private const string StrongQuote = "This separates the higher-dimensional problem into two levels. The strong question is whether every unital qudit channel Υ is CP-filter equivalent to its transpose, i.e., whether there exist invertible CP maps ℒ and ℛ, with CP inverses, such that Υᵀ = ℒ ∘ Υ ∘ ℛ.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unital measure-and-prepare channel on three-dimensional complex matrices has diagonal transpose range and noncommuting original range. Complete positivity of a map and its inverse forces an invertible congruence, which cannot identify these ranges.",
        H("A qutrit obstruction to CP-filter equivalence with the channel transpose"),
        Blocks(
            Node("CPInvertible", "Invertibility with a completely positive inverse", InvertibleFormula(),
                "MatrixMap(Fin 3, Fin 3, complex) is the type of complex linear maps on 3 by 3 matrices. IsCompletelyPositive is the existing all-amplification predicate: for every natural n, the tensor product with the identity on Fin n maps every positive semidefinite matrix to a positive semidefinite matrix. Both inverse identities hold on every matrix. The maps need not preserve trace. PDF p. 5, Section VI, Eq. (47): “" + StrongQuote + "”"),
            Node("UnitalChannel", "Unital qutrit channels", UnitalFormula(),
                "PDF p. 2, Section II.A: “Consider completely positive trace-preserving (CPTP) maps”. PDF p. 3, Lemma 2: the scaled channel “is trace preserving and unital.” IsCPTP is the existing conjunction of all-amplification complete positivity and preservation of the matrix trace on every matrix; unitality is F(1)=1. The displayed conjunction expands that reused predicate. The carrier here is Fin 3, the qutrit instance of the dimensional question."),
            Node("claim", "The strong question at dimension three", ClaimFormula(),
                "PDF p. 5, Section VI, Eq. (47): “" + StrongQuote + "” F encodes Υ, and L and R encode ℒ and ℛ. The composition symbols denote composition of complex linear maps. PDF pp. 2–3, Section II.D: “Fix a qubit basis. If a CP map has Kraus representation Λ(X)=∑ᵢ Kᵢ X Kᵢ†, its channel transpose is the CP map Λᵀ(X)=∑ᵢ Kᵢᵀ X K̅ᵢ.” PDF p. 3: “This definition is independent of the chosen Kraus representation, although it depends on the underlying basis”. ofKraus denotes the Lean function MatrixMap.of_kraus. MatrixMap.of_kraus K K is literally X↦∑ᵢ Kᵢ X Kᵢ†. Applying that same operator to the transposed family gives the displayed full sum ∑ᵢ Kᵢᵀ X (Kᵢᵀ)†. Since (Kᵢᵀ)† = K̅ᵢ, this is the source's Eq. (16) form Kᵀ X K̅, in the fixed standard basis. Definition-fidelity table: CPInvertible is CP with a two-sided CP inverse; UnitalChannel is IsCPTP together with F 1 = 1; claim uses MatrixMap.of_kraus K K for the Kraus representation and MatrixMap.of_kraus on the transposed family for the channel transpose. Trace duality determines the Heisenberg map Y↦∑ᵢ Kᵢ† Y Kᵢ from F: tr(Y F(X))=tr((∑ᵢ Kᵢ† Y Kᵢ) X). Nondegeneracy of the trace pairing identifies this map for any two finite Kraus representations. Transposing its value on Xᵀ gives ∑ᵢ Kᵢᵀ X K̅ᵢ, so the channel transpose is independent of the Kraus family. This is the dimension-three instance of the universal dimensional question; a failure here refutes that question."),
            Node("result", "Refutation of the strong question", new Formula.Not(F.Id("claim")),
                "Take the three trace-one positive semidefinite matrices ρ₀=diag(1/2,1/3,1/6), ρ₁=[[1/6,1/12,0],[1/12,1/3,0],[0,0,1/2]], and ρ₂=[[1/3,−1/12,0],[−1/12,1/3,0],[0,0,1/3]]. They sum to the identity. The channel F(X)=∑ⱼ Xⱼⱼρⱼ is completely positive, trace preserving, and unital. Its channel transpose has diagonal range. Applying complete positivity to the unnormalized maximally entangled projector gives a positive semidefinite Choi matrix, whose spectral decomposition supplies the finite Kraus operators. The identity Kraus scalarity theorem then forces a CP map with CP inverse to be an invertible congruence X↦AXA†. Surjectivity of R would make A F(Y) A† diagonal for every Y. Commutation of these diagonal matrices, including the image of the identity, and cancellation of A and A† force ρ₀ρ₁=ρ₁ρ₀. Their commutator has entry (0,1) equal to 1/72, a contradiction. The weaker positive/CP question in Eq. (48) remains open; the source's qubit conclusions are unaffected.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("marquez-gonzalez-2026-cp-filter-transpose-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("mgfilt-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            declaration == "claim"
                ? Blocks(Paragraph(Text(prose)), Paragraph(Math(Disp(TransposeFormula()))))
                : Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. xs]);
    private static Formula At(Formula x, params Formula[] xs) => new Formula.Apply(x, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula IffOf(Formula x, Formula y) => Seq(x, Sp, Iff, Sp, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Mat => Call("Matrix", Fin3, Fin3, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Map => Call("MatrixMap", Fin3, Fin3, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula CP(Formula x) => Call("IsCompletelyPositive", x);

    private static Formula InvertibleFormula()
    {
        Formula f = F.Id("F"), g = F.Id("G"), x = F.Id("X");
        return All("F", Map, IffOf(Call("CPInvertible", f), And(CP(f), Ex("G", Map,
            And(CP(g), And(All("X", Mat, Eqn(At(g, At(f, x)), x)), All("X", Mat, Eqn(At(f, At(g, x)), x))))))));
    }

    private static Formula UnitalFormula()
    {
        Formula f = F.Id("F"), x = F.Id("X");
        return All("F", Map, IffOf(Call("UnitalChannel", f), And(
            And(CP(f), All("X", Mat, Eqn(Call("trace", At(f, x)), Call("trace", x)))), Eqn(At(f, D(1)), D(1)))));
    }

    private static Formula TransposeFormula()
    {
        Formula s = F.Id("S"), k = F.Id("K"), x = F.Id("X"), i = F.Id("i");
        Formula family = new Formula.TypeArrow(s, Mat);
        Formula transposed = TransposedFamily(s, k);
        Formula rhs = SumOver("i", s, Mul(Mul(Call("transpose", At(k, i)), x),
            Call("conjTranspose", Call("transpose", At(k, i)))));
        return All("S", F.Id("Type"),
                Seq(OpenBracket, Call("Fintype", s), CloseBracket, Sp,
                All("K", family, And(All("X", Mat,
                    Eqn(At(Call("ofKraus", transposed, transposed), x), rhs)),
                    All("i", s, Eqn(Call("conjTranspose", Call("transpose", At(k, i))),
                        Call("map", At(k, i), F.Id("star"))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("F"), s = F.Id("S"), k = F.Id("K"), l = F.Id("L"), r = F.Id("R");
        Formula family = new Formula.TypeArrow(s, Mat);
        Formula transposed = TransposedFamily(s, k);
        Formula factor = And(Call("CPInvertible", l), And(Call("CPInvertible", r),
            Eqn(Call("ofKraus", transposed, transposed), Compose(l, f, r))));
        Formula quantified = All("S", F.Id("Type"),
            Seq(OpenBracket, Call("Fintype", s), CloseBracket, Sp,
                All("K", family, Imp(Eqn(f, Call("ofKraus", k, k)), Ex("L", Map,
                    Ex("R", Map, factor))))));
        return IffOf(F.Id("claim"), All("F", Map, Imp(Call("UnitalChannel", f), quantified)));
    }

    private static Formula SumOver(string v, Formula indexType, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(v), Sp, Colon, Sp, indexType), Sp, Parenthesized(body));
    private static Formula Compose(Formula left, Formula middle, Formula right) =>
        Seq(left, Sp, Circ, Sp, middle, Sp, Circ, Sp, right);
    private static Formula TransposedFamily(Formula indexType, Formula family) =>
        Parenthesized(Seq(LambdaLower, Sp, F.Id("i"), Sp, Colon, Sp, indexType,
            Comma, Sp, Call("transpose", At(family, F.Id("i")))));
}
