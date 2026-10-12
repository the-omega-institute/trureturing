using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookWeightedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookWeighted.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Weighted"),
        Blocks(
            Node("codebook_finite", "codebook_finite", "codebook finite", "For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K N : ℕ) (d : ℝ) : (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Finite", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("letter_length_le_weight", "letter_length_le_weight", "letter length le weight", "For the specified parameters, the following hypotheses imply the stated relation: (w : List Bool) : w.length ≤ Statement.letterWeight w", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weightedReadout_bounded", "weightedReadout_bounded", "weightedReadout bounded", "For the specified parameters, the following hypotheses imply the stated relation: (lang : Set (ℤ → Bool)) : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (weightedReadout lang)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("complete_lower_language_count_and_rate", "complete_lower_language_count_and_rate", "complete lower language count and rate", "For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hreset : initial false anchor < Statement.B M) (hcut : h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N) (hne : (Statement.codebook anchor K N d).Nonempty) : (∀ k, (Nat.card (WeakBook anchor K N d))^k ≤ Statement.factorCount (Statement.lowerLanguage K n d) (k*(N+20+6*M))) ∧ Real.log (Nat.card (WeakBook anchor K N d):ℝ)/Real.log 2/(N+20+6*M:ℝ) ≤ Statement.rate (Statement.lowerLanguage K n d)", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));

    private static DocumentBlock Node(string declaration, string identifier, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebookweighted-" + identifier.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
