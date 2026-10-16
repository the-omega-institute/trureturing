using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class GeneralizedPseudostandardPeriodicityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Note = LibraryNoteRef.Create("D5/L/Rewriting/floriandvorakova2016periodicity");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generalized pseudostandard words and involutory reflection structure.",
        H("GeneralizedPseudostandardPeriodicity"),
        Blocks(
            Describe.Lean(DescribeId.Create("tailconditions"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.TailConditions"),
                H("TailConditions"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(V("alpha"), Sp,
                    Colon, Sp, V("Type"))), Sp, Parenthesized(Seq(V("delta"), Sp, Colon, Sp, Nat(),
                    Sp, To, Sp, V("alpha"))), Sp, Parenthesized(Seq(V("Theta"), Sp, Colon, Sp,
                    Nat(), Sp, To, Sp, V("InvAntimorphism"), Sp, V("alpha"))), Sp,
                    Parenthesized(Seq(V("k"), Sp, Colon, Sp, Nat())), Sp, Comma, Sp,
                    V("TailConditions"), Sp, V("delta"), Sp, V("Theta"), Sp, V("k"), Sp, Iff, Sp,
                    Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(V("i"), Sp, V("j"), Sp, Colon,
                    Sp, Nat())), Sp, Comma, Sp, Num(1), Sp, Leq, Sp, V("i"), Sp, To, Sp, Num(1), Sp,
                    Leq, Sp, V("j"), Sp, To, Sp, Parenthesized(Seq(V("Theta"), Sp,
                    Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"))))), Sp, Dot, Sp, V("toFun"), Sp,
                    Brackets(Seq(V("delta"), Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"), Sp,
                    Plus, Sp, Num(1))))), Sp, Eq, Sp, Parenthesized(Seq(V("Theta"), Sp,
                    Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("j"))))), Sp, Dot, Sp, V("toFun"), Sp,
                    Brackets(Seq(V("delta"), Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("j"), Sp,
                    Plus, Sp, Num(1))))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp,
                    Parenthesized(Seq(V("i"), Sp, Colon, Sp, Nat())), Sp, Comma, Sp, Num(1), Sp,
                    Leq, Sp, V("i"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(V("w"), Sp, Colon,
                    Sp, V("List"), Sp, V("alpha"))), Sp, Comma, Sp, Parenthesized(Seq(V("Theta"),
                    Sp, Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"))))), Sp, Dot, Sp, V("toFun"),
                    Sp, V("w"), Sp, Eq, Sp, V("w"), Sp, To, Sp, Parenthesized(Seq(V("Theta"), Sp,
                    Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"), Sp, Plus, Sp, Num(2))))), Sp,
                    Dot, Sp, V("toFun"), Sp, Parenthesized(Seq(Parenthesized(Seq(V("Theta"), Sp,
                    Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"), Sp, Plus, Sp, Num(1))))), Sp,
                    Dot, Sp, V("toFun"), Sp, V("w"))), Sp, Eq, Sp, Parenthesized(Seq(V("Theta"), Sp,
                    Parenthesized(Seq(V("k"), Sp, Plus, Sp, V("i"), Sp, Plus, Sp, Num(1))))), Sp,
                    Dot, Sp, V("toFun"), Sp, V("w")))))),
                AssessedProvenance.FromLiterature(Note),
                Blocks(Paragraph(Text("ArXiv v1, pages 20–21, Conjecture 29: Consider an alphabet 𝒜 with #𝒜=d and G the set of all involutory antimorphisms on 𝒜^*. Let 𝐮(Δ, Θ) be a d-ary generalized pseudostandard word, where Δ is a sequence of letters from 𝒜 and Θ is a sequence of antimorphisms from G. Then 𝐮 is periodic if and only if the following conditions are met: 1. The normalized directive bi-sequence is of the form (Δ̃, Θ̃)=(vδ₁δ₂δ₃…, σ ϑ₁ ϑ₂ϑ₃…), where |v|=|σ| and ϑᵢ(δᵢ₊₁)=ϑⱼ(δⱼ₊₁) for all i,j ∈ ℕ. 2. For all i ∈ ℕ, if w is a ϑᵢ-palindrome, then ϑᵢ₊₁(w) is a ϑᵢ₊₂-palindrome. The tail begins after k entries. Both tail indices start at one; images of letters are one-letter words."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(Seq(V("claim"), Sp, Iff, Sp, Forall, Sp,
                    Parenthesized(Seq(V("alpha"), Sp, Colon, Sp, V("Type"))), Sp,
                    Brackets(Seq(V("Fintype"), Sp, V("alpha"))), Sp, Brackets(Seq(V("DecidableEq"),
                    Sp, V("alpha"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp,
                    Parenthesized(Seq(V("delta"), Sp, Colon, Sp, Nat(), Sp, To, Sp, V("alpha"))),
                    Sp, Parenthesized(Seq(V("Theta"), Sp, Colon, Sp, Nat(), Sp, To, Sp,
                    V("InvAntimorphism"), Sp, V("alpha"))), Sp, Parenthesized(Seq(V("u"), Sp, Colon,
                    Sp, Nat(), Sp, To, Sp, V("alpha"))), Sp, Parenthesized(Seq(V("W"), Sp, Colon,
                    Sp, Nat(), Sp, To, Sp, V("List"), Sp, V("alpha"))), Sp, Comma, Sp,
                    V("Generates"), Sp, V("delta"), Sp, V("Theta"), Sp, V("u"), Sp, V("W"), Sp, To,
                    Sp, Exists, Sp, Parenthesized(Seq(V("deltap"), Sp, Colon, Sp, Nat(), Sp, To, Sp,
                    V("alpha"))), Sp, Parenthesized(Seq(V("Thetap"), Sp, Colon, Sp, Nat(), Sp, To,
                    Sp, V("InvAntimorphism"), Sp, V("alpha"))), Sp, Parenthesized(Seq(V("Wp"), Sp,
                    Colon, Sp, Nat(), Sp, To, Sp, V("List"), Sp, V("alpha"))), Sp, Comma, Sp,
                    V("Generates"), Sp, V("deltap"), Sp, V("Thetap"), Sp, V("u"), Sp, V("Wp"), Sp,
                    Land, Sp, V("IsNormalized"), Sp, V("u"), Sp, V("Wp"))), Sp, Land, Sp,
                    Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(V("delta"), Sp, Colon, Sp,
                    Nat(), Sp, To, Sp, V("alpha"))), Sp, Parenthesized(Seq(V("Theta"), Sp, Colon,
                    Sp, Nat(), Sp, To, Sp, V("InvAntimorphism"), Sp, V("alpha"))), Sp,
                    Parenthesized(Seq(V("u"), Sp, Colon, Sp, Nat(), Sp, To, Sp, V("alpha"))), Sp,
                    Parenthesized(Seq(V("W"), Sp, Colon, Sp, Nat(), Sp, To, Sp, V("List"), Sp,
                    V("alpha"))), Sp, Comma, Sp, V("Generates"), Sp, V("delta"), Sp, V("Theta"), Sp,
                    V("u"), Sp, V("W"), Sp, To, Sp, V("IsNormalized"), Sp, V("u"), Sp, V("W"), Sp,
                    To, Sp, Qualified(V("Function"), "Surjective"), Sp, V("u"), Sp, To, Sp,
                    Parenthesized(Seq(Parenthesized(Seq(Exists, Sp, Parenthesized(Seq(V("p"), Sp,
                    Colon, Sp, Nat())), Sp, Comma, Sp, Num(0), Sp, Lt, Sp, V("p"), Sp, Land, Sp,
                    Qualified(V("Function"), "Periodic"), Sp, V("u"), Sp, V("p"))), Sp, Iff, Sp,
                    Exists, Sp, Parenthesized(Seq(V("k"), Sp, Colon, Sp, Nat())), Sp, Comma, Sp,
                    V("TailConditions"), Sp, V("delta"), Sp, V("Theta"), Sp, V("k")))))))),
                AssessedProvenance.FromLiterature(Note),
                Blocks(Paragraph(Text("ArXiv v1, pages 20–21, Conjecture 29: Consider an alphabet 𝒜 with #𝒜=d and G the set of all involutory antimorphisms on 𝒜^*. Let 𝐮(Δ, Θ) be a d-ary generalized pseudostandard word, where Δ is a sequence of letters from 𝒜 and Θ is a sequence of antimorphisms from G. Then 𝐮 is periodic if and only if the following conditions are met: 1. The normalized directive bi-sequence is of the form (Δ̃, Θ̃)=(vδ₁δ₂δ₃…, σ ϑ₁ ϑ₂ϑ₃…), where |v|=|σ| and ϑᵢ(δᵢ₊₁)=ϑⱼ(δⱼ₊₁) for all i,j ∈ ℕ. 2. For all i ∈ ℕ, if w is a ϑᵢ-palindrome, then ϑᵢ₊₁(w) is a ϑᵢ₊₂-palindrome. The alphabet is any finite type. Surjectivity says that every letter occurs. Periods are positive natural numbers and are pure periods. The first conjunct also gives a normalized directive for each generated word."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result"),
                H("result"),
                StatementSource.FromAuthor(Disp(Seq(V("claim")))),
                AssessedProvenance.FromRepo(Note),
                Blocks(Paragraph(Text("Every finite alphabet admits normalization, and a normalized directive of a word using every letter satisfies the two tail conditions exactly when the word has a positive pure period."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("florian-dvorakova-2016-generalized-pseudostandard-periodicity"),
                    ResolutionKind.Proved))),
        []));

    private static Formula V(string x) => F.Id(x);
    private static Formula Qualified(Formula owner, string member) =>
        Seq(owner, Dot, Operatorname, Grp(V(member)));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Brackets(Formula x) => Seq(OpenBracket, x, CloseBracket);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
}
