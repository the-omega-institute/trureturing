using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiLanguageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact finite forbidden language and uniqueness of closed labelled lifts.",
        H("The Andrasfai forbidden language"),
        Blocks(
            Describe.Lean(DescribeId.Create("triples"), DeclarationHandle.Create(Prefix + "Triples"),
                H("Wildcard triple repetitions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Triples contains the empty word and is closed under appending [a,b,true] for arbitrary Boolean letters a,b. It is exactly the Kleene star (Sigma Sigma 1)*, including zero repetitions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("contains-forbidden"), DeclarationHandle.Create(Prefix + "ContainsForbidden"),
                H("An occurrence with arbitrary context"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite Boolean word contains a forbidden factor if it equals p ++ [true,true] ++ t ++ [true] ++ s for some arbitrary prefix p, suffix s and Triples word t. This is the entire family 11(Sigma Sigma 1)*1, not just its length-six member."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("machine"), DeclarationHandle.Create(Prefix + "machine"),
                H("The partial four-state machine as a Mathlib DFA"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From states 0,1,2,3 the transitions on letters 0,1 are respectively (0,1), (0,2), (3,reject), (1,1). The Mathlib DFA adds state 4 as an absorbing reject state, starts in state 0, and accepts all states except 4. Rejecting runs are not closed lifts of the original four-state automaton."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("accepts-iff-avoids"), DeclarationHandle.Create(Prefix + "accepts_iff_avoids"),
                H("Finite language equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite Boolean word w, the standard DFA accepts w exactly when ContainsForbidden(w) is false. Any readable 11 reaches state 2; each wildcard triple then returns to 2 or rejects, and the last 1 rejects. Rejection is absorbing, so an occurrence anywhere is fatal. Conversely a run from 0 satisfies a simultaneous suffix invariant: state 2 has a suffix 11 followed by a Triples word; state 3 adds one zero to such a suffix; state 1 either ends in 1 or adds two zeros to such a suffix; state 4 certifies an actual forbidden occurrence. Appending one letter preserves this invariant. Thus a rejected finite word contains the forbidden factor, establishing the converse without an assumed language equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-run-unique"), DeclarationHandle.Create(Prefix + "closed_run_unique"),
                H("Uniqueness at lengths not divisible by three"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite word w whose length is not divisible by three, and any states q,r other than reject, if reading w returns q to q and r to r, then q=r. This fixes the labelled starting position; there is no quotient by rotations. For two different nonrejecting runs, the unordered state pairs (0,1), (1,2), (0,3) form a three-cycle. The remaining pairs (0,2), (1,3), (2,3) have strictly decreasing ranks until they enter that cycle. Exact local transition cases prove rank monotonicity and a phase increment in Z/3Z. Induction over an arbitrary word propagates these facts. A closed pair has constant rank, hence lies in the three-cycle; its phase can return only when the word length is divisible by three, a contradiction."))), DescribeRole.Theorem),
            Paragraph(Text("Existence of a closed lift for every periodically admissible membership word, the exact periodic-word-to-subset bridge, and the matrix trace counting correspondence remain separate obligations. Finite readability and uniqueness alone do not prove the Howroyd counting identity.")))));
}
