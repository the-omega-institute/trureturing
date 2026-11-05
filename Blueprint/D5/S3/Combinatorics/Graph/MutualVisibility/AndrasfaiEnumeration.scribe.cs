using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit finite equivalence counts labelled periodic avoiding words by transfer traces.",
        H("Enumeration prerequisites for the original identity"),
        Blocks(
            Paragraph(Text("Write P(N) for the subtype of labels : Fin N → Bool satisfying AndrasfaiLanguage.PeriodicAvoidance (List.ofFn labels). PeriodicAvoidance excludes the complete forbidden family from every finite repetition of the word. Positions have a fixed labelled origin. ClosedRun(N) retains a Boolean labelling and a live starting state in Fin 4 whose Fin.castSucc image closes under the original five-state DFA evaluation.")),
            Describe.Lean(DescribeId.Create("periodic-word-equivalence"),
                DeclarationHandle.Create(Prefix + "periodicWordEquivClosedRun"),
                H("The finite equivalence of words and closed lifts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N with N mod 3 nonzero, periodicWordEquivClosedRun N is an equivalence P(N) ≃ ClosedRun(N). The forgetful map sends a closed run to its unchanged labels. The existing exists_unique_closed_run theorem proves periodic avoidance and uniqueness. Conversely, a nonrejecting Fin 5 state has value below four and hence has a unique preimage in Fin 4 under Fin.castSucc. Equality of labels and uniqueness of the closed starting state prove injectivity; this preimage construction proves surjectivity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("periodic-word-card-eq-trace"),
                DeclarationHandle.Create(Prefix + "periodic_word_card_eq_trace"),
                H("Uniform periodic-word cardinality"), StatementSource.FromAuthor(WordCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite equivalence transports cardinality to the existing AndrasfaiCounting.closed_run_card_eq_trace theorem. The latter already preserves both Boolean labels on a shared transition. This theorem counts words only; identifying those words with actual original-host visible subsets is a separate obligation. At lengths 3m+2 with m positive, applying this count to the original graph requires a separate equivalence between its actual visible subsets and these periodic words."))), DescribeRole.Theorem),
            Paragraph(Text("The periodic-word count is a prerequisite for the original all-labelled-subset generating identity. No graph of index zero, quotient by rotations, maximality condition, independent-set substitution or eventual-only interpretation is introduced. The full original graph-count correspondence and formal power-series identity remain outside these results.")))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula WordCountFormula()
    {
        Formula n = F.Id("N");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula rat = Seq(Mathbb, Grp(F.Id("Q")));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        Formula nonzero = new Formula.Relation(Call("mod", n, D(3)), FormulaRelationOperator.NotEqual, D(0));
        Formula conditions = new Formula.Logic(positive, FormulaLogicOperator.And, nonzero);
        Formula count = Paren(Seq(Call("card", Call("P", n)), Sp, Colon, Sp, rat));
        Formula trace = Call("trace", new Formula.Power(Seq(Operatorname, Grp(F.Id("transfer"))), n));
        return Disp(Seq(Forall, Sp, Paren(Seq(n, Sp, Colon, Sp, nat)), Comma, Sp,
            new Formula.Logic(conditions, FormulaLogicOperator.Implies,
                new Formula.Relation(count, FormulaRelationOperator.Equal, trace))));
    }
}
