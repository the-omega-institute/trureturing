using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.NegativeExpansions;

internal sealed class BasePhiNegativePrefixTridentPreservationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lucas-gap core classifications survive the initial-value shifts that lift a core "
        + "to the full negative-prefix occurrence set.",
        H("Negative-Prefix Trident Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-gap-initial-value-translation"),
                DeclarationHandle.Create(
                    "D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation."
                        + "v_translate_initial_value_proved"),
                H("Lucas-gap sequences translate with their initial value"),
                StatementSource.FromAuthor(TranslationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adding a natural offset to every value of any of the three Lucas-gap "
                        + "families is identical to adding that offset to the initial value. "
                        + "The proof follows the common second-order recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-shifted-core-arms-are-pairwise-disjoint"),
                DeclarationHandle.Create(
                    "D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation."
                        + "three_arms_pairwise_disjoint_proved"),
                H("The three shifted core arms are pairwise disjoint"),
                StatementSource.FromAuthor(DisjointnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prefix headed by zero, unique lifting of each occurrence back to a "
                        + "core point and one of the offsets zero, one, or two forces distinct "
                        + "offset arms to be disjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("occurrence-set-lucas-gap-classification-preserved"),
                DeclarationHandle.Create(
                    "D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentPreservation."
                        + "occurrenceSet_lucas_gap_classification_proved"),
                H("The Lucas-gap classification lifts from the core to all occurrences"),
                StatementSource.FromAuthor(OccurrenceClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prefix headed by one has a single occurrence arm. A prefix headed by zero "
                        + "has exactly the union of the three translated arms, and the preceding "
                        + "disjointness theorem keeps that union pairwise disjoint."))),
                DescribeRole.Theorem))));

    private static Formula TranslationFormula() => Disp(Seq(
        Forall, Sp, F.Id("j"), Comma, Sp, F.Id("n"), Comma, Esc,
        Call("v", F.Id("a"), F.Id("b"), F.Id("r"), F.Id("n")),
        Plus, F.Id("j"), Eq,
        Call("v", F.Id("a"), F.Id("b"),
            Seq(F.Id("r"), Plus, F.Id("j")), F.Id("n"))));

    private static Formula DisjointnessFormula()
    {
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula armI = Call("Range", Call("v", Seq(F.Id("r"), Plus, i)));
        Formula armJ = Call("Range", Call("v", Seq(F.Id("r"), Plus, j)));

        return Disp(Seq(
            Forall, Sp, i, Comma, j, InMacro,
            OpenBrace, D(0), Comma, D(1), Comma, D(2), CloseBrace, Comma, Esc,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Call("Disjoint", armI, armJ)));
    }

    private static Formula OccurrenceClassificationFormula() => Disp(Seq(
        F.Id("w"), Underscore, D(0), Eq, D(1), Rightarrow, Sp,
        Call("Occ", F.Id("w")), Eq, Call("Range", Call("v", F.Id("r"))),
        Comma, RowBreak, Grp(),
        F.Id("w"), Underscore, D(0), Eq, D(0), Rightarrow, Sp,
        Call("Occ", F.Id("w")), Eq,
        Operatorname, Grp(F.Id("union")), Underscore,
        Grp(F.Id("j"), Eq, D(0)), Caret, D(2), Sp,
        Call("Range", Call("v", Seq(F.Id("r"), Plus, F.Id("j"))))));
}
