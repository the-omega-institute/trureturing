using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalHistoryCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite word storage and autonomous exact prediction have different mathematical requirements.",
        H("Mechanical History Capacity and Autonomous-State Obstruction"),
        Blocks(
            Paragraph(Text(
                "For every irrational slope alpha in [0,1) and every real intercept rho, "
                + "History(n) contains all distinct length-n words at natural starts. It is "
                + "not a bounded list of tested occurrences. The List.ofFn presentation is "
                + "proved to have exactly the same words as the existing factor-complexity owner.")),
            Describe.Lean(
                DescribeId.Create("mechanical-history-cardinality"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalHistoryCapacity.card_history"),
                H("Every natural history length has n plus one actual words"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("card"), Open, F.Id("History"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, F.Id("n"), Sp, Plus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count is imported through the word-preserving correspondence. "
                    + "Truncation of actual histories is surjective. Every positive extension "
                    + "has a collision in this prefix map, with two genuine natural starts "
                    + "sharing the observed word but producing different longer words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-history-bit-capacity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalHistoryCapacity.history_bit_encoding_iff"),
                H("Exact lossless bit capacity at every length"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("AdmissibleWidths"), Open, F.Id("n"), Close,
                    Sp, Eq, Sp, OpenBrace, F.Id("b"), Sp, Colon, Sp,
                    F.Id("n"), Sp, Plus, Sp, D(1), Sp, Leq, Sp,
                    F.Id("pow"), Open, D(2), Comma, F.Id("b"), Close, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A lossless b-bit encoding exists exactly when n+1 is at most 2^b. "
                    + "Necessity is the finite injection bound. Sufficiency constructs an "
                    + "injection through the standard finite cardinal equivalences. This "
                    + "is a static encoding result, with no transition-compatibility assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-capacity-5040-width"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalHistoryCapacity.capacity5040_min_bits"),
                H("The 60-state capacity box needs exactly six bits"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("AdmissibleWidths5040"), Sp, Eq, Sp,
                    OpenBrace, F.Id("b"), Sp, Colon, Sp, D(6), Sp, Leq, Sp,
                    F.Id("b"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is Fin(5) x Fin(3) x Fin(2) x Fin(2), so it has 60 states. "
                    + "Every injective six-bit encoding leaves exactly four of the 64 bit words "
                    + "unused. Separately, actual histories of lengths 59 and 63 have 60 and "
                    + "64 word types; length 64 has 65 types and no six-bit lossless encoding. "
                    + "None of these cardinalities is asserted to be a dynamical period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-no-finite-autonomous-model"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalHistoryCapacity.no_finite_autonomous_model"),
                H("No finite autonomous state can generate the exact whole word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("FiniteExactAutonomousModel"), Sp, Rightarrow, Sp, F.Id("False")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume a finite carrier C, a fixed update step, a fixed output map, "
                        + "and states q(i+1)=step(q(i)) emitting the mechanical word exactly. "
                        + "Equal starting states force every later output to agree, giving an "
                        + "injection of each History(n) into C. At n=card(C), the inequality "
                        + "card(C)+1 <= card(C) is impossible.")),
                    Paragraph(Text(
                        "This concerns autonomous machines with no external input or clock. "
                        + "It is not an impossibility theorem for input-driven automata, DFAOs, "
                        + "Turing computation, or numerical approximation. No independent "
                        + "novelty claim is made for classical Sturmian complexity or aperiodicity."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalFactorComplexity")),
        ]));
}
