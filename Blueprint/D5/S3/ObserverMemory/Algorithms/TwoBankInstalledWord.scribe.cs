using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class TwoBankInstalledWordDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-bank routing realizes each native source instruction by charged one-bit responses.",
        H("Two-Bank Installed Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bank"), Handle("Bank"),
                H("Bank contents"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A k-bit bank is a finite subset of Fin k; membership is its Boolean bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("flag"), Handle("Flag"),
                H("Five reply flags"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The five indices distinguish the four native read replies and the update acknowledgement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("address"), Handle("Address"),
                H("Literal addresses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Addresses are finite Boolean lists, including the empty root address."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("opcode"), Handle("Opcode"),
                H("Source instructions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An instruction reads one literal address, performs one update, or halts with a fixed Boolean output."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typed"), Handle("Typed"),
                H("Typed source replies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Read replies use flags zero through three; an update uses flag four. A halt has no typed reply."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word"), Handle("Word"),
                H("Complete mutable word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A word contains exactly two k-bit banks, all five flag bits, and one of eight phase values. Arbitrary flag patterns and all phase patterns are present."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("table"), Handle("Table"),
                H("Fixed source table"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A table assigns an instruction to every bank value and a successor bank to every flag. No particular source algorithm or initial encoding is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("toward"), Handle("toward"),
                H("Least differing bit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two banks differ, the least position in their symmetric difference is flipped; otherwise the bank is retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-flag"), Handle("singleFlag"),
                H("Singleton flag decoder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactly singleton flag sets decode to a reply flag. Empty sets and multiple flags do not."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("row"), Handle("Row"),
                H("Installed instruction row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each word has one instruction and one next word for each flag. Only replies typed for that instruction are actual native responses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("installed"), Handle("installed"),
                H("Total installed table"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The phase cycle is 000, 001, 011, 010, 110, 111, 101, 100, then 000. Ready rows execute the source instruction; routing rows read the root, fill the destination bank, erase the old bank, and reset the flag. Unsupported rows read the root and hold."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ready"), Handle("ready"),
                H("Two ready encodings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The left encoding stores the control in bank A at phase 000; the right encoding stores it in bank B at phase 010. The other bank and all flags are zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("routing"), Handle("Routing"),
                H("Paid routing paths"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every routing edge installs a root read and gives the same successor for every raw reply. The natural index counts these calls."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("change"), Handle("Change"),
                H("One logical change"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A change flips one bank bit, one flag bit, or advances one step of the eight-phase cycle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot"), Handle("Slot"),
                H("Logical positions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positions list the first bank, the second bank, the five flags, and the three phase bits."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-bits"), Handle("phaseBits"),
                H("Gray phase bits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eight phase values encode the stated cyclic Gray order; consecutive phases differ in exactly one bit, including the last-to-first transition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("logical"), Handle("logical"),
                H("Logical word projection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bank and flag membership give their bits; the phase contributes its three Gray bits."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-bit"), Handle("OneBit"),
                H("One Boolean coordinate changes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There is one position whose Boolean value is complemented, and every other position is retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-index"), Handle("slotIndex"),
                H("Contiguous slot order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite equivalence numbers the bank, flag, and phase positions consecutively."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("interleave"), Handle("interleave"),
                H("Zero interleaving"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Logical bits occupy the even positions and every odd position is zero. The physical length is twice the logical length minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical"), Handle("physical"),
                H("Physical word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered logical bits are interleaved with fixed zeros. For bank width k the length is 4k plus 15."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phase-index"), Handle("phaseIndex"),
                H("Phase decoding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All eight three-bit patterns decode to their phase indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("logical-equiv"), Handle("logicalEquiv"),
                H("All patterns are represented"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The word type is equivalent to all Boolean assignments on its logical slots; unsupported combinations are included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("installed-words"), Handle("installedWords"),
                H("Full installed image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The installed finite set is the complete image of physical encoding, containing exactly 2^(2k + 8) words."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("raw-reply"), Handle("RawReply"),
                H("Four native read replies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Raw read replies have four values; update acknowledgement is represented separately."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reply-flag"), Handle("replyFlag"),
                H("Read flag embedding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A raw reply maps to the corresponding one of the first four flags."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event"), Handle("Event"),
                H("Actual primitive chronology"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A read event records its literal address and actual reply; an update is a distinct event. Padding root reads remain in the chronology."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("execution"), Handle("Execution"),
                H("Charged one-bit execution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every read follows the observation at the current epoch and records its reply. Every update advances the epoch once. Each immediate response changes one physical bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-program"), Handle("sourceProgram"),
                H("Native source program"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source table becomes a native program with bank-valued controls, preserving read literals, typed successors, and halt locations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word-program"), Handle("wordProgram"),
                H("Native installed program"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete word is the native control. Installed rows determine all instructions and successors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("installed-carrier"), Handle("Installed"),
                H("Physical control carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A physical control is a word in the full installed image."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-equiv"), Handle("physicalEquiv"),
                H("Physical encoding equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Physical encoding is a bijection from complete logical words to installed physical controls."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-instruction"), Handle("physicalInstruction"),
                H("Physical row instruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unique decoded word selects the fixed instruction at each physical control."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-program"), Handle("physicalProgram"),
                H("Physical native program"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport through the physical equivalence preserves native observations and epochs without changing literal addresses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("terminates-with"), Handle("TerminatesWith"),
                H("Halting execution data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A configuration terminates with a trace when that trace reaches an installed halt. This predicate is proof data and is not consulted by a row."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("remaining"), Handle("remaining"),
                H("Remaining primitive calls"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a terminating trace exists, its length defines the remaining-call count. Otherwise this total definition returns zero, which by itself does not assert termination."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-reply-encoding"), Handle("rawReply"),
                H("Native reply encoding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four source-tree replies are encoded in the fixed flag order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-observation"), Handle("actualObservation"),
                H("Observation of the current source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The observation at epoch n reads the source after n substitutions. Only updates advance that epoch."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-rank"), Handle("sourceRank"),
                H("Rank at the current source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The remaining-call count is evaluated from the supplied actual source at epoch zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-rank-invariant"), Handle("SourceRankInvariant"),
                H("History-independent rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two terminating executions with the same observer word and equal actual sources have equal remaining-call counts, even if their histories and epoch numbers differ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typed-transfer"), Handle("typed_transfer"),
                H("Exact transfer between ready banks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every width k, table T, ready direction, bank z, and reply r typed for the source instruction, the ready row installs that same instruction. After its reply writes the flag, a root-read routing path reaches the opposite ready encoding of the successor bank. Its exact length is the weight of z plus the weight of the successor plus four in the left-to-right direction and plus six in the reverse direction. Including the source instruction gives five and seven, respectively. Filling and erasing proceed by least differing bits; the endpoint has the old bank and all flags reset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("installed-local"), Handle("installed_local"),
                H("Every total row holds or changes one bit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every table, word, and flag, the selected successor either equals the original word or satisfies the logical one-bit change relation. This includes unsupported words and does not require reachability or a typed-reply premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-rows"), Handle("physical_rows"),
                H("Sparse rows and physical one-bit responses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every table, word, and flag, neither the word nor its selected successor has adjacent occupied physical positions. The successor either holds the logical word or changes exactly one physical bit. The assertions apply to the entire installed image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-transfer"), Handle("native_transfer"),
                H("Native events and epochs are preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every observation field, ready direction, bank and starting epoch, a read instruction has an installed execution whose first event is that exact read and actual reply, followed by the counted root reads at the same epoch. An update has an execution whose first event is an update, followed by the counted root reads at the incremented epoch. Each response changes one physical bit; there are no additional updates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simulate-run"), Handle("simulate_run"),
                H("Simulation of every supplied finite source run"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite source Run, on one observation field from a bank and epoch to another bank and epoch, yields a finite installed Execution between ready encodings at the same endpoint epochs. The initial ready direction is arbitrary. The final direction and full primitive event list are supplied by the construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("installed-halt"), Handle("installed_halt"),
                H("Conditional halt transport and remaining-call rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume a finite source Run reaches a bank whose instruction halts with a fixed bit. For either initial ready direction, the installation contains exactly 2^(2k + 8) words of physical length 4k plus 15; every transfer uses at most 2k plus 7 primitives, and every row is sparse and holds or changes one bit. There exist a final ready direction and an installed event trace reaching that same fixed halt output. Every halt-ended logical Run from the entry has this endpoint and epoch; physical transport has the same existence and endpoint uniqueness. The entry rank equals the event-list length, the final rank is zero, and each reachable prefix has an execution suffix whose length equals its remaining rank. Every one-event step with a terminating suffix decreases that rank by one. Equal actual sources give history-independent ranks under the two supplied termination hypotheses. This theorem assumes the source run and halt premise: it supplies neither a particular source instruction table, its initial-word encoding, nor unconditional termination or source and storage resource bills."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(Owner + name);
}
