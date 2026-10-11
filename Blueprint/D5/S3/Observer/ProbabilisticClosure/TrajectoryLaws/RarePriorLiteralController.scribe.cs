using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class RarePriorLiteralControllerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController", H("Encoded-head original-event tape transfer"), Blocks(
            Paragraph(Text("Event has precisely the nine original event constructors. Its completion index is Fin 4. The original embedding changes only that index from a finite address to its natural value; all letters, registers, snapshots and controls are the original payloads. The six-slot ROM is obtained only from NativeFullResidual.eventBlock. Its exact embedding preserves acquired, rejected, accepted, completed, written, latched, moved, held and stopped events, including the third write before its latch.")),
            Paragraph(Text("CopyState has a finite scratch tape, finite head, five-way PC and one between-instruction bit latch. A read loads one addressed tape bit into the latch. A write updates one scratch cell. An emit exposes that cell without recording an output prefix. An advance moves the head by one cell. At the exhausted head the next instruction enters an absorbing halt. These instructions consult neither an actual input port nor a synthetic random port. Ticks, output lists and frame decoding are external analysis, absent from retained state.")),
            Paragraph(Text("Each frame uses the explicit sum/product codec of Option Event, with unary width 113452; absence is part of the paid frame. The renderer keeps one current frame tape and its bit head. It has no list of completed blocks, first-hit index, rejection count, input suffix or readable output archive. The generic copy theorem applies at every prefix length and every additional internal cut, including width zero.")),
            Paragraph(Text("Retained serializes actual, synthetic, pre and next Runtime together, the Service, initialization Flight, native Flight, sampler Flight, operation, slot and role. Each Flight includes the entire scanner and its countdown with its own table dimensions. RenderSnapshot adds the full installation copy, finite header scratch, current frame scratch, stage tag and framing latch. Every possible value of these fields, including malformed, retry and fault values, has an injective fixed-width code.")),
            Paragraph(Text("The fixed program image contains the original resident code padded to B0, all finite initial-field headers, all six-slot event rows, the five unary PC records and 64 zero padding bits. Those padding bits do not implement a framing interpreter. Its width is B0 plus 793800 squared plus 793800 times 24 times frameWidth plus 89. The bound is programWidth plus retainedSize plus copyWidth(programWidth) plus copyWidth(793800) plus copyWidth(frameWidth) plus 10, with copyWidth(w) equal to 10 times (w plus one) plus w. This pays the immutable image and the entire simultaneous installation copy separately.")),
            Paragraph(Text("The proved operations are a loader transfer and a current-frame transfer with retained context. frameStep reads one bit from the paid installation tape. The loaded row is proved equal to the eventBlock frame at every bit address, and actual frame execution after loading consumes that row. The opaque Loaded package proves that the frame reader's endpoint is the actual installStep iteration, retains the same context and contains programTape. Its proof fields are not retained machine registers; it does not replace loader instructions with a free load opcode. The slot remains a finite parameter; frameAddress computes its finite sum/product address as a macro. CopyState head advancement is a macro; Motor supplies the separate encoded-head scan and carry refinement. frameStep does not interpret the loaded dispatcher or derive the slot from retained control. The stage tag is charged data, not an implemented adaptive scheduler. The literal address/carry dispatcher, native and service orchestration, header and interframe scheduling, actual-operation bridge, joint marked law, original full-law equality and COMPLETE membership require further results. The transfer results do not assert those missing bridges.")),
            Paragraph(Text("Motor retains a unary thermometer head tape, its adjacent physical probe, a nine-way instruction tag, scratch tape and bit latch. Seek reads one head bit, limit tests one physical end-mask bit, move follows one adjacent physical rail, read loads one ROM bit, write changes one scratch bit, emit exposes that bit and carry writes the first false head bit before returning the probe to the fixed origin. Halt and fault are absorbing. The numerical head exists only in the checkpoint relation, never as an instruction input. The external checkpoint clock is m squared plus five times m; one complete transfer at boundary m costs two times m plus six instructions. The proved paused execution and trace match the retained four-instruction CopyState checkpoints. Width zero and the terminal seek are included. This head refinement does not execute the finite sum/product image address or the adaptive dispatcher.")),
            Paragraph(Text("TransferSnapshot retains the entire RenderSnapshot and literal installation, header and current-frame motors simultaneously. Its code includes every old Runtime, Service, Flight and copy field, every new head bit, physical probe, PC, latch and scratch bit. The fixed bound is programWidth plus motorStaticWidth plus renderWidth plus the three motorWidth terms plus one, where motorWidth(w) is 18 times (w plus one) plus (w plus one) plus w. The immutable motor records and end masks have width 81 plus (programWidth plus one) plus 793801 plus (frameWidth plus one). This bound covers every TransferSnapshot, including malformed and fault values. It is a transfer-attachment bound, not total COMPLETE charge.")),
            Paragraph(Text("literalInstallStep advances only the attached installation motor. At every actual install cut, all old renderer context, Runtime and scanner fields and both other motors remain equal to their entry values. HeadControl excludes reachable faults, and the finite-snapshot function motorRank strictly decreases until halt. Its reconstructed head count is external analysis and is not a machine register or a motorStep input. The actual installation run copies programTape. A selected installed frame is a projection using the unchanged frameAddress macro; running Motor on that row reproduces the existing original-event code and exact eventBlock. The row address is not executed by this transfer result. The adaptive dispatcher, distinct actual and synthetic ports, scanner-return decoding by paid instructions, source commit and scheduled header/six-slot streaming remain unproved.")),
            Paragraph(Text("AddressState attaches explicit unary key and offset tapes, four physical rail probes, seventeen address tags, two return continuation bits, a latch and a complete program-width Motor to the full TransferSnapshot. addressStep adds the fixed base and a fixed frame stride for each true key bit using repeated single-bit carries. Separate key and offset read/branch instructions select the continuation. A final head-bit scan reaches the actual address before readProgram reads one bit of the retained installation tape. No addressStep branch computes a product or reads addressIndex, frameAddress, an event decoder or a semantic scanner result. The product appears only in the endpoint comparison. Every intermediate cut preserves the whole outer snapshot and both raw input tapes, excludes fault and strictly decreases addressRank until returned. addressRank is the least remaining returned distance obtained from the proved execution, used only in external analysis; no instruction reads it or stores an iteration count.")),
            Paragraph(Text("The address code includes all simultaneous transfer and address fields; the static charge additionally includes base/key end masks, all seventeen opcode records and the constant zero ROM. literalAddressBound is programWidth plus addressStaticWidth plus addressWidth plus one. addressWidth is transferWidth plus addressControlWidth plus frameKeyWidth plus frameWidth plus motorWidth(programWidth), and addressControlWidth is frameBase plus one, frameKeyWidth plus one, twice (frameWidth plus one), seventeen and three added together. addressStaticWidth is motorStaticWidth plus frameBase plus one plus frameKeyWidth plus one plus 289 plus programWidth. The same charge covers every AddressState, including returned, malformed and fault values. Each explicit unary input reaches a returned bit in at most addressTimeBound instructions, where addressTimeBound is eight times programWidth squared plus forty times programWidth plus eight times frameKeyWidth plus sixteen. This ceiling is external analysis, not a retained count. When the installation tape is the proved literal loader endpoint, that bit equals the original eventROM frame bit. Preparing those input tapes from live source fields by paid instructions, complete bit execution of physical rail-probe storage, the adaptive scanner dispatcher and scheduled source/output transaction remain unresolved.")),
            Paragraph(Text("The rail model takes one adjacent physical probe move and reset to the fixed origin as primitives. Probe values are represented by Fin and included in the injective charge, while the logical copy head is the explicit unary bit tape. A stored binary probe-address implementation is not supplied. Instruction tags are interpreted by fixed case distinctions in motorStep and addressStep; paid encoded instruction fetch and tag dispatch are not proved. The immutable tag records and masks are counted, but no result identifies those records with a resident digital interpreter for motorStep or addressStep. These component bounds therefore establish neither whole-controller code charge nor original COMPLETE membership.")),
            Paragraph(Text("LiveProducer is a concrete tagged rail dispatcher. It retains the entire AddressState, native and service raw-key builders, initialization/service/native/menu scanners, encoded Runtime and Service return-word motors, twenty-three stage tags, raw operation, ready-role selector, service-code latch, reset probe, two request flags and the two distinct port latches. Its key builders read unary bits and execute fixed four- and two-carry loops before preparing the native and service scanner queries. The original prepared relation remains an analysis relation. Its transition does not call runtimeStep, microStep, scannerResult, a Runtime/Service decoder, firstHit, serialReady, serialOperation or a mathematical endpoint evaluator. Service menu semantics occurs only in the fixed table definition; its resident bit-access realization remains unproved.")),
            Paragraph(Text("The proved live native path runs key preparation, the frozen native scanner transition, encoded return-word copying, the retained address subroutine, one output bit and commit. A commit flag selects the new physical Runtime word; returnedRuntime decodes that word only in external refinement. The raw operation register similarly determines returnedOperation outside the instruction transition. For every legal supplied operation, this path commits exactly runtimeStep and returns that original Operation. Its selected output bit equals the original eventROM bit under the prepared entry relation. Every cut preserves all inherited actual/synthetic/pre/next Runtime and scanner context. The complete native path excludes fault and decreases the least remaining deterministic return distance before returned; this rank is never a machine input.")),
            Paragraph(Text("The legacy prepared acquisition relation requests the source port once, stores its bit as a raw Read tag, prepares the native query by carries and commits the corresponding original Runtime and Operation. The fresh port is a different argument and is ignored on this acquisition path. This source bridge still uses the preprepared read-zero renderer row: an acquired one has no proved matching event-row preparation. It therefore supplies no faithful full source-event stream. Ready-role classification, pending/delivered dispatch from the current encoded source, initialization/header scheduling, six-slot progression, interframe output, canonical ready reset and repeated-service refinement are unfinished. The native scanner refinement directly applies serial_adaptive_execution at its finite flight endpoint. The service and initialization branches remain staged code without a complete adaptive execution bridge. No result connects the live service input/key/reset stages to the actual scanner and menu return or supplies arbitrary repeated service execution. repeated_fresh_bit_service is not a live consumer of this result.")),
            Paragraph(Text("The entire dispatcher code is injective and every State fits programWidth plus staticWidth plus stateWidth plus one. stateWidth is addressWidth plus both key widths, all four scanner widths, both motor widths and the full control product. A key width is m plus k plus one plus m plus one plus k times m plus one plus six plus k; scanner width is the existing scannerCodec product. The control product pays all twenty-three stages, the four operation tags, five ready roles, both 21505-way latches, both request/commit bits and both binary input latches. staticWidth includes addressStaticWidth, 529 unary stage-record bits, all key/return-word end masks and every key/payload bit of the 21504-by-8 menu table. This covers every internal, input, output, fault and retry State value, including malformed values, within the rail model. It does not prove a literal digital interpreter or original COMPLETE charge.")),
            Paragraph(Text("Atomic primitives still include finite stage case dispatch, stored Fin probe/counter motion and reset, scanner-entry register reset, raw scanner-index latch wiring, supplier installedGraphStep opcode/row access and copying a tape reference into the key input. The charged stage records are not fetched or decoded by the dispatcher. No theorem identifies its scanner accesses or menu table with the copied resident image at every physical bit cut. The committed source is an externally interpreted encoded word, while the inherited actual Runtime is a saved snapshot. Original canonical ready scratch and an executable repeated original-controller cycle are not established. The initial header, whole six-slot output schedule, both distinct request protocols over every original source constructor and the common serial Runtime/operation law remain required for Unit1; Unit2 and COMPLETE/U are not conclusions.")),
            Paragraph(Text("CurrentBank contains separate physical actual and synthetic unary Runtime banks, a frozen pre-copy motor, a carry-built raw native query, an installed scanner, a raw payload tape, a result motor, a field-projection motor, a raw event-row key, six-slot and frame-offset tags, a read/write bank latch and a resident opcode motor. The selected physical bank is copied by Motor before query preparation. The native carry loop writes the actual query tape. A native scan reads both key and payload bits of the retained installation tape, and every scanner microstep first copies the twelve opcode and branch bits of its resident instruction record. Opcode decoding tests those captured bits. The concrete Current producer retains the original dispatcher snapshot and CurrentBank together, with a charged binary acquisition tag. Acquisition captures the original Read operation from the actual source port, and every subsequent deterministic instruction executes this same current-bank path. The original prepared dispatcher remains an analysis relation used by the retained transaction theorem.")),
            Paragraph(Text("The field projection copies the last bit of each fixed 24092-bit Runtime block. For a physically valid unary Runtime word, these paid copied bits encode exactly its original fields. The event-row key is formed by the existing carry builder with stride twenty-four and the raw operation-times-six plus slot tail. It therefore uses the transaction's own captured Operation. The output branch advances offsets in original order, then slots from zero through five. Only one bit is exposed at each emit cut, and no output prefix is retained. The writeback branch reads one result bit into a latch, then writes one cell of the role-selected bank; it shifts the optional Runtime representation by one cell and preserves all fields, monitor and mode. Synthetic cuts preserve the entire actual physical bank.")),
            Paragraph(Text("current_bank_paid_fetch starts from an installed physical image, two raw banks and a captured operation with query, result and event row unprepared. It proves a live producer prefix to the paid native query and resident opcode-fetch cut, preserving the banks and captured operation. Under the stated installed-image, query and opcode-tape relations, one installed-bit scanner transition equals the supplier's graph transition. Separately, the result-copy entry relation gives a finite bitwise target-bank writeback, and a valid pre-copy gives the exact original field tape. These conditional suffix clauses alone do not state native retirement. The separate original-frame result joins the renderer and writeback. Canonical clearing and the next original query remain unproved.")),
            Paragraph(Text("CurrentBank.width counts both physical banks, the full pre-copy motor, native key builder, raw native query, scanner, raw payload, full optional result motor, field motor, event-row builder, opcode motor and all role/operation/slot/offset/probe/latch/phase controls. Current.width additionally counts the whole retained LiveProducer snapshot and the acquisition tag. Its static image contains the inherited image and two hundred additional unary control-record bits for fourteen phases and two outer tags. The inherited AddressState simultaneously retains all prior actual/synthetic/pre/next Runtime values, Service, Flights, images, head and scratch fields. The bound covers every State value, including malformed, install, output, fault and retry cuts. CurrentBank nativeBit, fieldROM and opcodeROM use fixed finite arithmetic address maps; adjacent Fin movement, opcode tag matching, query/row resets and whole-reference key wiring remain macro primitives. Paid native addresses and canonical scratch reset, full header/framing, pending/delivered classification, fresh service, common execution law and original COMPLETE/U are unresolved.")),
            Paragraph(Text("current_bank_native_payload joins the unprepared physical-bank entry to the installed native key and payload scan. The copied twelve-bit opcode record supplies every scanner microstep. A prefix invariant identifies each copied payload cell and its accumulator. The successful optional Runtime payload is then copied into the result motor, and the preserved old Runtime supplies the paid field-projection copy. The copied-field endpoint has the raw event-row key initialized from those old fields and this same captured Operation, at slot and offset zero. Executing that row carry and the installed address subroutine then reaches an output cut whose first bit is exactly the original first frame bit for those same fields and Operation. For each actual source bit x and arbitrary fresh-port value y, when the selected role is actual and the captured Operation is Read x, the same paid path starts from the actual acquisition step with x and y. Thus both Read values use their own original event row. The actual and synthetic banks remain unchanged on this prefix. Address arithmetic, finite phase dispatch and scanner resets retain the stated macro boundaries. These prefix clauses do not state full six-slot output or target-bank commit; the separate original-frame result supplies that suffix. Canonical ready reset remains unproved.")),
            Paragraph(Text("current_bank_original_frames consumes the unprepared current-bank payload path and executes the same controller's six slots, each at every offset from zero through frameWidth minus one. Row preparation and address execution are silent. Each phase-seven cut emits exactly one installed-image bit before phase eight advances its offset; the final offset advances the slot only after that frame has completed. The external trace of this complete rendering and writeback suffix is exactly the flattened six original frame codes in slot order. Every paused output trace is a prefix of that exact stream. Decoding the six fixed frame words gives the unchanged original eventBlock. The successful native run has no fault cut, including after retirement, and every cut in the synthetic role preserves the entire actual physical bank. The result tape and frozen old fields remain the same throughout rendering. Only after slot five finishes does phase nine begin its bitwise target-bank writeback. The endpoint actual and synthetic tapes identify the unchanged opposite bank and the exact full successor Runtime bank, including fields, monitor and mode. Both acquired Read values select their own original event row. The endpoint is phase eleven with retained working data. A finite-control invariant makes the preceding native-query preparation prefix silent, so the theorem also records this exact trace from the unprepared physical-bank entry through full writeback. It supplies neither the initial header/interframe protocol nor canonical Ready, scratch clearing, a return handshake, lawful pending/delivered dispatch, live fresh service, a resident literal interpreter, COMPLETE membership or U.")),
            Paragraph(Text("Return is a successor-local controller that delegates the retained Current segment through its first phase-eleven retirement. A paid acknowledgement starts a fixed sweep of eighteen current-core buffers. Each sweep instruction writes one scratch cell; a separate fifty-instruction control sequence sets the core's finite probes, heads, carries, PCs, roles and latches. Both physical Runtime banks and the installed image remain retained. The core-ready relation is the reset Current.entry together with the reset menu motor. Saved LiveProducer state and outer TransferSnapshot scratch remain present, so this is not full canonical Ready.")),
            Paragraph(Text("The next menu round copies fourteen control bits from the committed physical actual bank by the encoded-head motor. These copied bits gate pending states to their matching Stop operation, delivered states to no acquisition, and active states to a distinct actual-source acquisition stage. The source bit sets that same raw Read operation. Paid native key construction then reads the committed bank and reaches the exact original Runtime/Operation query. Runtime and menu decoding occur only in the external proof relation. The control tap arithmetic, finite tag dispatch and rail resets remain macros; the fresh request remains false. This construction supplies neither paid installed service dispatch nor fresh initialization, rejection, reset or persistent synthetic service.")),
            Node("current-bank-paid-core-return", "current_bank_paid_core_return", "Paid current-core return and committed-bank re-entry",
                "The unchanged original frame/writeback producer reaches a connected paid scratch-erasure and control-reset endpoint. Its next original-menu operation acquires its own Read bit, accepts only the matching pending Stop, rejects delivered acquisition and prepares the native query from the committed actual bank. The universal injective image-plus-state bound includes the retained producer, menu motor and return controls at every state. Full canonical Ready, literal instruction refinement, live fresh service and COMPLETE/U remain unresolved."),
            Node("current-bank-original-frames", "current_bank_original_frames", "Six original frame words and full bank writeback",
                "The same unprepared physical-bank producer reaches its old-field row, streams all six original frame codes in exact slot/offset order, and then writes the entire successor Runtime to its selected physical bank while preserving the opposite bank. Every paused output is a prefix of this exact stream, its decoded frame list is the original eventBlock, and all cuts exclude fault and preserve the actual bank in the synthetic role. Actual Read zero and one retain their own acquired Operation. Phase eleven retains work and is not canonical Ready; the exact output claim covers the unprepared physical-bank entry through rendering and writeback."),
            Node("current-bank-native-payload", "current_bank_native_payload", "Physical bank through installed payload and field copy",
                "A current physical bank and raw captured Operation, with all work tapes initially unprepared, reach the original successful Runtime payload, its copied result tape and the original old-field tape. The first event-row key uses this same Operation, and its actual carry and installed address execution expose the original first frame bit. No full retirement, canonical-ready cycle or COMPLETE/U conclusion is asserted."),
            Node("current-bank-paid-fetch", "current_bank_paid_fetch", "Physical bank to resident opcode prefix",
                "An unprepared current-bank entry reaches the live query and paid resident opcode cut. Installed key/payload accesses refine the native scanner under exact physical relations. A role-selected bitwise writeback preserves the other actual bank during synthetic work. This is a prefix and conditional-suffix result; the full native retirement and canonical-ready cycle remain required."),
            Node("tagged-source-commit", "tagged_source_commit", "Tagged encoded source transaction",
                "An injectively charged concrete rail producer commits each legal prepared native operation and its encoded Runtime, consumes a paid address return and emits the corresponding prepared event bit. Its deterministic native cuts preserve saved context, exclude fault and decrease a finite-snapshot return rank. An actual source Read selects and commits its original Runtime/Operation through the same native path; renderer-row preparation for that acquired bit remains outside the bridge."),
            Node("charged-address-execution", "charged_address_execution", "Paid unary address and installed bit",
                "The complete address-state code is injective and fits a fixed image-plus-state bound at every value. Every cut preserves the outer snapshot and raw input tapes, excludes fault and decreases an external deterministic rank until return. For every finite unary key and offset, the actual carry and branch run returns the selected installed bit, and proved literal installation identifies each selected event-frame bit with the original eventROM."),
            Node("charged-literal-transfers", "charged_literal_transfers", "Charged literal installation and frame transfer",
                "The full attachment code is injective and bounded at every value. Every install cut preserves concurrent context, has a valid encoded head, excludes fault and decreases a deterministic rank. Paused installation matches exact motor checkpoints, the installed tape is the actual program image and selected row traces reproduce the original eventBlock."),
            Node("encoded-head-copy-refinement", "encoded_head_copy_refinement", "Encoded head at every paused instruction",
                "For every finite ROM, the actual head-bit scan and carry execution reaches the exact macro checkpoint tape and trace, preserves all residual instruction cuts, copies the complete tape and reaches a permanent halt."),
            Node("six-slot-original-events", "six_slot_original_events", "Exact original six-slot ROM",
                "For every finite field state and operation, the original block has at most six events, every emitted completion index is below four, and the embedded present ROM slots equal that exact block."),
            Node("paused-copy-refinement", "paused_copy_refinement", "Every paused tape transfer",
                "After m complete four-instruction transfers, all subsequent internal states and observations equal execution from the exact prefix checkpoint. At the full width the scratch equals the ROM, and the exhausted instruction halts permanently."),
            Node("streamed-original-events", "streamed_original_events", "Current original frame output",
                "Each actual copy trace emits the complete code of its selected finite frame and retains that tape. Decoding the six external frame traces gives exactly the original event block."),
            Node("charged-installed-frames", "charged_installed_frames", "Charged installation and current frames",
                "The complete snapshot encoding is injective and every value fits the fixed budget. The loader installs the actual image tape. Current-frame instructions read that installed image, satisfy the paused invariant with retained context and emit the exact original block under finite macro addressing."),
            Node("streamed-original-history", "streamed_original_history", "Original source-history replay",
                "For every lawful nativeDrive prefix, the streamed frame blocks reconstruct the original full output and replay to its actual finite fields. The operations and iteration indices are external proof coordinates, not retained machine inputs.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode"))]));

    private static Formula App(string name, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Comma, Sp));
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return F.Seq(terms.ToArray());
    }
    private static Formula N(string name)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        var parts = name.Split('.');
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) terms.Add(Dot);
            terms.Add(Seq(Operatorname, Grp(F.Id(parts[i]))));
        }
        return F.Seq(terms.ToArray());
    }
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ListOf(Formula x) => App("List", x);
    private static Formula FinOf(Formula x) => App("Fin", x);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Land, Sp, Open, b, Close, Close);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Star, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Field(Formula x, string s) => Seq(Open, x, Close, Dot, N(s));
    private static Formula Fn(string x, Formula ty, Formula body) =>
        Seq(Open, N("fun"), Sp, N(x), Sp, Colon, Sp, ty, Sp, Mapsto, Sp, body, Close);
    private static Formula Pair(Formula a, Formula b, Formula c) =>
        Seq(Open, a, Comma, b, Comma, c, Close);
    private static Formula With(Formula x, string f, Formula value) =>
        Seq(OpenBrace, x, Sp, N("with"), Sp, N(f), Sp, Colon, Eq, Sp, value, CloseBrace);
    private static Formula Iter(Formula fn, Formula ticks, Formula state) =>
        Seq(Open, fn, Close, Caret, Grp(Seq(OpenBracket, ticks, CloseBracket)), Sp, state);
    private static Formula Cp(Formula rom, Formula m, Formula hm) => App("copyCheckpoint", rom, m, hm);
    private static Formula Run(Formula rom, Formula start, Formula ticks) => App("copyRun", rom, start, ticks);
    private static Formula Trace(Formula rom, Formula start, Formula ticks) => App("copyTrace", rom, start, ticks);
    private static Formula PrefixBits(Formula rom, Formula m) =>
        App("List.ofFn", Fn("i", FinOf(m), App("rom", App("Fin.castLE", N("hm"), N("i")))));
    private static Formula Frame(Formula f, Formula op, Formula slot) => App("eventROM", f, op, slot);
    private static Formula Rom(Formula f, Formula op, Formula slot) => App("frameTape", Frame(f, op, slot));
    private static Formula Decoded(Formula f, Formula op) =>
        App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame",
                Trace(Rom(f, op, N("slot")), N("renderFrame"), Mul(D(4), N("frameWidth"))))))));
    private static Formula InstalledDecoded(Formula state) =>
        App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame",
                Trace(App("installedFrameROM", App("installed", state), N("slot")),
                    N("renderFrame"), Mul(D(4), N("frameWidth"))))))));
    private static Formula CopyConclusion()
    {
        var rom = N("rom"); var w = N("w"); var m = N("m"); var r = N("r");
        var cp = Cp(rom, m, N("hm")); var start = App("copyEntry", w);
        var ticks = Add(Mul(D(4), m), r);
        var equality = And(EqF(Run(rom, start, ticks), Run(rom, cp, r)),
            EqF(Trace(rom, start, ticks), Seq(PrefixBits(rom, m), Sp, Plus, Plus, Sp, Trace(rom, cp, r))));
        var paused = All("m", Nat, All("hm", Le(m, w), All("r", Nat, equality)));
        var installed = EqF(Field(Run(rom, start, Mul(D(4), w)), "tape"), rom);
        var stopped = All("n", Nat, EqF(Run(rom, start, Add(Add(Mul(D(4), w), D(1)), N("n"))),
            With(Cp(rom, w, Seq(N("le"), Underscore, Grp(N("rfl")))), "pc", N("CopyPC.halt"))));
        return And(paused, And(installed, stopped));
    }

    private static DocumentBlock.Describe Node(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Statement(string name) => name switch
    {
        "current_bank_paid_core_return" => CurrentBankCoreReturn(),
        "current_bank_original_frames" => CurrentBankFrames(),
        "current_bank_native_payload" => CurrentBankPayload(),
        "current_bank_paid_fetch" => CurrentBankFetch(),
        "tagged_source_commit" => TaggedSourceCommit(),
        "charged_address_execution" => LiteralAddress(),
        "charged_literal_transfers" => LiteralTransfers(),
        "encoded_head_copy_refinement" => MotorRefinement(),
        "six_slot_original_events" => SixSlots(),
        "paused_copy_refinement" => All("w", Nat, All("rom", Arrow(FinOf(N("w")), N("Bool")), CopyConclusion())),
        "streamed_original_events" => StreamedEvents(),
        "charged_installed_frames" => ChargedFrames(),
        "streamed_original_history" => StreamedHistory(),
        _ => throw new System.InvalidOperationException(name)
    };

    private static Formula Both(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--) result = And(xs[i], result);
        return result;
    }
    private static Formula Some(Formula x) => App("some", x);
    private static Formula Ex(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula CurrentBankCoreReturn()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var r = N("r"); var cur = Field(Field(r, "current"), "current"); var t = N("t");
        var outer = Field(Field(cur, "addressed"), "outer");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        Formula Select(Formula yes, Formula no) => Seq(Open, N("if"), Sp, role,
            Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no, Close);
        var next = Word(App("runtimeCodec", d));
        var start = App("LiveProducer.Return.entry", App("LiveProducer.Current.entry",
            saved, image, a, c, role, App("operationCodec", op)));
        var round = All("w", N("Runtime"), Arrow(
            EqF(Field(cur, "actual"), Word(App("runtimeCodec", N("w")))),
            App("LiveProducer.Return.NextRound", r, N("w"))));
        var endpoint = Ex("t", Nat, Ex("r", N("LiveProducer.Return.State"), Both(
            EqF(App("LiveProducer.Return.run", start, D(0), D(0), t), r),
            EqF(r, App("LiveProducer.Return.coreReady", saved, outer, Select(a, next), Select(next, c))),
            EqF(Field(Field(outer, "installation"), "tape"), N("programTape")), round)));
        var charge = All("s", N("LiveProducer.Return.State"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("LiveProducer.Return.staticImage"), "length")),
                Field(App("LiveProducer.Return.code", N("s")), "length")), N("LiveProducer.Return.bound")));
        var ports = Arrow(EqF(App("LiveProducer.Return.actualRequest", N("q")), N("false")),
            EqF(App("LiveProducer.Return.step", N("q"), N("x"), N("y")),
                App("LiveProducer.Return.step", N("q"), N("u"), N("v"))));
        foreach (var name in new[] { "v", "u", "y", "x" }) ports = All(name, N("Letter"), ports);
        ports = All("q", N("LiveProducer.Return.State"), ports);
        var body = Both(App("Function.Injective", N("LiveProducer.Return.code")), charge, ports, endpoint);
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(Select(c, a), Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankFrames()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var p = N("p"); var q = N("q"); var pc = Field(p, "current"); var qc = Field(q, "current");
        var tp = N("tp"); var tr = N("tr");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        Formula Select(Formula yes, Formula no) => Seq(Open, N("if"), Sp, role,
            Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no, Close);
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role,
            App("operationCodec", op));
        var next = Word(App("runtimeCodec", d));
        var frames = Field(App("List.ofFn", Fn("slot", FinOf(D(6)), App("bitCode",
            App("frameCodec", App("eventROM", Field(z, "fields"), op, N("slot")))))), "flatten");
        var bankStart = App("LiveProducer.CurrentBank.entry", image, a, c, role, App("operationCodec", op));
        var paused = All("k", Nat, Arrow(Le(N("k"), Add(tp, tr)),
            Ex("suffix", ListOf(N("Bool")), EqF(frames,
                Seq(App("LiveProducer.CurrentBank.trace", bankStart, N("k")), Sp,
                    Plus, Plus, Sp, N("suffix"))))));
        var cut = App("LiveProducer.CurrentBank.run", bankStart, N("n"));
        var cuts = All("n", Nat, And(
            Seq(Field(cut, "phase"), Sp, Neq, Sp, D(1,2)),
            Arrow(EqF(role, N("true")), EqF(Field(cut, "actual"), a))));
        var decoded = App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame", App("bitCode",
                App("frameCodec", App("eventROM", Field(z, "fields"), op, N("slot")))))))));
        var acquired = App("LiveProducer.Current.step",
            App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y"));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            Arrow(EqF(role, N("false")), Arrow(EqF(op, App("Operation.read", N("x"))),
                EqF(App("LiveProducer.Current.run", acquired, D(0), D(0), Add(tp, tr)), q)))));
        var body = Ex("tp", Nat, Ex("p", N("LiveProducer.Current.State"),
            Ex("tr", Nat, Ex("q", N("LiveProducer.Current.State"), Both(
                EqF(App("LiveProducer.Current.run", start, D(0), D(0), tp), p),
                EqF(Field(p, "acquiring"), N("false")), EqF(Field(pc, "phase"), D(5)),
                EqF(App("LiveProducer.Current.run", p, D(0), D(0), tr), q),
                EqF(Field(qc, "phase"), D(1,1)),
                EqF(Field(qc, "actual"), Select(a, next)),
                EqF(Field(qc, "synthetic"), Select(next, c)),
                EqF(Field(qc, "operation"), App("operationCodec", op)),
                EqF(Field(qc, "role"), role),
                EqF(Field(Field(Field(qc, "addressed"), "outer"), "installation.tape"), N("programTape")),
                EqF(App("LiveProducer.CurrentBank.trace", pc, tr), frames),
                EqF(App("LiveProducer.CurrentBank.trace",
                    App("LiveProducer.CurrentBank.entry", image, a, c, role, App("operationCodec", op)),
                    Add(tp, tr)), frames), paused, cuts,
                EqF(decoded, App("eventBlock", Field(z, "fields"), op)), acquisition)))));
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(Select(c, a), Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankPayload()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var q = N("q"); var cur = Field(q, "current"); var t = N("t");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role,
            App("operationCodec", op));
        var payload = Word(App("optionalRuntimeCodec", Some(d)));
        var fields = Word(App("fieldsCodec", Field(z, "fields")));
        var operation = App("operationCodec", op);
        var tail = Seq(Langle, Sp, Mul(Field(operation, "val"), D(6)), Sp, Rangle);
        var acquired = App("LiveProducer.Current.step",
            App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y"));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            Arrow(EqF(role, N("false")), Arrow(EqF(op, App("Operation.read", N("x"))),
                EqF(App("LiveProducer.Current.run", acquired, D(0), D(0), t), q)))));
        var returned = N("r"); var returnedCurrent = Field(returned, "current");
        var emits = Ex("n", Nat, Ex("r", N("LiveProducer.Current.State"), Both(
            EqF(App("LiveProducer.Current.run", q, D(0), D(0), N("n")), returned),
            EqF(Field(returnedCurrent, "phase"), D(7)),
            EqF(App("LiveProducer.Current.output", returned),
                Some(App("frameTape", App("eventROM", Field(z, "fields"), op, D(0)), D(0)))),
            EqF(Field(returnedCurrent, "actual"), a),
            EqF(Field(returnedCurrent, "synthetic"), c))));
        var body = Ex("t", Nat, Ex("q", N("LiveProducer.Current.State"), Both(
            EqF(App("LiveProducer.Current.run", start, D(0), D(0), t), q),
            EqF(Field(q, "acquiring"), N("false")), EqF(Field(cur, "phase"), D(5)),
            EqF(Field(cur, "payload"), payload), EqF(Field(Field(cur, "native"), "pc"), D(2)),
            EqF(Field(cur, "actual"), a), EqF(Field(cur, "synthetic"), c),
            EqF(Field(cur, "operation"), operation), EqF(Field(cur, "role"), role),
            EqF(Field(Field(Field(cur, "addressed"), "outer"), "installation.tape"), N("programTape")),
            EqF(Field(Field(cur, "result"), "tape"), payload),
            EqF(Field(Field(cur, "pre"), "tape"), Word(App("runtimeCodec", z))),
            EqF(Field(Field(cur, "fields"), "tape"), fields),
            EqF(Field(cur, "slot"), D(0)), EqF(Field(Field(cur, "offset"), "val"), D(0)),
            EqF(Field(cur, "row"), App("LiveProducer.keyEntry", fields, tail)), acquisition, emits)));
        var selected = Seq(Open, N("if"), Sp, role, Sp, N("then"), Sp, c,
            Sp, N("else"), Sp, a, Close);
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(selected, Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankFetch()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var op = N("op"); var q = N("q");
        var cur = Field(q, "current"); var t = N("t");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        var producer = N("LiveProducer.Current.State"); var bank = N("LiveProducer.CurrentBank.State");
        Formula Word(Formula x) => App("LiveProducer.word", x);
        var query = Word(App("nativeKeyCodec", Seq(Open, z, Comma, op, Close)));
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role, App("operationCodec", op));
        var selected = Seq(Open, N("if"), Sp, role, Sp, N("then"), Sp, c, Sp, N("else"), Sp, a, Close);
        var fetched = Ex("t", Nat, Ex("q", producer, Both(
            EqF(App("LiveProducer.Current.run", start, D(0), D(0), t), q),
            EqF(Field(q, "acquiring"), N("false")), EqF(Field(cur, "phase"), D(2)),
            EqF(Field(cur, "query"), query),
            EqF(Field(cur, "native"), App("scannerEntry", App("nativeKeyCodec", Seq(Open, z, Comma, op, Close)))),
            EqF(Field(Field(cur, "opcodes"), "tape"), App("LiveProducer.CurrentBank.opcodeTape", D(0))),
            EqF(Field(cur, "actual"), a), EqF(Field(cur, "synthetic"), c),
            EqF(Field(cur, "operation"), App("operationCodec", op)), EqF(Field(cur, "role"), role),
            EqF(Field(Field(Field(cur, "addressed"), "outer"), "installation.tape"), N("programTape")))));
        var preparation = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")),
            Arrow(EqF(selected, Word(App("runtimeCodec", z))), fetched));
        var native = Field(q, "native");
        var scanner = All("q", bank, Arrow(
            EqF(Field(Field(Field(q, "addressed"), "outer"), "installation.tape"), N("programTape")),
            Arrow(EqF(Field(q, "query"), Word(Field(native, "query"))),
            Arrow(EqF(Field(Field(q, "opcodes"), "tape"), App("LiveProducer.CurrentBank.opcodeTape", Field(native, "pc"))),
                EqF(Field(App("LiveProducer.CurrentBank.scanStep", q), "native"),
                    App("installedGraphStep", N("nativeTable"), native))))));
        var preserve = All("q", bank, All("n", Nat, Arrow(EqF(Field(q, "role"), N("true")),
            EqF(Field(App("LiveProducer.CurrentBank.run", q, N("n")), "actual"), Field(q, "actual")))));
        var r = N("r"); var d = N("d");
        var writing = All("q", bank, All("d", N("Runtime"), Arrow(EqF(Field(q, "phase"), D(9)),
            Arrow(EqF(Field(q, "bankProbe"), D(0)),
            Arrow(EqF(Field(Field(q, "result"), "tape"), Word(App("optionalRuntimeCodec", Some(d)))),
                Ex("t", Nat, Ex("r", bank, Both(
                    EqF(App("LiveProducer.CurrentBank.run", q, t), r), EqF(Field(r, "phase"), D(1,1)),
                    EqF(App("LiveProducer.CurrentBank.bank", r), Word(App("runtimeCodec", d))),
                    EqF(Field(r, "operation"), Field(q, "operation")),
                    Arrow(EqF(Field(q, "role"), N("true")), EqF(Field(r, "actual"), Field(q, "actual")))))))))));
        var fields = All("q", bank, Arrow(EqF(Field(Field(q, "pre"), "tape"), Word(App("runtimeCodec", z))),
            EqF(App("LiveProducer.CurrentBank.fieldROM", q), Word(App("fieldsCodec", Field(z, "fields"))))));
        var charge = All("q", producer, LtF(Add(Add(Field(N("programImage"), "length"),
            Field(N("LiveProducer.Current.staticImage"), "length")), Field(App("LiveProducer.Current.code", q), "length")), N("LiveProducer.Current.bound")));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            EqF(App("LiveProducer.Current.step", App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y")),
                App("LiveProducer.Current.entry", saved, image, a, c, N("false"), App("operationCodec", App("Operation.read", N("x")))))));
        var ports = All("q", producer, All("alpha", N("Letter"), All("beta", N("Letter"), All("chi", N("Letter"), All("eta", N("Letter"),
            Arrow(EqF(App("LiveProducer.Current.actualRequest", q), N("false")),
                EqF(App("LiveProducer.Current.step", q, N("alpha"), N("beta")), App("LiveProducer.Current.step", q, N("chi"), N("eta")))))))));
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), All("a", bankType,
            All("c", bankType, All("role", N("Bool"), All("z", N("Runtime"), All("op", N("Operation"),
                Both(App("Function.Injective", N("LiveProducer.Current.code")), charge, preparation, scanner, preserve, writing, fields, acquisition, ports))))))));
    }

    private static Formula MotorRefinement()
    {
        var w = N("w"); var rom = N("rom"); var m = N("m"); var r = N("r");
        var entry = App("motorEntry", w);
        var checkpoint = App("motorCheckpoint", rom, m, N("hm"));
        var paused = All("m", Nat, All("hm", Le(m, w), All("r", Nat, And(
            EqF(App("motorRun", rom, entry, Add(App("motorTime", m), r)),
                App("motorRun", rom, checkpoint, r)),
            EqF(App("motorTrace", rom, entry, Add(App("motorTime", m), r)),
                Seq(Trace(rom, App("copyEntry", w), Mul(D(4), m)), Sp, Plus, Plus, Sp,
                    App("motorTrace", rom, checkpoint, r)))))));
        var tape = EqF(Field(App("motorRun", rom, entry, App("motorTime", w)), "tape"), rom);
        var trace = EqF(App("motorTrace", rom, entry, App("motorTime", w)),
            App("List.ofFn", Fn("i", FinOf(w), App("rom", N("i")))));
        var terminal = With(With(App("motorCheckpoint", rom, w, Seq(N("le"), Underscore, Grp(N("rfl")))),
            "probe", App("Fin.last", w)), "pc", N("MotorPC.halt"));
        var halted = All("n", Nat, EqF(App("motorRun", rom, entry,
            Add(Add(Add(App("motorTime", w), Mul(D(2), w)), D(2)), N("n"))), terminal));
        return All("w", Nat, All("rom", Arrow(FinOf(w), N("Bool")),
            And(paused, And(tape, And(trace, halted)))));
    }

    private static Formula LiteralTransfers()
    {
        var s = N("s"); var q = N("q"); var m = N("m"); var r = N("r"); var slot = N("slot");
        var start = App("literalInstallStart", s);
        Formula RunAt(Formula t) => Iter(N("literalInstallStep"), t, start);
        var state = RunAt(N("ticks")); var motor = Field(state, "installation");
        var invariant = Seq(Exists, Sp, Open, N("m"), Sp, Colon, Sp, Nat, Close, Comma, Sp,
            App("HeadControl", motor, N("m")));
        var noFault = Seq(Field(motor, "pc"), Sp, Neq, Sp, N("MotorPC.fault"));
        var progress = Arrow(Seq(Field(motor, "pc"), Sp, Neq, Sp, N("MotorPC.halt")),
            LtF(App("motorRank", Field(App("literalInstallStep", state), "installation")),
                App("motorRank", motor)));
        var cuts = All("ticks", Nat, And(EqF(Field(state, "base"), Field(s, "base")),
            And(EqF(Field(state, "header"), Field(s, "header")),
            And(EqF(Field(state, "frame"), Field(s, "frame")),
            And(invariant, And(noFault, progress))))));
        var paused = All("m", Nat, All("hm", Le(m, N("programWidth")), All("r", Nat,
            EqF(Field(RunAt(Add(App("motorTime", m), r)), "installation"),
                App("motorRun", N("programTape"),
                    App("motorCheckpoint", N("programTape"), m, N("hm")), r)))));
        var endpoint = RunAt(App("motorTime", N("programWidth")));
        var installed = EqF(Field(Field(endpoint, "installation"), "tape"), N("programTape"));
        var pre = Field(Field(Field(Field(s, "base"), "retained"), "pre"), "fields");
        var op = Field(Field(Field(s, "base"), "retained"), "operation");
        var frames = All("slot", FinOf(D(6)), EqF(
            App("motorTrace", App("literalInstalledFrameROM", endpoint, slot),
                App("motorEntry", N("frameWidth")), App("motorTime", N("frameWidth"))),
            App("bitCode", App("frameCodec", Frame(pre, op, slot)))));
        var block = EqF(App("literalStreamedBlock", pre, op), App("eventBlock", pre, op));
        var charge = All("q", N("TransferSnapshot"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("motorStaticImage"), "length")),
                Field(App("transferCode", q), "length")), N("literalTransferBound")));
        return All("s", N("TransferSnapshot"),
            And(App("Function.Injective", N("transferCode")),
                And(charge, And(cuts, And(paused, And(installed, And(frames, block)))))));
    }

    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula TaggedSourceCommit()
    {
        var s = N("s"); var op = N("op"); var slot = N("slot"); var i = N("i");
        var z = Field(Field(Field(s, "base"), "retained"), "actual");
        var stateType = N("LiveProducer.State");
        var prepared = App("LiveProducer.prepared", s, op, slot, i);
        Formula RunAt(Formula t) => App("LiveProducer.run", prepared, D(0), D(0), t);
        var q = N("q");
        var charge = All("q", stateType, LtF(Add(Add(Field(N("programImage"), "length"),
            Field(N("LiveProducer.staticImage"), "length")), Field(App("LiveProducer.code", q), "length")), N("LiveProducer.bound")));
        Formula ports = Arrow(EqF(App("LiveProducer.actualRequest", q), N("false")),
            Arrow(EqF(App("LiveProducer.freshRequest", q), N("false")),
                EqF(App("LiveProducer.step", q, N("a"), N("b")),
                    App("LiveProducer.step", q, N("c"), N("d")))));
        ports = All("d", N("Letter"), ports);
        ports = All("c", N("Letter"), ports);
        ports = All("b", N("Letter"), ports);
        ports = All("a", N("Letter"), ports);
        ports = All("q", stateType, ports);
        Formula Saved(Formula x) => Field(Field(Field(x, "addressed"), "outer"), "base");
        var cuts = All("q", stateType, All("a", N("Letter"), All("b", N("Letter"), All("t", Nat,
            EqF(Field(Saved(App("LiveProducer.run", q, N("a"), N("b"), N("t"))), "retained"),
                Field(Saved(q), "retained"))))));
        var returned = EqF(Field(q, "stage"), N("LiveProducer.Stage.returned"));
        var output = Some("u", Nat, And(Le(N("u"), N("t")), EqF(App("LiveProducer.emitted", RunAt(N("u"))),
            App("some", Seq(App("frameTape", App("eventROM", Field(z, "fields"), op, slot)), Sp, i)))));
        var endpoint = Some("t", Nat, Some("q", stateType, And(EqF(RunAt(N("t")), q),
            And(returned, And(EqF(App("LiveProducer.returnedRuntime", q), App("some", N("d"))),
            And(EqF(App("LiveProducer.returnedOperation", q), App("some", op)), output))))));
        var atN = RunAt(N("n"));
        var rankCuts = All("n", Nat, And(Seq(Field(atN, "stage"), Sp, Neq, Sp, N("LiveProducer.Stage.fault")),
            Arrow(Seq(Field(atN, "stage"), Sp, Neq, Sp, N("LiveProducer.Stage.returned")),
                LtF(App("LiveProducer.rank", App("LiveProducer.step", atN, D(0), D(0))), App("LiveProducer.rank", atN)))));
        var native = All("d", N("Runtime"), Arrow(EqF(App("runtimeStep", z, op), App("some", N("d"))), And(endpoint, rankCuts)));
        var acquired = App("LiveProducer.step", App("LiveProducer.sourceEntry", s, slot, i), N("x"), D(0));
        var sourceReturn = And(returned, And(
            EqF(App("LiveProducer.returnedRuntime", q), App("some", N("d"))),
            EqF(App("LiveProducer.returnedOperation", q), App("some", App("Operation.read", N("x"))))));
        var sourceEndpoint = Some("t", Nat, Some("q", stateType, And(
            EqF(App("LiveProducer.run", acquired, D(0), D(0), N("t")), q), sourceReturn)));
        var source = All("x", N("Letter"), All("d", N("Runtime"), Arrow(
            EqF(App("runtimeStep", z, App("Operation.read", N("x"))), App("some", N("d"))), sourceEndpoint)));
        Formula result = And(native, source);
        result = And(cuts, result);
        result = And(ports, result);
        result = And(charge, result);
        result = And(App("Function.Injective", N("LiveProducer.code")), result);
        result = All("i", FinOf(N("frameWidth")), result);
        result = All("slot", FinOf(D(6)), result);
        result = All("op", N("Operation"), result);
        return All("s", N("TransferSnapshot"), result);
    }

    private static Formula LiteralAddress()
    {
        var s = N("s"); var q = N("q"); var a = N("a"); var i = N("i");
        var entry = App("addressEntry", s, a, i);
        var index = App("addressIndex", a, i);
        Formula RunAt(Formula start, Formula ticks) => App("addressRun", start, ticks);
        var state = RunAt(entry, N("n"));
        var preserved = And(EqF(Field(state, "outer"), s),
            And(EqF(Field(state, "key"), Field(entry, "key")),
            And(EqF(Field(state, "offset"), Field(entry, "offset")), And(
                Seq(Field(Field(state, "control"), "pc"), Sp, Neq, Sp, N("AddressPC.fault")),
                Arrow(Seq(Field(Field(state, "control"), "pc"), Sp, Neq, Sp, N("AddressPC.returned")),
                    LtF(App("addressRank", App("addressStep", state)), App("addressRank", state)))))));
        var cuts = All("a", FinOf(N("frameKeyWidth")), All("i", FinOf(N("frameWidth")),
            All("n", Nat, preserved)));
        var returned = EqF(Field(Field(q, "control"), "pc"), N("AddressPC.returned"));
        var endpoint = Some("ticks", Nat, Some("q", N("AddressState"),
            And(EqF(RunAt(entry, N("ticks")), q), And(returned,
            And(EqF(Field(q, "outer"), s), And(
                EqF(Field(Field(Field(q, "head"), "probe"), "val"), Field(index, "val")),
                And(EqF(Field(Field(q, "control"), "latch"),
                    Seq(Field(Field(s, "installation"), "tape"), Sp, index)),
                    Le(N("ticks"), N("addressTimeBound")))))))));
        var execution = All("a", FinOf(N("frameKeyWidth")), All("i", FinOf(N("frameWidth")), endpoint));
        var installed = Iter(N("literalInstallStep"), App("motorTime", N("programWidth")),
            App("literalInstallStart", s));
        var raw = App("addressEntry", installed, App("frameKey", s, N("slot")), i);
        var pre = Field(Field(Field(Field(s, "base"), "retained"), "pre"), "fields");
        var op = Field(Field(Field(s, "base"), "retained"), "operation");
        var frames = All("slot", FinOf(D(6)), All("i", FinOf(N("frameWidth")),
            Some("ticks", Nat, Some("q", N("AddressState"), And(
                EqF(RunAt(raw, N("ticks")), q), And(returned,
                    EqF(Field(Field(q, "control"), "latch"),
                        Seq(App("frameTape", Frame(pre, op, N("slot"))), Sp, i))))))));
        var charge = All("q", N("AddressState"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("addressStaticImage"), "length")),
                Field(App("addressCode", q), "length")), N("literalAddressBound")));
        return All("s", N("TransferSnapshot"), And(App("Function.Injective", N("addressCode")),
            And(charge, And(cuts, And(execution, frames)))));
    }

    private static Formula SixSlots()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var bound = Le(Field(App("eventBlock", f, op), "length"), D(6));
                var indices = All("i", Nat, All("b", N("Letter"), Seq(
                    App("OriginalEvent.completed", N("i"), N("b")), Sp, InMacro, Sp,
                    App("eventBlock", f, op), Sp, Implies, Sp, LtF(N("i"), D(4)))));
                var blocks = App("List.map", N("original"), App("List.filterMap", N("id"),
                    App("List.ofFn", App("eventROM", f, op))));
                return All("f", N("FiniteFields"), All("op", N("Operation"),
                    And(bound, And(indices, EqF(blocks, App("eventBlock", f, op))))));
    }

    private static Formula StreamedEvents()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var one = All("slot", FinOf(D(6)), And(
                    EqF(Trace(Rom(f, op, slot), N("renderFrame"), Mul(D(4), N("frameWidth"))),
                        App("bitCode", App("frameCodec", Frame(f, op, slot)))),
                    EqF(Field(App("frameRun", f, op, slot, Mul(D(4), N("frameWidth"))), "tape"), Rom(f, op, slot))));
                return All("f", N("FiniteFields"), All("op", N("Operation"),
                    And(one, EqF(Decoded(f, op), App("eventBlock", f, op)))));
    }

    private static Formula ChargedFrames()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(App("installed", s), "frame", N("renderFrame"));

                var charge = All("q", N("RenderSnapshot"), LtF(Add(Field(N("programImage"), "length"),
                    Field(App("snapshot", N("q")), "length")), N("rendererBound")));
                var endpoint = EqF(App("installed", s), Iter(N("installStep"), Mul(D(4), N("programWidth")),
                    With(s, "installation", App("copyEntry", N("programWidth")))));
                var installed = EqF(Field(Field(Iter(N("installStep"), Mul(D(4), N("programWidth")),
                    With(s, "installation", App("copyEntry", N("programWidth")))), "installation"), "tape"), N("programTape"));
                var cp = Cp(Rom(pre, operation, slot), N("m"), N("hm"));
                var equality = EqF(Field(Iter(App("frameStep", slot), Add(Mul(D(4), N("m")), N("r")), entry), "frame"),
                    Run(Rom(pre, operation, slot), cp, N("r")));
                var paused = All("slot", FinOf(D(6)), All("m", Nat,
                    All("hm", Le(N("m"), N("frameWidth")), All("r", Nat, equality))));
                return All("s", N("RenderSnapshot"), And(App("Function.Injective", N("snapshot")),
                    And(charge, And(endpoint, And(installed, And(paused, EqF(InstalledDecoded(s), App("eventBlock", pre, operation))))))));
    }

    private static Formula StreamedHistory()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var initial = Field(Field(N("c"), "source"), "finiteFields");
                var final = Field(Field(N("d"), "source"), "finiteFields");
                var blocks = App("streamedBlocks", initial, N("ops"));
                var result = And(EqF(App("fullTranscript", N("c"), N("omega"), N("n")),
                    App("some", Pair(N("ops"), final, blocks))),
                    EqF(App("List.foldl", N("replayBlock"), initial, blocks), final));
                var body = Seq(EqF(App("nativeDrive", N("c"), N("omega"), N("n")),
                    App("some", Pair(N("ops"), N("d"), N("k")))), Sp, Implies, Sp, result);
                body = All("ops", ListOf(N("Operation")), body);
                body = All("k", Nat, body); body = All("n", Nat, body);
                body = All("omega", N("Stream"), body);
                body = All("d", N("AcquiredNativeState"), body);
                return All("c", N("AcquiredNativeState"), body);
    }
}
