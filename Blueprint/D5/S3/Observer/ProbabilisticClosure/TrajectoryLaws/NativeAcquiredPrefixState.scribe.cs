using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeAcquiredPrefixStateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.";

    public DocumentDefinition Create()
    {
        Formula t = F.Id("t"), r = F.Id("r"), s = F.Id("s"), c = F.Id("c");
        Formula j = F.Id("j"), ops = F.Id("ops"), rho = F.Id("rho"), bs = F.Id("bs");
        Formula op = F.Id("op"), nat = F.Id("Nat"), registers = F.Id("Registers");
        Formula word = Call("List", F.Id("Operation"));
        Formula markers = Call("List", F.Id("Letter"));
        Formula counts = Call("Counts", Seq(Call("alpha", c), Plus, j),
            Seq(Call("beta", c), Plus, j));
        Formula loops = All("t", nat, Imp(Seq(t, Le, D(3)), All("r", registers,
            All("s", nat, All("c", F.Id("Counts"), All("j", nat, All("ops", word,
                Equal(Call("execute", Call("atPhase", t, r, s, c, F.Id("p")),
                        Call("append", Call("reads", Call("loopWord", j)), ops)),
                    Call("execute", Call("atPhase", t, r, Seq(s, Plus, j), counts, F.Id("p")), ops)))))))));
        Formula projection = All("c", F.Id("AcquiredNativeState"), All("op", F.Id("Operation"),
            Equal(Call("map", F.Id("pi"), Call("nativeStep", c, op)),
                Call("finiteStep", Call("pi", c), op))));
        Formula recovery = All("rho", F.Id("Letter"), All("bs", markers,
            Imp(Seq(Call("length", bs), Le, D(4)),
                Equal(Call("recoverMarkers", Call("markerCut", rho, bs)), Call("take", D(3), bs)))));
        Formula written = All("rho", F.Id("Letter"), All("bs", markers,
            Imp(Seq(Call("length", bs), Le, D(4)),
                Call("WrittenFields", rho, bs, Call("markerRegisters", rho, bs)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Literal acquired seed and payload state with all live numeric banks.",
            H("Native state and the original writers"), Blocks(
                Paragraph(Text("The fixed source has one acquired seed bit and four payload markers. Letters 0 and 1 mean alpha and beta. NativeControl is seed with an optional first letter, early with completed count t in Fin 3 and active phase, or fourth with the original active, pending and delivered controls. Its completedCount is respectively 0, t, 3 or 4. No clock or marker archive is a runtime field.")),
                Paragraph(Text("FiniteFields contains control and Registers. The latter retains an optional acquired seed, weight in Fin 5, optional syndrome in Fin 2, the actual ordered records QOne and QTwo, first-marker Z and optional ThirdSnapshot. The snapshot has fixed ell=2 and completed count 3, retaining its seed, weight and syndrome. The seed and syndrome are unset initially; all records are empty, weight and Z are zero. NativeSourceState also retains S=payloadReturns in Nat. AcquiredNativeState adds live alpha and beta counts initialized at zero. The full state has no finite-state assertion and installs no selected count bank.")),
                Paragraph(Text("Read has only the actual Letter as input. In seed control, equal pairs reject and return to seed-ready; unequal alpha-beta and beta-alpha pairs acquire seed 0 and 1. Acceptance initializes weight zero and syndrome 1+rho. Every Read increments exactly its acquired-letter count. In payload p, alpha completes marker 0 and beta suspends; in payload beta, alpha completes a return and beta completes marker 1. Every return increments S, including in segment four. Stop increments no count and preserves S; only the pending matching color is permitted, and delivered admits no operation.")),
                Paragraph(Text("Marker transactions route with old t and weight w. The first and second zero events are a and c; the first and second one events are b and d. At completions with old t<3, including the third completion, each is appended to scopes {a,c,d} and {b,c}. An unmatched third occurrence holds the records. Only the first marker writes Z. Weight adds the marker and syndrome adds its coefficient in (1,rho,1,rho), including rho=0. The third marker writes these fields before retaining the new bare snapshot; thereafter QOne, QTwo, Z and snapshot hold while live weight, syndrome, S and counts continue.")),
                Node("execute-payload-loops", "execute_payload_loops", "Unbounded native return execution", loops,
                    "Here atPhase(t,r,s,c,p) assembles the indicated original control, registers and banks; Counts(a,b) is the pair of numeric banks. For every t at most 3, every register and bank value, every natural j and every suffix ops, executing j beta-alpha returns preserves registers and phase, adds j to S and each count, then executes the same suffix from that actual successor. Induction over j follows two paid native Reads per return."),
                Node("finite-projection-commutes", "finite_projection_commutes", "Operations commute with finite projection", projection,
                    "The projection pi(c)=c.source.finiteFields erases S and counts. Map denotes Option.map. Both legal successors and failures agree with the independently defined finiteStep, so the projection preserves permissions. This is a projection of the full source, rather than reconstruction of its numeric banks."),
                Node("marker-fields-recover", "marker_fields_recover", "Written records recover the selected marker prefix", recovery,
                    "For bs of length at most four, markerCut(rho,bs) pairs markerRegisters(rho,bs) with payloadControl(length(bs),p) when length(bs)<4, and with pending(getLastD(bs,0)) otherwise. recoverMarkers reads completedCount and Registers only. It returns bs.take(3): at length zero the empty word, at length one Z, at length two Z and weight, and at three or four the eight distinct QOne,QTwo,Z addresses. Both seeds and every triple are included."),
                Node("marker-fields-exact", "marker_fields_exact", "Exact bare fields and third latch", written,
                    "WrittenFields states that seed is some rho, live weight is the integer sum of bs, syndrome is some (1+rho plus the indexed coefficient sum), and Z is headD(bs,0). QOne and QTwo equal their writers on bs.take(3). Snapshot is none before three completions and otherwise the post-third seed, weight and syndrome. The modulo-five constructor is exact because at most four bits have been written. These finite formulas include fourth-marker holding."),
                Paragraph(Text("PrefixForm is separate proof data: an ordered list of rejected-pair kinds followed by seed-ready, one first seed letter, or an acquired seed with PayloadForm. PayloadForm uses independent concatenations of loopWord and pWord, optional pending beta, exactly four completion slots, matching pending Stop and delivered. render concatenates these words. reconstruct calculates banks and marker writes from this data without executing Read. No form or rejected-pair list occurs in native state.")))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(x), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Open, premise, Close, Rightarrow, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
