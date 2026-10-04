using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class EndpointCellsDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retained initial targets, actual endpoint cells, and deterministic complete-block controllers.",
        H("EndpointCells"),
        Blocks(
            Paragraph(Text(
                "CandidateState(k,X) is a nonempty set of pairs consisting of an "
                    + "initial source in an arbitrary type X and a current optional "
                    + "LiveRecord. AllowedBlock fixes either the full or the internally "
                    + "legal block alphabet; an old tail is not an alphabet restriction. "
                    + "replyFiber retains the initial coordinate and updates only the "
                    + "current coordinate, filtering by the single actual endpoint "
                    + "reading. acquisitionSystem uses the native finite-horizon "
                    + "ControlSystem and has only nonempty reply fibers as successors. "
                    + "targetGoal means pairwise constancy of the original target f on "
                    + "the retained initial coordinates, independently of current values. "
                    + "These definitions do not assume the first-zero criterion.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-acquisition-merge-obstruction"),
                DeclarationHandle.Create(Owner + "acquisition_merge_obstruction"),
                H("Merged current records require equal initial labels"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("X"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("Y"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))),
                    Comma, Sp, F.Id("f"), Colon, Sp, Seq(F.Id("X"), Sp, To, Sp, F.Id("Y")), Comma, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("cell"), Colon, Sp, Call("CandidateState", F.Id("k"), F.Id("X")), Comma,
                    Sp, Seq(Open, Seq(Seq(Open, Call("BoundedReachStrategy", Call("acquisitionSystem", F.Id("k"), F.Id("m"), F.Id("ell"),
                    F.Id("X")), Call("targetGoal", F.Id("f")), F.Id("n"), F.Id("cell")), Close), Sp, Implies, Sp, Seq(Open, Seq(Forall,
                    Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp, F.Id("z"), Colon, Sp, F.Id("X"), Comma, Sp, F.Id("q"), Colon,
                    Sp, Call("Option", Call("LiveRecord", F.Id("k"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(Call("pair",
                    F.Id("x"), F.Id("q")), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close), Sp, Land, Sp, Seq(Open, Seq(Call("pair",
                    F.Id("z"), F.Id("q")), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close)), Close), Sp, Implies, Sp, Seq(Open,
                    Seq(Call("f", F.Id("x")), Sp, Eq, Sp, Call("f", F.Id("z"))), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k and m, either alphabet choice, arbitrary "
                        + "types X and Y, target f from X to Y, natural budget n and "
                        + "nonempty candidate cell, assume a native BoundedReachStrategy "
                        + "for acquisitionSystem(k,m,alphabet,X) and targetGoal(f). "
                        + "For every initial x and z and every common current record q, "
                        + "membership of both (x,q) and (z,q) in that cell implies "
                        + "f(x)=f(z). The proof follows the actually attained nonempty "
                        + "reply fiber of a common successor. It covers q=none and "
                        + "does not identify a newly rejected live source's label with "
                        + "the label of an initially rejected source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-all-one-archive-exact"),
                DeclarationHandle.Create(Owner + "all_one_archive_exact"),
                H("Successful all-one endpoint archives are exact"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("t"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("v"), Colon,
                    Sp, Call("ZMod", D(2)), Comma, Sp, F.Id("phi"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma,
                    Sp, F.Id("s"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("b"), Colon, Sp, Seq(Seq(Mathbb, Grp(F.Id("N"))),
                    Sp, To, Sp, Call("ZMod", D(2))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq, Sp, F.Id("k")),
                    Close), Sp, Land, Sp, Seq(Open, Seq(D(1), Sp, Leq, Sp, F.Id("m")), Close), Sp, Land, Sp, Seq(Open, Seq(F.Id("s"),
                    Sp, Lt, Sp, F.Id("k")), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Call("OnesArchive",
                    F.Id("k"), F.Id("m"), F.Id("t"), F.Id("v"), F.Id("phi"), F.Id("s"), F.Id("b")), Close), Sp, Iff, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(Seq(F.Id("s"), Plus, Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m"))), Sp, Lt, Sp, F.Id("k")), Close),
                    Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("i"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open,
                    Seq(Seq(Open, Seq(F.Id("i"), Sp, Lt, Sp, F.Id("t")), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("allOneIncrement",
                    F.Id("k"), F.Id("m"), F.Id("i"), F.Id("phi")), Sp, Eq, Sp, Call("b", F.Id("i"))), Close)), Close)), Close)),
                    Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Seq(Open, Call("OnesArchive", F.Id("k"), F.Id("m"), F.Id("t"),
                    F.Id("v"), F.Id("phi"), F.Id("s"), F.Id("b")), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("allOneOrbit",
                    F.Id("k"), F.Id("m"), F.Id("t"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))), Sp, Eq, Sp, Call("some",
                    Seq(F.Id("v"), Plus, Seq(Sum, Underscore, Grp(Seq(F.Id("i"), Sp, Lt, Sp, F.Id("t"))), Sp, Call("b", F.Id("i")))),
                    Seq(F.Id("phi"), Plus, Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m"))), Seq(F.Id("s"), Plus, Seq(F.Id("t"), Sp, Cdot,
                    Sp, F.Id("m"))))), Close)), Close), Sp, Land, Sp, Seq(Open, Seq(Call("allOneOrbit", F.Id("k"), F.Id("m"),
                    F.Id("t"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))), Sp, Eq, Sp, Call("if", Seq(Seq(F.Id("s"), Plus,
                    Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m"))), Sp, Lt, Sp, F.Id("k")), Call("some", Seq(F.Id("v"), Plus, Seq(Sum,
                    Underscore, Grp(Seq(F.Id("i"), Sp, Lt, Sp, F.Id("t"))), Sp, Call("allOneIncrement", F.Id("k"), F.Id("m"),
                    F.Id("i"), F.Id("phi")))), Seq(F.Id("phi"), Plus, Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m"))), Seq(F.Id("s"),
                    Plus, Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("m")))), Seq(Operatorname, Grp(F.Id("none"))))), Close)), Close)),
                    Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every k at least two, positive m, natural t, value v, "
                            + "ambient phase phi, initial tail s below k and arbitrary "
                            + "sequence b of ZMod 2 increments, OnesArchive says that "
                            + "every actual endpoint after r all-one blocks, for r "
                            + "from zero through t, equals v plus the sum of the first "
                            + "r values of b. This holds exactly when s+tm is below k "
                            + "and each allOneIncrement(k,m,i,phi) equals b(i) for i<t.")),
                    Paragraph(Text(
                        "The theorem also supplies the actual current record of a "
                            + "successful archive: its value is v plus the archived "
                            + "sum, its phase is phi+tm, and its current tail is s+tm. "
                            + "Without assuming success, the literal all-one orbit "
                            + "equals none when s+tm reaches k; otherwise its value "
                            + "is v plus the sum of the actual phase increments and "
                            + "its other coordinates are the same shifted phase and "
                            + "tail. The recorded endpoints all belong to the same "
                            + "executed orbit; block-internal bits are unread."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-first-zero-block-exact"),
                DeclarationHandle.Create(Owner + "first_zero_block_exact"),
                H("The first zero gives the exact rejection and merge"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("a"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("w"), Colon,
                    Sp, Seq(Call("Fin", F.Id("n")), Sp, To, Sp, Seq(Operatorname, Grp(F.Id("Bool")))), Comma, Sp, F.Id("rest"),
                    Colon, Sp, Call("List", Seq(Operatorname, Grp(F.Id("Bool")))), Comma, Sp, F.Id("v"), Colon, Sp, Call("ZMod",
                    D(2)), Comma, Sp, F.Id("phi"), Colon, Sp, Call("ZMod", Seq(F.Id("k"), Plus, D(1))), Comma, Sp, F.Id("s"),
                    Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Seq(Open, Seq(D(2), Sp, Leq,
                    Sp, F.Id("k")), Close), Sp, Land, Sp, Seq(Open, Seq(Call("ofFn", F.Id("w")), Sp, Eq, Sp, Call("append", Call("replicate",
                    F.Id("a"), Seq(Operatorname, Grp(F.Id("true")))), Call("cons", Seq(Operatorname, Grp(F.Id("false"))), F.Id("rest")))),
                    Close), Sp, Land, Sp, Seq(Open, Call("DBonacciAdmissible", F.Id("k"), F.Id("n"), F.Id("w")), Close), Sp, Land,
                    Sp, Seq(Open, Seq(F.Id("s"), Sp, Lt, Sp, F.Id("k")), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("runBits",
                    F.Id("k"), F.Id("w"), Call("some", F.Id("v"), F.Id("phi"), F.Id("s"))), Sp, Eq, Sp, Call("if", Seq(Seq(F.Id("s"),
                    Plus, F.Id("a")), Sp, Lt, Sp, F.Id("k")), Call("some", Seq(F.Id("v"), Plus, Call("wordIncrement", F.Id("k"),
                    F.Id("phi"), F.Id("w"))), Seq(F.Id("phi"), Plus, F.Id("n")), Call("tailAfter", D(0), F.Id("w"))), Seq(Operatorname,
                    Grp(F.Id("none"))))), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k at least two, natural n and a, word w on Fin n, "
                        + "Boolean list rest, value v, ambient phase phi and old "
                        + "tail s below k, assume w is DBonacciAdmissible and its "
                        + "chronological list is a true bits followed by false and "
                        + "rest. firstZeroResult is none if s+a reaches k. Otherwise "
                        + "it is exactly (v+wordIncrement(k,phi,w),phi+n,tailAfter(0,w)). "
                        + "Thus every surviving old tail at that fixed value and "
                        + "phase has the same actual endpoint record. The premise "
                        + "is local block legality; it does not exclude cross-boundary "
                        + "rejection or assume success of the acquisition target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-native-controller-exact"),
                DeclarationHandle.Create(Owner + "native_controller_exact"),
                H("Native strategies are actual bounded controllers"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("X"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("Y"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))),
                    Comma, Sp, F.Id("f"), Colon, Sp, Seq(F.Id("X"), Sp, To, Sp, F.Id("Y")), Comma, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("cell"), Colon, Sp, Call("CandidateState", F.Id("k"), F.Id("X")), Comma,
                    Sp, Seq(Open, Seq(Seq(Open, Seq(Exists, Sp, F.Id("tree"), Colon, Sp, Call("AcquisitionTree", F.Id("k"), F.Id("m"),
                    F.Id("ell"), F.Id("Y"), F.Id("n")), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Forall, Sp, F.Id("pair"), Colon,
                    Sp, Call("Pair", F.Id("X"), Call("Option", Call("LiveRecord", F.Id("k")))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(F.Id("pair"), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("result",
                    F.Id("tree"), Call("snd", F.Id("pair"))), Sp, Eq, Sp, Call("f", Call("fst", F.Id("pair")))), Close)), Close)),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord", F.Id("k"))),
                    Comma, Sp, Seq(Open, Seq(Call("length", Call("archive", F.Id("tree"), F.Id("q"))), Sp, Leq, Sp, F.Id("n")),
                    Close)), Close)), Close)), Close), Sp, Iff, Sp, Seq(Open, Call("BoundedReachStrategy", Call("acquisitionSystem",
                    F.Id("k"), F.Id("m"), F.Id("ell"), F.Id("X")), Call("targetGoal", F.Id("f")), F.Id("n"), F.Id("cell")), Close)),
                    Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k and m, either alphabet flag, arbitrary source "
                        + "type X and label type Y, target f:X->Y, horizon n and nonempty "
                        + "candidate cell, there is an AcquisitionTree of horizon n "
                        + "that returns f(initial) on every retained source/current pair "
                        + "and issues at most n blocks on every current record, if and "
                        + "only if the native acquisitionSystem has a BoundedReachStrategy "
                        + "to targetGoal(f) with that same horizon and cell. A step "
                        + "executes its allowed complete block, reads its actual endpoint "
                        + "and follows only that reply. Nonempty reply fibers preserve "
                        + "initial labels. Impossible replies use a label from the parent "
                        + "cell. No decidable equality, target observation, reset or "
                        + "counterfactual branch execution is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-archive-controller-synthesis"),
                DeclarationHandle.Create(Owner + "archive_controller_synthesis"),
                H("Actual fixed archives synthesize retained-label controllers"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb,
                    Grp(F.Id("N"))), Comma, Sp, F.Id("ell"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Bool"))), Comma, Sp, F.Id("X"),
                    Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))), Comma, Sp, F.Id("Y"), Colon, Sp, Seq(Operatorname, Grp(F.Id("Type"))),
                    Comma, Sp, F.Id("f"), Colon, Sp, Seq(F.Id("X"), Sp, To, Sp, F.Id("Y")), Comma, Sp, F.Id("actions"), Colon,
                    Sp, Call("List", Call("AllowedBlock", F.Id("k"), F.Id("m"), F.Id("ell"))), Comma, Sp, F.Id("cell"), Colon,
                    Sp, Call("CandidateState", F.Id("k"), F.Id("X")), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Forall, Sp, F.Id("first"),
                    Colon, Sp, Call("Pair", F.Id("X"), Call("Option", Call("LiveRecord", F.Id("k")))), Comma, Sp, F.Id("second"),
                    Colon, Sp, Call("Pair", F.Id("X"), Call("Option", Call("LiveRecord", F.Id("k")))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(Seq(Open, Seq(F.Id("first"), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close), Sp, Land, Sp, Seq(Open,
                    Seq(F.Id("second"), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close), Sp, Land, Sp, Seq(Open, Seq(Call("fixedBlockArchive",
                    F.Id("actions"), Call("snd", F.Id("first"))), Sp, Eq, Sp, Call("fixedBlockArchive", F.Id("actions"), Call("snd",
                    F.Id("second")))), Close)), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("f", Call("fst", F.Id("first"))),
                    Sp, Eq, Sp, Call("f", Call("fst", F.Id("second")))), Close)), Close)), Close), Sp, Implies, Sp, Seq(Open,
                    Seq(Exists, Sp, F.Id("tree"), Colon, Sp, Call("AcquisitionTree", F.Id("k"), F.Id("m"), F.Id("ell"), F.Id("Y"),
                    Call("length", F.Id("actions"))), Comma, Sp, Seq(Open, Seq(Seq(Open, Seq(Forall, Sp, F.Id("pair"), Colon,
                    Sp, Call("Pair", F.Id("X"), Call("Option", Call("LiveRecord", F.Id("k")))), Comma, Sp, Seq(Open, Seq(Seq(Open,
                    Seq(F.Id("pair"), Sp, InMacro, Sp, Call("val", F.Id("cell"))), Close), Sp, Implies, Sp, Seq(Open, Seq(Call("result",
                    F.Id("tree"), Call("snd", F.Id("pair"))), Sp, Eq, Sp, Call("f", Call("fst", F.Id("pair")))), Close)), Close)),
                    Close), Sp, Land, Sp, Seq(Open, Seq(Forall, Sp, F.Id("q"), Colon, Sp, Call("Option", Call("LiveRecord", F.Id("k"))),
                    Comma, Sp, Seq(Open, Seq(Call("length", Call("archive", F.Id("tree"), F.Id("q"))), Sp, Leq, Sp, Call("length",
                    F.Id("actions"))), Close)), Close)), Close)), Close)), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k and m, either alphabet, arbitrary source "
                        + "type X and label type Y, target f, finite list of allowed "
                        + "complete blocks and nonempty candidate cell, suppose "
                        + "equal fixedBlockArchive values imply equal INITIAL target "
                        + "labels for every pair of sources in that cell. There is "
                        + "a correct AcquisitionTree with horizon equal to the list "
                        + "length and at most that many issued blocks on every current "
                        + "record. fixedBlockArchive executes each actual block on "
                        + "the record produced by its predecessor and records only "
                        + "complete endpoint readings. The induction follows every "
                        + "attained nonempty reply fiber and constructs labels without "
                        + "decidable target equality. The archive-fiber hypothesis "
                        + "must still be established for the source's clearing and "
                        + "recursive acquisition construction."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
