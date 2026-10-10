using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TraceKeyedArtifactCacheSoundnessDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Governance/TraceKeyedArtifactCacheSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A trace-keyed artifact cache filled only by from-scratch builds yields from-scratch "
            + "artifacts and restores every unaffected module.",
        H("Trace-Keyed Artifact Cache Soundness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cached-build-eq-build"),
                DeclarationHandle.Create(Module + "cachedBuild_eq_build"),
                H("Reader builds equal from-scratch builds"),
                StatementSource.FromAuthor(SoundnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A snapshot assigns every module a source and the finite set of modules "
                            + "whose artifacts its build reads; a natural-number rank decreases "
                            + "along these dependencies. build compiles a module's source against "
                            + "the set of its dependencies' artifacts. traceKey hashes the source "
                            + "together with the set of digests of those artifacts.")),
                    Paragraph(Text(
                        "A cache state maps keys to optional artifacts. store(W, m) writes the "
                            + "from-scratch artifact of m in W under its key, clean empties the "
                            + "cache, and run applies a list of operations to the empty cache. "
                            + "cachedBuild computes the key of a module from its own dependency "
                            + "artifacts, returns the stored artifact on a hit and compiles on a "
                            + "miss. The state consulted for each module is arbitrary, so stores "
                            + "and cleans may interleave with the reader in any order.")),
                    Paragraph(Text(
                        "NoCollision asks only that equal keys realized by the writers and the "
                            + "reader come from equal sources and equal sets of dependency "
                            + "artifacts; an injective pairing satisfies it. Every state reached "
                            + "by writer stores and cleans holds only from-scratch artifacts under "
                            + "their own keys. Strong induction on rank makes the reader's "
                            + "dependency artifacts equal to the from-scratch ones, so the key it "
                            + "computes is traceKey. A hit was stored by some writer under the same "
                            + "key, NoCollision equates the two build inputs, and compile returns "
                            + "the same artifact; a miss compiles the same input directly.")),
                    Paragraph(Text(
                        "The conclusion does not require the reader to be distinct from the "
                            + "writers: any snapshot whose stores are honest from-scratch builds "
                            + "may write without affecting soundness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cached-build-restores-unaffected"),
                DeclarationHandle.Create(Module + "cachedBuild_restores_unaffected"),
                H("Unaffected modules are restored"),
                StatementSource.FromAuthor(RestoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Unaffected(S, T, n) holds when n has the same source and the same "
                            + "dependency set in S and T and every dependency is unaffected. By "
                            + "induction along this predicate the from-scratch artifacts of n in "
                            + "S and T coincide.")),
                    Paragraph(Text(
                        "By the previous theorem the reader's dependency artifacts are the "
                            + "from-scratch artifacts of T, which coincide with those of S on the "
                            + "dependencies of an unaffected module. The key the reader computes "
                            + "for n is therefore the key of n in S, and an entry under that key "
                            + "makes the reader restore n instead of compiling it.")),
                    Paragraph(Text(
                        "Consequently a module the reader compiles is affected, meaning a "
                            + "source or dependency change occurs in its dependency closure, or "
                            + "the consulted cache state lacks the key of that module in S."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Instance(Formula type) =>
        Seq(OpenBracket, Call("DecidableEq", type), CloseBracket);

    private static Formula Binders()
    {
        Formula node = F.Id("Node");
        Formula source = F.Id("Src");
        Formula artifact = F.Id("Art");
        Formula digestType = F.Id("Dig");
        Formula key = F.Id("Key");
        Formula snapshot = Call("Snapshot", node, source);
        return Seq(
            Forall, Sp, node, Comma, Sp, source, Comma, Sp, artifact, Comma, Sp,
            digestType, Comma, Sp, key, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Instance(artifact), Comma, Sp, Instance(digestType), Comma, Sp, Instance(key),
            Comma, RowBreak, Grp(),
            F.Id("compile"), Colon, Sp,
            Arrow(source, Arrow(Call("Finset", artifact), artifact)), Comma, Sp,
            F.Id("hash"), Colon, Sp,
            Arrow(source, Arrow(Call("Finset", digestType), key)), Comma, Sp,
            F.Id("digest"), Colon, Sp, Arrow(artifact, digestType), Comma, RowBreak, Grp(),
            F.Id("writers"), Colon, Sp, Call("Set", snapshot), Comma, Sp,
            F.Id("T"), Colon, Sp, snapshot, Comma, Sp,
            F.Id("schedule"), Colon, Sp, Arrow(node, Call("List", Call("Op", node, source))),
            Comma, RowBreak, Grp());
    }

    private static Formula Hypotheses()
    {
        Formula n = F.Id("n");
        Formula w = F.Id("W");
        Formula m = F.Id("m");
        return Seq(
            Call("NoCollision", F.Id("compile"), F.Id("hash"), F.Id("digest"),
                Call("insert", F.Id("T"), F.Id("writers"))), Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, n, Comma, Sp, w, Comma, Sp, m, Comma, Sp,
            Call("store", w, m), Sp, InMacro, Sp, Call("schedule", n), Sp, Rightarrow, Sp,
            w, Sp, InMacro, Sp, F.Id("writers"), Close, Sp, Rightarrow, RowBreak, Grp());
    }

    private static Formula Look()
    {
        Formula n = F.Id("n");
        return Seq(
            LambdaLower, Sp, n, Sp, Mapsto, Sp,
            Call("run", F.Id("compile"), F.Id("hash"), F.Id("digest"), Call("schedule", n)));
    }

    private static Formula SoundnessFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Binders(),
            Hypotheses(),
            Forall, Sp, n, Colon, Sp, F.Id("Node"), Comma, Sp,
            Call("cachedBuild", F.Id("compile"), F.Id("hash"), F.Id("digest"), Look(),
                F.Id("T"), n), Sp, Eq, Sp,
            Call("build", F.Id("compile"), F.Id("T"), n), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula RestoreFormula()
    {
        Formula n = F.Id("n");
        Formula a = F.Id("a");
        Formula s = F.Id("S");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Binders(),
            Hypotheses(),
            Forall, Sp, s, Colon, Sp, Call("Snapshot", F.Id("Node"), F.Id("Src")), Comma, Sp,
            n, Colon, Sp, F.Id("Node"), Comma, Sp,
            Call("Unaffected", s, F.Id("T"), n), Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Sp, a, Comma, Sp,
            Call("run", F.Id("compile"), F.Id("hash"), F.Id("digest"), Call("schedule", n)),
            Open, Call("traceKey", F.Id("compile"), F.Id("hash"), F.Id("digest"), s, n), Close,
            Sp, Eq, Sp, Call("some", a), Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("Restores", F.Id("compile"), F.Id("hash"), F.Id("digest"), Look(),
                F.Id("T"), n), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
