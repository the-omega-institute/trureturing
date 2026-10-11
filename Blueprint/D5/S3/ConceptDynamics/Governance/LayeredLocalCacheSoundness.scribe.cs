using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class LayeredLocalCacheSoundnessDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Governance/LayeredLocalCacheSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A persistent module-indexed cache above a trace-keyed shared cache preserves "
            + "from-scratch artifacts under arbitrary reachable session histories. Its "
            + "dependency plan has exact locality and compile work, and a noncompiling "
            + "probe detects precisely the absence of compilation.",
        H("Persistent Layered Cache Soundness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("layered-cache-contract"),
                DeclarationHandle.Create(Module + "layered_cache_contract"),
                H("Reachable layers, exact work, and readiness"),
                StatementSource.FromAuthor(ContractFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The model M contains a build system and a family of snapshots. "
                            + "Each snapshot has a source and finite dependency set at each "
                            + "module, with a natural rank decreasing along dependencies. "
                            + "Compilation is a total deterministic function of the source "
                            + "and dependency artifacts. Equal trace keys among the model's "
                            + "snapshots imply equal sources and dependency artifact sets. "
                            + "A local layer L stores at most one key and artifact pair per "
                            + "module. The executor and probe receive already materialized "
                            + "shared states. The state consulted at n is the result of its "
                            + "schedule of honest writer stores and whole-cache cleans.")),
                    Paragraph(Text(
                        "For a finite root set R, demand Q is the least set containing R "
                            + "and closed under dependencies. The finite support of a root is "
                            + "the root together with the union of its dependencies' supports. "
                            + "Rank recursion makes this finite. The union of these supports "
                            + "over R is exactly Q. Repeatedly selecting a module of least rank "
                            + "among the remaining modules constructs a plan p that lists exactly Q, "
                            + "without duplicates, and places each dependency before its user. "
                            + "At each node the executor reads the already processed dependency "
                            + "artifacts, computes the current key, checks its local record, "
                            + "and on a local miss consults the shared state. Only a double "
                            + "miss invokes compilation. Every result is stored at that node. "
                            + "The event records the node, computed key, lookup outcomes, "
                            + "compilation flag, and local read set consisting of the node "
                            + "and its dependencies.")),
                    Paragraph(Text(
                        "Reachable layers start empty and are closed under changing the "
                            + "current snapshot, executing a valid plan, deleting any entry, "
                            + "clearing the layer, and copying another reachable layer. Every "
                            + "entry in such a layer has honest snapshot provenance. Induction "
                            + "over a plan first identifies its dependency artifacts with "
                            + "from-scratch artifacts. The computed key is then the current "
                            + "trace key. A local hit is correct by provenance and the collision "
                            + "condition; a shared hit is correct by shared-cache soundness; "
                            + "a miss compiles exactly the from-scratch input. This preserves "
                            + "provenance and correctness of the processed prefix. Thus every "
                            + "requested root has its from-scratch artifact at termination, "
                            + "and the resulting layer is reachable for further sessions.")),
                    Paragraph(Text(
                        "The sequence of visited nodes equals p.nodes. The union of all "
                            + "local read sets is exactly Q, and every local record outside Q "
                            + "is unchanged. Since a node occurs only once, its own local "
                            + "record at lookup is its initial record. A module compiles "
                            + "exactly when it lies in Q and its current trace key misses "
                            + "both that initial record and the shared state consulted there. "
                            + "The shared schedules may differ by module; no single shared "
                            + "cache snapshot is required.")),
                    Paragraph(Text(
                        "Fix the snapshot, shared lookup schedules, and plan p. For any "
                            + "two local layers that agree at every node of Q, execution "
                            + "produces identical ordered event lists and identical final "
                            + "records on Q. Outside Q, each final layer retains its own "
                            + "initial records. The two initial layers need not be reachable "
                            + "or have honest provenance. Dependency closure makes the "
                            + "input artifact sets equal at each step; the current keys, "
                            + "local hits, shared lookups, compilation choices, and stored "
                            + "artifacts then agree. Updating the same node with the same "
                            + "record preserves agreement on Q, so induction gives the "
                            + "whole execution result. This semantic independence from "
                            + "outside records does not require the final layers to agree "
                            + "outside Q and does not depend on the event read-set annotation.")),
                    Paragraph(Text(
                        "The probe follows the same dependency plan and performs the same "
                            + "key computation, lookups, and restoration writes, but stops "
                            + "at the first double miss. It never invokes the compiler. "
                            + "Induction on the plan couples each successful probe step with "
                            + "the corresponding execution step. The probe returns a restored "
                            + "layer exactly when every execution event has a false compilation "
                            + "flag. If it reports a module n, then n belongs to Q and its "
                            + "current key misses both layers. This comparison fixes the "
                            + "initial local layer and the shared lookup schedules in both runs.")),
                    Paragraph(Text(
                        "Artifact correctness is conditional on the stated collision law "
                            + "and honest store semantics. A local record represents a "
                            + "complete artifact; arbitrary corruption and concurrent local "
                            + "mutation are excluded from the history operations. The theorem "
                            + "constructs a finite valid dependency plan for every finite root "
                            + "set and makes no assertion "
                            + "about storage cost, elapsed time, or the cost of finding a plan."))),
                DescribeRole.Theorem))));

    private static Formula ContractFormula()
    {
        Formula m = F.Id("M");
        Formula s = F.Id("S");
        Formula schedule = F.Id("schedule");
        Formula l = F.Id("L");
        Formula roots = F.Id("R");
        Formula b = Seq(m, Dot, F.Id("B"));
        Formula snapshots = Seq(m, Dot, F.Id("snapshots"));
        Formula p = Call("planFor", b, s, roots);
        Formula nodes = Seq(p, Dot, F.Id("nodes"));
        Formula shared = Seq(LambdaLower, Sp, F.Id("n"), Sp, Mapsto, Sp,
            Call("run", b, Call("schedule", F.Id("n"))));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, m, Comma, Sp, s, Sp, InMacro, Sp, snapshots, Comma, Sp,
            schedule, Comma, Sp, l, Comma, Sp, roots, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, F.Id("n"), Comma, Sp, F.Id("W"), Comma, Sp, F.Id("a"), Comma,
            Sp, Call("store", F.Id("W"), F.Id("a")), Sp, InMacro, Sp,
            Call("schedule", F.Id("n")), Sp, Rightarrow, Sp, F.Id("W"), Sp, InMacro, Sp,
            snapshots, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("Reachable", m, l), Sp, Rightarrow, Sp,
            Seq(p, Dot, F.Id("roots")), Sp, Eq, Sp, roots, Sp, Land, Sp,
            Call("Guarantees", m, s, schedule, l, p,
                Call("execute", b, s, shared, l, nodes)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
