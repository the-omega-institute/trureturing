using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class FiniteLedgerCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible legal ledgers admit at most two delayed corrections per proposition.",
        H("Finite Ledger Correction"),
        Blocks(
            Paragraph(Text(
                "Let P, Proof, Ax and Model be arbitrary types, k kernel data, D a finite "
                + "subset of P, and L a chain of actual LegalLedger objects. Each step is a "
                + "total admissible transformation, and its application gives the next ledger. "
                + "Admissibility retains every old node, edge and selected proof witness. "
                + "Consistency means that no proposition and its k-negation are both Proved. "
                + "No soundness or universal certificate-existence assumption is used.")),
            Paragraph(Text(
                "The readout s(t,p) is frozen when p belongs to the certified core, refuted "
                + "when only its negation belongs, and open when neither belongs. Claim labels "
                + "also include unverified, which is not a fourth ledger state. A Policy has "
                + "arbitrary initial claims q(0,p) on the subtype D. Its mismatch set is "
                + "M(t) = {p in D : q(t,p) differs from s(t,p)}. C(t) is a subset of M(t), "
                + "nonempty whenever M(t) is nonempty. Consequently it is empty when M(t) is "
                + "empty. Only selected claims change: q(t+1,p) is s(t,p) for p in C(t) and "
                + "q(t,p) otherwise. The next comparison uses L(t+1), so the ledger can change "
                + "immediately after a correction of the old readout.")),
            Paragraph(Text(
                "Write Delta(p) for the actual times t at which s(t+1,p) differs from s(t,p), "
                + "R(p) for {t : p is in C(t)}, and E for {(t,p) : p is in C(t)}. "
                + "Stable(T) abbreviates: for every t at least T and p in D, s(t,p) = s(T,p). "
                + "Bars on finite sets denote their cardinalities. Subsingleton means any two "
                + "members are equal.")),
            Paragraph(Text(
                "U(0) lists one claim (p,q(0,p)) for each p in D. B(t) lists (p,s(t,p)) "
                + "once for every p in C(t), and U(t+1) appends B(t) to U(t). Sequence "
                + "positions provide increasing record numbers. Last(U,p) reads the last "
                + "claim about p; its unverified default for an absent entry is never needed "
                + "on D because U(0) contains every member. The identity below connects this "
                + "single append-only sequence to the Policy claims.")),
            Describe.Lean(
                DescribeId.Create("finite-ledger-correction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DependencyTopology/FiniteLedgerCorrection."
                    + "finite_ledger_correction"),
                H("Finite support, two corrections per proposition, and permanent quietness"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Frozen membership persists by node retention. Refuted membership "
                        + "persists because the retained negation has an actual permitted proof, "
                        + "and consistency excludes a proof of the proposition in any later core. "
                        + "Thus every non-open readout persists and each Delta(p) is a subsingleton.")),
                    Paragraph(Text(
                        "Two actual corrections at a < b force an actual change at some t with "
                        + "a <= t < b. Otherwise induction through the exact update rule keeps "
                        + "the claim corrected at a equal to the unchanged readout, contradicting "
                        + "selection of a mismatch at b. Equal endpoint readouts are constant "
                        + "through the interval by terminal persistence. Consequently correction "
                        + "times inject into the two phases distinguished by whether the current "
                        + "readout is open. The combined events inject into D times those two "
                        + "phases. These injections first prove actual support finite; only then "
                        + "are finite cardinalities and the natural-number infinite sum used. "
                        + "The sum equals the event cardinality by its finite time fibers.")),
                    Paragraph(Text(
                        "Finite actual revisions give a terminal value for each proposition "
                        + "by LedgerLimit.finite_revisions_have_terminal_value. A finite maximum "
                        + "gives a common T. For any actual stabilization time T, the exact "
                        + "mismatch recurrence is M(t+1) = M(t) minus C(t). Nonempty mismatches "
                        + "strictly decrease, so FiniteDefectTermination.finite_defect_repairs_terminate "
                        + "gives emptiness within at most |D| more steps; the same recurrence "
                        + "makes emptiness permanent.")),
                    Paragraph(Text(
                        "The result includes empty D, arbitrary partial nonempty selections, "
                        + "and unverified initial claims. It bounds correction records, with "
                        + "no additional fairness premise and no uniform bound on T. Permanent "
                        + "quietness concerns M on D; the whole ledger need not stop changing."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula p = F.Id("p"), t = F.Id("t"), T = F.Id("T"), stop = F.Id("stop");
        Formula Dm = F.Id("D"), k = F.Id("k");
        Formula C = Call("C", t), R = Call("R", p), E = F.Id("E");
        Formula total = Seq(Sum, Underscore, Grp(t, Eq, D(0)), Caret, Grp(Infty), Sp, Card(C));
        Formula stable = Call("Stable", T);
        return Disp(Seq(
            Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Proof"), Comma, Sp,
            F.Id("Ax"), Comma, Sp, F.Id("Model"), Colon, Sp, F.Id("Type"), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Call("KernelData", F.Id("P"), F.Id("Proof"),
                F.Id("Ax"), F.Id("Model")), Comma, RowBreak, Grp(),
            Forall, Sp, F.Id("L"), Colon, Sp, Call("Chain", k), Comma, Sp,
            Forall, Sp, Dm, Colon, Sp, Call("Finset", F.Id("P")), Comma, Sp,
            Forall, Sp, F.Id("policy"), Colon, Sp, Call("Policy", F.Id("L"), Dm), Comma, Sp,
            Call("Consistent", k), Sp, Implies, RowBreak, Grp(),
            Open, Forall, Sp, p, Colon, Sp, Dm, Comma, Sp,
                Call("Subsingleton", Call("Delta", p)), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, p, Colon, Sp, Dm, Comma, Sp,
                Call("Finite", R), Sp, Land, Sp, Card(R), Sp, Le, Sp, D(2), Close,
                Sp, Land, RowBreak, Grp(),
            Call("Finite", E), Sp, Land, Sp, Card(E), Sp, Eq, Sp, total, Sp, Land, Sp,
                total, Sp, Le, Sp, D(2), Sp, Times, Sp, Card(Dm), Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, T, Comma, Sp, stable, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, T, Comma, Sp, stable, Sp, Implies, Sp,
                Exists, Sp, stop, Comma, Sp, stop, Sp, Le, Sp, T, Sp, Plus, Sp, Card(Dm),
                Sp, Land, Sp, Open, Forall, Sp, t, Sp, Ge, Sp, stop, Comma, Sp,
                Call("M", t), Sp, Eq, Sp, Emptyset, Close, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, t, Sp, p, Comma, Sp, Call("Last", Call("U", t), p),
                Sp, Eq, Sp, Call("q", t, p), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, t, Comma, Sp,
                Call("U", Seq(t, Plus, D(1))), Sp, Eq, Sp,
                Call("append", Call("U", t), Call("B", t)), Sp, Land, Sp,
                Call("length", Call("B", t)), Sp, Eq, Sp, Card(C), Sp, Land, RowBreak, Grp(),
                Call("Nodup", Call("map", F.Id("fst"), Call("B", t))), Sp, Land, Sp,
                Forall, Sp, p, Sp, F.Id("sigma"), Comma, Sp,
                Open, p, Comma, F.Id("sigma"), Close, Sp, InMacro, Sp, Call("B", t),
                Sp, Leftrightarrow, Sp, Open, p, Sp, InMacro, Sp, C, Sp, Land, Sp,
                F.Id("sigma"), Sp, Eq, Sp, Call("s", t, p), Close, Close, Dot));
    }

    private static Formula Card(Formula f) => Seq(Bar, f, Bar);
}
