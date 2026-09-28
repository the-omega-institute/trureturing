using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Realization;

internal sealed class CommutingReversibleRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting finite realizations have exact itinerary capacity and a tail-shift reversibility criterion.",
        H("Commuting Reversible Realization"),
        Blocks(Describe.Lean(
            DescribeId.Create("commuting-reversible-realization-capacity-and-stabilization"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/Realization/CommutingReversibleRealization."
                + "commuting_reversible_realization"),
            H("Exact capacity, reversible existence, and stabilization"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let S be a nonempty finite source, A a finite alphabet, D a total source "
                    + "update, q its readout, and n a nonnegative horizon. The complete itinerary "
                    + "iota(s) has coordinate j equal to q(D^j(s)). Let T be its actual range, "
                    + "K its cardinality, sigma the tail shift on T, and gT(t) the coordinate t(0). "
                    + "Let W_n be the range of words through time n, N_n its cardinality, and "
                    + "R_n the kernel of the finite-word map.")),
                Paragraph(Text(
                    "Write C(M,I,F,g) for a finite total carrier M with total preparation I, "
                    + "update F and readout g, satisfying I(D(s)) = F(I(s)) and "
                    + "g(F^j(I(s))) = q(D^j(s)) for every source s and every 0 <= j <= n. "
                    + "The quantifiers over implementations below use exactly this condition. "
                    + "No surjectivity of I is required for the lower bound.")),
                Paragraph(Text(
                    "The first clause gives correctness at every future time and counts both "
                    + "the prepared image and the whole carrier. The second gives the explicit "
                    + "K-state implementation M = T with surjective preparation. Together they "
                    + "make K the exact minimum. If sigma is injective, finiteness makes this "
                    + "same implementation reversible, so the reversible minimum is also K.")),
                Paragraph(Text(
                    "For necessity, commutation makes P = I(S) forward invariant. An injective "
                    + "update restricts to a bijection on finite P. The surjective behavioral "
                    + "factor from P to T intertwines the updates; lifting a state of T first "
                    + "to P and then to a predecessor proves that sigma is surjective. Finiteness "
                    + "then gives injectivity. Unprepared states and duplicated behaviors do not "
                    + "alter this argument.")),
                Paragraph(Text(
                    "For the final equivalence, prefix projection is a surjection from T to W_n. "
                    + "Equal cardinalities make it injective, identifying R_n with the complete "
                    + "itinerary kernel. This kernel lies inside R_(n+1), which lies inside R_n. "
                    + "Conversely, equality of consecutive kernels identifies the stable finite "
                    + "quotient with the complete quotient, giving equal cardinalities."))),
            DescribeRole.Theorem))));

    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Sub(Formula x, Formula n) => new Formula.Subscript(x, n);

    private static Formula Statement()
    {
        Formula m = F.Id("M"), i = F.Id("I"), f = F.Id("F"), g = F.Id("g");
        Formula t = F.Id("T"), k = F.Id("K"), n = F.Id("n"), x = F.Id("x"), j = F.Id("j");
        Formula iota = F.Id("iota"), sigma = F.Id("sigma"), gt = F.Id("gT");
        Formula contract = App(F.Id("C"), m, i, f, g);
        Formula allTime = Seq(Forall, Sp, x, Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
            Forall, Sp, j, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            App(g, App(Seq(f, Caret, Grp(j)), App(i, x))), Sp, Eq, Sp,
            App(F.Id("q"), App(Seq(F.Id("D"), Caret, Grp(j)), x)));
        return Disp(Seq(
            Open, Forall, Sp, m, Comma, Sp, i, Comma, Sp, f, Comma, Sp, g, Comma, Sp,
            contract, Sp, Rightarrow, Sp, Open, allTime, Close, Sp, Land, Sp,
            k, Sp, Le, Sp, Card(Call("range", i)), Sp, Le, Sp, Card(m), Sp, Land, Sp,
            Open, Call("Bijective", f), Sp, Rightarrow, Sp, Call("Bijective", sigma), Close,
            Close, Sp, Land, RowBreak,
            Grp(), Call("Finite", t), Sp, Land, Sp, Call("Surjective", iota), Sp, Land, Sp,
            App(F.Id("C"), t, iota, sigma, gt), Sp, Land, RowBreak,
            Grp(), Open, Open, Exists, Sp, m, Comma, Sp, i, Comma, Sp, f, Comma, Sp, g, Comma, Sp,
            contract, Sp, Land, Sp, Call("Bijective", f), Close, Sp, Iff, Sp,
            Call("Injective", sigma), Close, Sp, Land, RowBreak,
            Grp(), Open, Call("Injective", sigma), Sp, Iff, Sp,
            Call("Bijective", sigma), Close, Sp, Land, RowBreak,
            Grp(), Open, k, Sp, Eq, Sp, Sub(F.Id("N"), n), Sp, Iff, Sp,
            Sub(F.Id("R"), n), Sp, Eq, Sp,
            Sub(F.Id("R"), Seq(n, Sp, Plus, Sp, D(1))), Close, Dot));
    }
}
