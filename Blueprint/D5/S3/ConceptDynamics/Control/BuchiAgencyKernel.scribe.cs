using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class BuchiAgencyKernelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/BuchiAgencyKernel.live_agency_buchi_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nested robust renewal kernel has a safe policy that renews infinitely often.",
        H("Buchi Agency Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("live-agency-is-safe-and-renews-infinitely-often"),
                DeclarationHandle.Create(Declaration),
                H("Live agency is robustly safe and renews infinitely often"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The inner regional attractor is the least fixed point of robust "
                            + "finite-horizon reachability. Finiteness supplies a natural-number "
                            + "arrival rank for every state in this attractor.")),
                    Paragraph(Text(
                        "At the outer greatest fixed point, rank-positive states choose an action "
                            + "whose possible successors have smaller rank. Rank-zero states lie "
                            + "in the renewal set and choose an action back into the live kernel.")),
                    Paragraph(Text(
                        "The resulting policy keeps every adversarial trajectory in LiveAgency, "
                            + "hence in the robust freedom kernel. Strict descent forces another "
                            + "renewal after every time bound, which is the Buchi condition."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Control/FiniteHorizonReachability"))]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula game = F.Id("G");
        Formula renew = Seq(F.Id("L"), Underscore, Grp(F.Id("renew")));
        Formula live = Call("LiveAgency", game, renew);
        Formula free = Seq(Call("FreeKernel", game), Underscore, Grp(F.Id("rob")));
        Formula rank = F.Id("r");
        Formula policy = F.Id("pi");
        Formula trajectory = F.Id("x");
        Formula time = F.Id("t");
        Formula bound = F.Id("N");
        Formula visit = F.Id("n");

        return Disp(Seq(
            Forall, Sp, game, Comma, Sp, renew, Comma, Sp,
            Call("FiniteGame", game), Sp, Rightarrow, RowBreak, Grp(),
            live, Sp, Subseteq, Sp, free, Sp, Land, RowBreak, Grp(),
            Exists, Sp, rank, Comma, Sp, policy, Comma, Sp,
            Call("RankedRenewalPolicy", game, live, renew, rank, policy), Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, trajectory, Comma, Sp,
            Open, Call("StartsIn", trajectory, live), Sp, Land, Sp,
            Call("Follows", game, policy, trajectory), Close, Sp,
            Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, time, Comma, Sp,
            Call("At", trajectory, time), Sp, InMacro, Sp, free, Close, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, bound, Comma, Sp, Exists, Sp, visit, Comma, Sp,
            bound, Sp, Le, Sp, visit, Sp, Land, Sp,
            Call("At", trajectory, visit), Sp, InMacro, Sp, renew, Dot));
    }
}
