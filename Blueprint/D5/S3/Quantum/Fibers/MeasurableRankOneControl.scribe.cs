using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class MeasurableRankOneControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint probability laws for arbitrary independent measurable rank-one controls.",
        H("Measurable Random Control and Actual Complete Records"), Blocks(
            Describe.Lean(DescribeId.Create("arbitrary-control-joint-tv"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/MeasurableRankOneControl.arbitrary_protocol_tv_supremum"),
                H("The arbitrary-control complete-record supremum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("U"), Colon, C("WaitFamily", F.Id("n")), Comma,
                    C("UnitarySemigroup", F.Id("U")), Rightarrow, Sp,
                    Forall, Sp, F.Id("X"), Comma, F.Id("Y"), Colon, C("Density", F.Id("n")), Comma,
                    C("iSup", Seq(F.Id("R"), Colon, C("Control", C("unitaryMenu", F.Id("U")))),
                        C("measurableTotalVariation",
                            C("jointLaw", C("unitaryMenu", F.Id("U")), F.Id("R"), F.Id("X")),
                            C("jointLaw", C("unitaryMenu", F.Id("U")), F.Id("R"), F.Id("Y")))), Eq,
                    C("ENNRealOfReal", C("FirstReadTVSup", F.Id("U"), F.Id("X"), F.Id("Y")))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input domain is all complex positive semidefinite trace-one matrices on an arbitrary finite index type. WaitFamily(n) denotes maps from nonnegative real times to complex n-by-n matrices. UnitarySemigroup(U) means U(0) is the identity, U(t+u) equals U(u) U(t), and U(t)-adjoint times U(t) is the identity for every pair of nonnegative times. unitaryMenu(U) uses these three proofs. The iSup notation binds R over Control of that menu, at any fixed seed universe; ENNRealOfReal is ENNReal.ofReal applied to the real first-read supremum.")),
                    Paragraph(Text("A seed is sampled from an arbitrary probability space with one input-independent law. For each seed it selects an actual finite Stop/wait/complete-rank-one-read feedback tree. Tree sizes need not be uniformly bounded; waiting times range over all nonnegative reals.")),
                    Paragraph(Text("A terminal record is coded by its finite list of read outcomes. Structural induction proves that this code is injective for each fixed tree. Together with the retained seed, the code determines the original dependent record and all its control decisions and waits. Stop before any read is the empty list. Zero-probability branches remain present and require no conditional-probability division.")),
                    Paragraph(Text("For each density and tree, the common record measure is the finite sum of Dirac masses at these codes, weighted by the actual ludersLaw. The original law_nonnegative, law_mass and luders_law_eq establish nonnegativity, normalization and the operational correspondence. Every code outside the selected tree has zero mass.")),
                    Paragraph(Text("A measurable random control requires the mass of every fixed outcome word to be a measurable function of the seed, for every input density. This is a condition for the protocol to define a probability law. It is necessary for a measurable record kernel, and is sufficient because finite-alphabet words form a countable discrete space: every event mass is the countable sum of its singleton masses. Neither the seed law nor the selected strategy can depend on the unknown input.")),
                    Paragraph(Text("The recordKernel is constructed from these actual finite measures. Its rows are probability measures, hence it is a Markov kernel. jointLaw is Mathlib's compProd of the seed probability law and that kernel; normalization follows from the existing Markov compProd probability instance. Its measurable-event probability is the integral of the actual finite record masses whose codes lie in the corresponding seed section. This establishes a joint measure, including events that depend on both the seed and the record.")),
                    Paragraph(Text("Kernel measurability makes every real event-section probability measurable, and normalization bounds it between zero and one. It is therefore integrable on the seed probability space. The existing arbitrary_random_control_event_bound applies to these section events. Taking the measurable-event supremum gives the upper TV bound. Injective coding preserves the finite complete-record TV. Constant strategies on a one-point probability space then recover the deterministic actual_protocol_tv_supremum, giving the reverse bound and the stated equality.")),
                    Paragraph(Text("A common measurable coarse output is a measurable map of the joint seed-and-record space, used identically for both input laws. The existing measurable_total_variation_map_le applies directly, so forgetting the seed, discarding outcomes, or retaining any measurable function of the complete record cannot increase total variation. This consequence introduces no additional mathematical declaration."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
