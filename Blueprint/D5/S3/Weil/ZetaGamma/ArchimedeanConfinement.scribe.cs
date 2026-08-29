using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ArchimedeanConfinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var xi = F.Id("xi");
        var level = F.Id("a");
        var scale = F.Id("L");
        var multiplier = Seq(
            D(2), Sp, Pi, Sp, Open,
            Call("mu", xi), Sp, Plus, Sp,
            Call("PX", Call("exp", Seq(D(2), scale)), xi), Close);
        var dangerous = F.Id("B");
        var intervals = F.Id("I");
        var pair = F.Id("p");
        var pairType = Seq(reals, Sp, Times, Sp, reals);
        var intervalUnion = Call(
            "iUnion",
            Seq(pair, Sp, InMacro, Sp, intervals),
            Call("Ioo", Call("fst", pair), Call("snd", pair)));

        var statement = Disp(new Formula.Aligned([
            Seq(Forall, Sp, scale, Comma, Sp, level, Colon, Sp, reals, Comma),
            Seq(Grp(), Call(
                "Tendsto",
                Seq(Open, xi, Colon, Sp, reals, Sp, Mapsto, Sp, multiplier, Close),
                Call("cocompact", reals),
                F.Id("atTop")), Sp, Rightarrow),
            Seq(Grp(), Operatorname, Grp(F.Id("let")), Sp, dangerous, Sp, Colon, Eq, Sp,
                OpenBrace, xi, Sp, InMacro, Sp, reals, Sp, Bar, Sp,
                multiplier, Sp, Lt, Sp, level, CloseBrace, Comma),
            Seq(Grp(), Call("IsBounded", dangerous), Sp, Land, Sp,
                Minus, dangerous, Sp, Eq, Sp, dangerous, Sp, Land),
            Seq(Grp(), Exists, Sp, intervals, Colon, Sp, Call("Finset", pairType), Comma, Sp,
                dangerous, Sp, Eq, Sp, intervalUnion, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Proper growth of the completed-zeta frequency multiplier confines each strict "
                + "sublevel to finitely many symmetric bounded open intervals.",
            H("Archimedean Confinement"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("archimedean-confinement"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaGamma/ArchimedeanConfinement."
                            + "archimedean_confinement"),
                    H("The dangerous frequency set is bounded, symmetric, and interval-finite"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The multiplier is the canonical two-pi rescaling of the existing "
                                + "digamma density mu plus the finite von Mangoldt cosine polynomial "
                                + "PX at exp(2L). The displayed Tendsto premise is the previously "
                                + "established proper-growth clause.")),
                        Paragraph(Text(
                            "Analytic isolated zeros make the threshold level finite inside a "
                                + "compact confinement set. Each connected component is the open "
                                + "interval between its infimum and supremum; both endpoints lie in "
                                + "the finite frontier, giving the displayed finite index set.")),
                        Paragraph(Text(
                            "Repository and pinned-Mathlib searches found no exact existing theorem. "
                                + "The proof directly reuses Zeta23.mu, Zeta23.PX, mu_even, "
                                + "differentiableAt_digamma, analytic isolated-zero codiscreteness, "
                                + "and compact codiscrete finiteness."))),
                    DescribeRole.Theorem))));
    }
}
