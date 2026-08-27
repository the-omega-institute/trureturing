using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FinitePrimeTimeRectangleCertificateDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/PredictionDepth/FinitePrimeTimeRectangleCertificate."
            + "finite_prime_time_rectangle_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite dimension-bounded quantum certificate extends to a finite rectangular window.",
        H("Finite Prime-Time Rectangle Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-time-rectangle-certificate"),
                DeclarationHandle.Create(Declaration),
                H("A complete effect family has a complete finite rectangle"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The input family consists of centered effects on the canonical real "
                            + "trace-zero Hermitian carrier. If its full real span is the carrier, "
                            + "at most d squared minus one concrete index-time pairs already span "
                            + "it and separate all density states.")),
                    Paragraph(Text(
                        "From those pairs, J is constructed as their first-coordinate image and "
                            + "T as one plus the supremum of their second coordinates. Every "
                            + "selected pair lies in J times the times below T, so equality on the "
                            + "whole rectangle implies equality on the selected certificate.")),
                    Paragraph(Text(
                        "The proof imports the frozen finite-pair certificate and adds only the "
                            + "canonical finite-rectangle construction required by the source."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula Apply(Formula function, params Formula[] arguments) =>
            new Formula.Apply(function, [.. arguments]);
        Formula d = F.Id("d"), effects = F.Id("E"), selected = F.Id("S");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula pairType = Seq(naturals, Times, naturals);
        Formula carrier = Call("HermitianTraceZero", Call("Fin", d));
        Formula allSpan = Seq(
            Call("span", reals, Call("range", effects)), Sp, Eq, Sp, Call("top"));
        Formula selectedSpan = Seq(
            Call("span", reals, Call("range", Call("restrict", effects, selected))),
            Sp, Eq, Sp, Call("top"));
        Formula bound = Seq(
            Call("card", selected), Sp, Leq, Sp,
            new Formula.Power(d, D(2)), Sp, Minus, Sp, D(1));
        Formula rho = Rho, sigma = SigmaLower;
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula Readout(Formula state, Formula index, Formula time) =>
            Seq(Re, Open, Call("Tr", Seq(Call("matrix", state), Sp,
                Apply(effects, Seq(Open, index, Comma, Sp, time, Close)))), Close);
        Formula selectedSeparates = Seq(
            Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, stateType, Comma, Sp,
            Open, Forall, Sp, F.Id("q"), InMacro, Sp, selected, Comma, Sp,
            Readout(rho, Call("fst", F.Id("q")), Call("snd", F.Id("q"))), Sp, Eq, Sp,
            Readout(sigma, Call("fst", F.Id("q")), Call("snd", F.Id("q"))), Close,
            Sp, Rightarrow, Sp, rho, Sp, Eq, Sp, sigma);
        Formula indices = F.Id("J"), horizon = F.Id("T");
        Formula rectangleSeparates = Seq(
            Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, stateType, Comma, Sp,
            Open, Forall, Sp, F.Id("p"), InMacro, Sp, indices, Comma, Sp,
            F.Id("t"), InMacro, Sp, naturals, Comma, Sp,
            F.Id("t"), Sp, Lt, Sp, horizon, Comma, Sp,
            Readout(rho, F.Id("p"), F.Id("t")), Sp, Eq, Sp,
            Readout(sigma, F.Id("p"), F.Id("t")), Close,
            Sp, Rightarrow, Sp, rho, Sp, Eq, Sp, sigma);

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak, Grp(),
            effects, Colon, Sp, pairType, Sp, To, Sp, carrier, Comma, RowBreak, Grp(),
            allSpan, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, selected, Colon, Sp, Call("Finset", pairType), Comma, Sp,
            bound, Sp, Land, RowBreak, Grp(),
            selectedSpan, Sp, Land, RowBreak, Grp(),
            Open, selectedSeparates, Close, Sp, Land, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            indices, Sp, Colon, Eq, Sp, Call("image", F.Id("fst"), selected), Semi, Sp,
            horizon, Sp, Colon, Eq, Sp, D(1), Sp, Plus, Sp,
            Call("sup", F.Id("snd"), selected), Semi, RowBreak, Grp(),
            rectangleSeparates, Dot));
    }
}
