using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FinitePrimeTimeCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete natural-indexed quantum effect family has a finite dimension-bounded certificate.",
        H("Finite Prime-Time Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-effects-have-a-finite-prime-time-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate."
                        + "finite_prime_time_certificate"),
                H("Complete effects have a finite prime-time certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first coordinate of each natural pair is the observer index and the "
                            + "second is time. No arithmetic-primality predicate is imposed on the "
                            + "first coordinate.")),
                    Paragraph(Text(
                        "If the full family spans the real traceless Hermitian carrier, finite-"
                            + "dimensional basis extraction selects concrete pairs whose number is "
                            + "at most the carrier dimension d squared minus one.")),
                    Paragraph(Text(
                        "The selected effects still span the full carrier. The difference of two "
                            + "density states is a traceless Hermitian coordinate, so equality of "
                            + "all selected real trace expectations forces the states to agree."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula d = F.Id("d"), effects = F.Id("E"), selected = F.Id("J");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula pairType = Seq(naturals, Times, naturals);
        Formula hermitian = new Formula.Subscript(
            Seq(Operatorname, Grp(F.Id("Herm"))), Seq(d, Comma, Sp, D(0)));
        Formula allSpan = Seq(
            Call("span", Seq(reals, Comma, Sp,
                Open, effects, Open, F.Id("p"), Comma, Sp, F.Id("t"), Close,
                Colon, Sp, F.Id("p"), Comma, Sp, F.Id("t"), InMacro, Sp, naturals, Close)),
            Sp, Eq, Sp, hermitian);
        Formula selectedSpan = Seq(
            Call("span", Seq(reals, Comma, Sp,
                Open, effects, Open, F.Id("p"), Comma, Sp, F.Id("t"), Close,
                Colon, Sp, Open, F.Id("p"), Comma, Sp, F.Id("t"), Close,
                InMacro, Sp, selected, Close)),
            Sp, Eq, Sp, hermitian);
        Formula bound = Seq(
            new Formula.Apply(Seq(Operatorname, Grp(F.Id("card"))), [selected]),
            Sp, Leq, Sp, new Formula.Power(d, D(2)), Minus, D(1));

        Formula rho = Rho, sigma = SigmaLower;
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula effect = new Formula.Apply(
            effects, [F.Id("p"), F.Id("t")]);
        Formula pairRho = Seq(Re, Sp,
            Call("Tr", Seq(Call("matrix", rho), Sp, effect)));
        Formula pairSigma = Seq(Re, Sp,
            Call("Tr", Seq(Call("matrix", sigma), Sp, effect)));
        Formula separates = Seq(
            Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, stateType, Comma, Sp,
            Open, Forall, Sp, Open, F.Id("p"), Comma, Sp, F.Id("t"), Close,
            InMacro, Sp, selected, Comma, Sp, pairRho, Sp, Eq, Sp, pairSigma, Close,
            Sp, Rightarrow, Sp, rho, Sp, Eq, Sp, sigma);

        return Disp(Seq(
            Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            Call("NeZero", d), Comma, RowBreak,
            Grp(), effects, Colon, Sp, pairType, Sp, To, Sp, hermitian, Comma, RowBreak,
            Grp(), allSpan, Sp, Rightarrow, RowBreak,
            Grp(), Exists, Sp, selected, Colon, Sp, Call("Finset", pairType), Comma, Sp,
            bound, Sp, Land, RowBreak,
            Grp(), selectedSpan, Sp, Land, RowBreak,
            Grp(), separates, Dot));
    }
}
