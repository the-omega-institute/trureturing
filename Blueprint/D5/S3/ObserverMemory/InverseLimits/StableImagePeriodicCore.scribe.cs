using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class StableImagePeriodicCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated images of a finite self-map decrease and stabilize at its periodic core.",
        H("Stable Image Periodic Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-iterate-images-stabilize-at-the-periodic-core"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore."
                    + "iterate_range_card_antitone_and_stable"),
                H("Finite iterate images stabilize at the periodic core"),
                StatementSource.FromAuthor(StableImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state carrier and F a self-map. The cardinality of "
                            + "the range of the n-th iterate is antitone in n.")),
                    Paragraph(Text(
                        "Once n reaches the number of states, the range of the n-th iterate is "
                            + "exactly the set of periodic points of F. Thus the decreasing image "
                            + "capacity stabilizes at the cardinality of the periodic core.")),
                    Paragraph(Text(
                        "The proof combines Mathlib's finite pigeonhole theorem with its "
                            + "periodic-point range and iterate lemmas. Pinned-Mathlib, Loogle, "
                            + "GitHub Lean-code, repository, and receipt searches found no equal "
                            + "or stronger stable-image declaration. LeanSearch's API endpoint "
                            + "returned HTTP 404 and supplied no search conclusion.")),
                    Paragraph(Text(
                        "This closes the monotonicity and periodic-core stabilization of the "
                            + "first capacity sequence in the source atom. It does not claim the "
                            + "second quotient-capacity sequence or the linearized rank clause."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Iterate(Formula time) =>
        Seq(F.Id("F"), Caret, Grp(time));

    private static Formula Range(Formula time) =>
        Apply(Seq(Operatorname, Grp(F.Id("range"))), Iterate(time));

    private static Formula Ncard(Formula set) =>
        Apply(Seq(Operatorname, Grp(F.Id("ncard"))), set);

    private static Formula Card(Formula type) =>
        Apply(Seq(Operatorname, Grp(F.Id("card"))), type);

    private static Formula StableImageFormula()
    {
        Formula carrier = F.Id("Y");
        Formula earlier = F.Id("m");
        Formula later = F.Id("n");
        Formula time = F.Id("t");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula periodicCore =
            Apply(Seq(Operatorname, Grp(F.Id("periodicPts"))), F.Id("F"));
        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, carrier, CloseBracket,
            Comma, Esc,
            F.Id("F"), Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Esc,
            Open,
            Forall, Sp, earlier, Comma, Sp, later, InMacro, Sp, natural, Comma, Esc,
            earlier, Sp, Leq, Sp, later, Sp, Rightarrow, Sp,
            Ncard(Range(later)), Sp, Leq, Sp, Ncard(Range(earlier)),
            Close, Sp, Land, Sp, Open,
            Forall, Sp, time, InMacro, Sp, natural, Comma, Esc,
            Card(carrier), Sp, Leq, Sp, time, Sp, Rightarrow, Sp,
            Range(time), Sp, Eq, Sp, periodicCore,
            Close, Dot));
    }
}
