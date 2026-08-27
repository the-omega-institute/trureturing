using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class CanonicalAllowedReasonMeetDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Meet closure gives a canonical unique coarsest allowed sufficient reason.",
        H("Canonical Allowed Reason Meet"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "meet-closed-allowed-reasons-have-unique-coarsest-ratio"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementAlgebra/"
                        + "CanonicalAllowedReasonMeet."
                        + "meet_closed_allowed_reasons_have_unique_coarsest_ratio"),
                H("Meet closure gives the unique coarsest ratio"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the repository's canonical class of effective concept "
                            + "readouts modulo mutual refinement. The frozen kernel order "
                            + "isomorphism identifies this carrier with the order dual of the "
                            + "complete lattice of equivalence relations.")),
                    Paragraph(Text(
                        "Acceptable reasons are exactly the allowed concept classes above the "
                            + "judgment essence. Their meet is constructed by taking the infimum "
                            + "after the kernel-order encoding and transporting it back through "
                            + "the inverse isomorphism.")),
                    Paragraph(Text(
                        "The two displayed premises are the source's existence condition and "
                            + "closure of the allowed doctrine under this relevant nonempty meet. "
                            + "The conclusion exposes both leastness of the canonical meet and "
                            + "unique existence of a least acceptable reason.")),
                    Paragraph(Text(
                        "The source's closing sentence about legal language is an interpretation "
                            + "of this leastness result, not a separately defined predicate. No "
                            + "additional legal-language vocabulary is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula allowed = Seq(Mathcal, Grp(F.Id("E")));
        Formula judgment = F.Id("J");
        Formula reason = F.Id("R");
        Formula conceptClass = Call("ConceptClass", state);
        Formula doctrineType = Seq(Mathcal, Grp(F.Id("P")), Open, conceptClass, Close);
        Formula acceptable = Seq(
            OpenBrace, reason, Sp, InMacro, Sp, conceptClass, Sp, Mid, Sp,
            reason, Sp, InMacro, Sp, allowed, Sp, Land, Sp,
            judgment, Sp, Leq, Sp, reason, CloseBrace);
        Formula encoding = Call("conceptKernelOrderIso", state);
        Formula ratio = Call(
            "symmApply",
            encoding,
            Call("sInf", Call("image", encoding, acceptable)));
        Formula nonempty = Call("Nonempty", acceptable);
        Formula closure = Seq(
            Open, nonempty, Sp, Rightarrow, Sp,
            ratio, Sp, InMacro, Sp, allowed, Close);
        Formula uniqueLeast = Seq(
            Exists, Bang, Sp, reason, Colon, Sp, conceptClass, Comma, Sp,
            Call("IsLeast", acceptable, reason));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")),
            Comma, RowBreak, Grp(),
            allowed, Colon, Sp, doctrineType, Comma, Sp,
            judgment, Colon, Sp, conceptClass, Comma, RowBreak, Grp(),
            nonempty, Sp, Land, Sp, closure,
            RowBreak, Grp(), Rightarrow, Sp,
            Call("IsLeast", acceptable, ratio), Sp, Land,
            RowBreak, Grp(), uniqueLeast, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
