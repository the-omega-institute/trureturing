using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class CompactHausdorffDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula source = F.Id("X");
        Formula quotient = F.Id("B");
        Formula target = F.Id("Y");
        Formula map = F.Id("q");
        Formula observable = F.Id("T");
        Formula factor = F.Id("factor");
        Formula mapType = Call("ContinuousMap", source, quotient);
        Formula observableType = Call("ContinuousMap", source, target);
        Formula factorType = Call("ContinuousMap", quotient, target);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, quotient, Comma, Sp, target,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Call("TopologicalSpace", source), CloseBracket, Comma, Sp,
            OpenBracket, Call("TopologicalSpace", quotient), CloseBracket, Comma, Sp,
            OpenBracket, Call("TopologicalSpace", target), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("CompactSpace", source), CloseBracket, Comma, Sp,
            OpenBracket, Call("T2Space", quotient), CloseBracket, Comma, RowBreak, Grp(),
            map, Colon, Sp, mapType, Comma, Sp,
            Call("Surjective", map), Comma, RowBreak, Grp(),
            observable, Colon, Sp, observableType, Comma, Sp,
            Call("FactorsThrough", observable, map), RowBreak, Grp(),
            Rightarrow, Sp, Call("IsClosedMap", map), Sp, Land, Sp,
            Call("IsQuotientMap", map), Sp, Land, RowBreak, Grp(),
            Exists, Bang, Sp, factor, Colon, Sp, factorType, Comma, Sp,
            observable, Sp, Eq, Sp, factor, Sp, Circ, Sp, map, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Compact-to-Hausdorff continuous surjections are automatically closed and quotient, enabling unique continuous descent.",
            H("Automatic Quotient and Continuous Descent"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("compact-hausdorff-automatic-quotient"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/Transport/CompactHausdorffDescent."
                            + "compact_hausdorff_automatic_quotient"),
                    H("Compact-to-Hausdorff maps descend continuously"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The source is compact, the intermediate space is Hausdorff, "
                                + "and q is a continuous surjection. The conclusion exposes "
                                + "both closedness and quotientness of q.")),
                        Paragraph(Text(
                            "The continuous map T is constant on q-fibers. The imported "
                                + "continuous-descent theorem then constructs the unique "
                                + "continuous factor through q."))),
                    DescribeRole.Theorem))));
    }
}
