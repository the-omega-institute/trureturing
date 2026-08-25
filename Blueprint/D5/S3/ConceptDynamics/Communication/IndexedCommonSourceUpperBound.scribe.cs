using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class IndexedCommonSourceUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Communication/IndexedCommonSourceUpperBound."
            + "indexed_common_source_upper_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An indexed family of messages cannot jointly distinguish more than its "
            + "common source readout.",
        H("Indexed Common-Source Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("the-joint-message-readout-factors-through-the-common-source"),
            DeclarationHandle.Create(Declaration),
            H("The joint message readout remains below its common source"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each component premise supplies a factor from the common source value "
                        + "to that message value. The proof selects those factors and bundles "
                        + "their outputs into the canonical dependent joint readout.")),
                Paragraph(Text(
                    "Evaluating the assembled factor at a state reduces componentwise to the "
                        + "given message factorization, so the entire message family remains a "
                        + "postprocessing of the same source."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula sourceType = F.Id("B");
        Formula messageType = F.Id("M");
        Formula i = F.Id("i");
        Formula message = F.Id("m");
        Formula source = F.Id("s");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula messageAt = new Formula.Subscript(messageType, i);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, index, Comma, Sp, state, Comma, Sp, sourceType,
                Colon, Sp, type, Comma, Sp, messageType, Colon, Sp, index,
                Sp, To, Sp, type, Comma),
            Seq(
                message, Colon, Sp, Forall, Sp, i, Colon, Sp, index, Comma, Sp,
                state, Sp, To, Sp, messageAt, Comma, Sp, source, Colon, Sp,
                state, Sp, To, Sp, sourceType, Comma),
            Seq(
                Open, Forall, Sp, i, Colon, Sp, index, Comma, Sp,
                Call("Refines", new Formula.Apply(message, [i]), source), Close, Sp,
                Rightarrow, Sp,
                Call("Refines", Call("jointReadout", message), source), Dot),
        ]));
    }
}
