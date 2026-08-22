using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class PublicUnlinkabilityAccountabilityIncompatibilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nontrivial identity makes public unlinkability incompatible with complete accountability.",
        H("Public Unlinkability and Accountability Incompatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("public-unlinkability-accountability-incompatible"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/"
                        + "PublicUnlinkabilityAccountabilityIncompatibility."
                        + "public_unlinkability_accountability_incompatible"),
                H("Public unlinkability and complete accountability are incompatible"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a public transcript and I an identity readout on the same "
                            + "source carrier. Identity is nontrivial when two source states have "
                            + "different identity readouts.")),
                    Paragraph(Text(
                        "Structural public unlinkability says the canonical common-core relation "
                            + "of P and I is the top setoid, so its common coarsening is trivial. "
                            + "Complete public accountability says I factors through P via the "
                            + "canonical Refines relation.")),
                    Paragraph(Text(
                        "The displayed conclusion publicly negates the conjunction of these two "
                            + "clauses. It imports the existing common-core construction and "
                            + "applies its obstruction theorem without redeclaring either family "
                            + "primitive."))),
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula publicType = Subscript(F.Id("B"), F.Id("P"));
        Formula identityType = Subscript(F.Id("B"), F.Id("I"));
        Formula publicTranscript = F.Id("P");
        Formula identity = F.Id("I");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula top = F.Id("top");
        Formula identityNontrivial = Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, stateType, Comma, Sp,
            Call("I", left), Sp, Neq, Sp, Call("I", right));
        Formula publicUnlinkability = Seq(
            Call("commonCoreRelation", publicTranscript, identity), Sp, Eq, Sp, top);
        Formula completeAccountability = Call("Refines", identity, publicTranscript);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, publicType, Comma, Sp,
            identityType, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            publicTranscript, Colon, Sp, Arrow(stateType, publicType), Comma, Sp,
            identity, Colon, Sp, Arrow(stateType, identityType), Comma, RowBreak, Grp(),
            Grp(identityNontrivial), Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Grp(Seq(
                publicUnlinkability, Sp, Land, Sp, completeAccountability)), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
