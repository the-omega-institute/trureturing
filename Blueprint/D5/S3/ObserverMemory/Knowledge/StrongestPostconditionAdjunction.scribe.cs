using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class StrongestPostconditionAdjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strongest postconditions and weakest preconditions form the direct-image / "
        + "inverse-image adjunction.",
        H("Strongest and Weakest Condition Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strongest-and-weakest-conditions-form-an-adjunction"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Knowledge/StrongestPostconditionAdjunction."
                    + "sp_wp_adjunction"),
                H("Strongest postconditions are left adjoint to weakest preconditions"),
                StatementSource.FromAuthor(AdjunctionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a process F, the strongest postcondition sp_F(P) is the direct "
                            + "image of P. The weakest precondition wp_F(Q) is the inverse image "
                            + "defined by the preceding frozen module.")),
                    Paragraph(Text(
                        "The displayed equivalence quantifies over arbitrary state types, a "
                            + "process, a source predicate P, and a target predicate Q. It states "
                            + "both directions of the image-preimage inclusion adjunction.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Set.image_preimage packages exactly this Galois "
                            + "connection, with Set.image_subset_iff as its defining theorem. The "
                            + "proof only specializes that result and unfolds the two condition "
                            + "definitions. Repository searches found no existing D5 theorem "
                            + "packaging the program-logic vocabulary."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ObserverMemory/Knowledge/WeakestPrecondition"))]));

    private static Formula Condition(
        Formula name, Formula process, Formula predicate) => Seq(
        Operatorname, Grp(name), Underscore, Grp(process),
        Open, predicate, Close);

    private static Formula AdjunctionFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula process = F.Id("F");
        Formula precondition = F.Id("P");
        Formula postcondition = F.Id("Q");
        Formula strongest = Condition(F.Id("sp"), process, precondition);
        Formula weakest = Condition(F.Id("wp"), process, postcondition);

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, yType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            process, Colon, Sp, xType, Sp, To, Sp, yType, Comma, Sp,
            precondition, Sp, Subseteq, Sp, xType, Comma, Sp,
            postcondition, Sp, Subseteq, Sp, yType, Comma, RowBreak,
            strongest, Sp, Subseteq, Sp, postcondition, Sp, Iff, Sp,
            precondition, Sp, Subseteq, Sp, weakest, Dot));
    }
}
