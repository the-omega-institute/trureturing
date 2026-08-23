using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class ExperimentIdentifiabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target is identifiable exactly when it factors through the joint experiment "
            + "readout, equivalently when experiment-indistinguishability implies equal targets.",
        H("Experiment Identifiability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("experiment-identifiability-equivalences"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/ExperimentIdentifiability."
                        + "identifiable_tfae"),
                H("Target identifiability has three equivalent forms"),
                StatementSource.FromAuthor(IdentifiabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An experiment family records one response for every index, and its "
                            + "joint readout collects those responses into a dependent tuple. "
                            + "The target is identifiable when a single factor map recovers the "
                            + "target value from that complete response tuple.")),
                    Paragraph(Text(
                        "The joint kernel contains exactly the state pairs that every experiment "
                            + "fails to distinguish. Containment in the target kernel says that "
                            + "each such pair has the same target value, which is the pointwise "
                            + "fiber-constancy condition in the third clause.")),
                    Paragraph(Text(
                        "On a nonempty state space, the answerability criterion turns fiber "
                            + "constancy into a factor through the joint readout. Membership in "
                            + "the joint kernel is componentwise equality across all experiment "
                            + "indices, completing the equivalence with kernel containment.")),
                    Paragraph(Text(
                        "The Boolean examples separate the boundary: an identity experiment "
                            + "identifies the identity target, while a constant experiment fails "
                            + "factorization, kernel containment, and fiber constancy."))),
                DescribeRole.Theorem))));

    private static Formula IdentifiabilityFormula()
    {
        Formula indexType = F.Id("S");
        Formula stateType = F.Id("X");
        Formula targetType = F.Id("Y");
        Formula responseFamily = F.Id("R");
        Formula experiment = F.Id("e");
        Formula target = F.Id("t");
        Formula factor = F.Id("f");
        Formula index = F.Id("u");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula responseAtIndex = new Formula.Subscript(responseFamily, index);
        Formula responseProduct = Seq(
            Prod, Underscore, Grp(index, Colon, Sp, indexType), responseAtIndex);
        Formula fiberConstancy = Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, stateType, Comma, Sp,
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Equal(Call("e", index, left), Call("e", index, right)), Close,
            Sp, Rightarrow, Sp,
            Equal(Call("t", left), Call("t", right)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                targetType, Colon, Sp, type, Comma, Sp,
                responseFamily, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                experiment, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType,
                Comma, Sp, stateType, Sp, To, Sp, responseAtIndex, Comma, Sp,
                target, Colon, Sp, stateType, Sp, To, Sp, targetType, Comma),
            Seq(
                Call("Nonempty", stateType), Sp, Rightarrow, Sp,
                Operatorname, Grp(F.Id("TFAE")), OpenBracket,
                Exists, Sp, factor, Colon, Sp, responseProduct, Sp, To, Sp,
                targetType, Comma, Sp,
                Equal(target, Seq(factor, Sp, Circ, Sp, Call("jointReadout", experiment))),
                Comma),
            Seq(
                Call("jointKernel", experiment), Sp, Subseteq, Sp,
                Call("targetKernel", target), Comma),
            Seq(fiberConstancy, CloseBracket, Dot),
        ]));
    }
}
