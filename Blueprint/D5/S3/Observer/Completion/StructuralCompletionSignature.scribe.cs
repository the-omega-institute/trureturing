using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class StructuralCompletionSignatureDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Completion/StructuralCompletionSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A structural completion signature is the one-orbit quotient of the constrained "
            + "zero-defect carrier, and a gauge-fixed completion constant is its sole value.",
        H("Structural Completion Signatures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-point-signature-and-constant-vocabulary"),
                DeclarationHandle.Create(DeclarationPrefix + "completion_vocabulary"),
                H("Completion points, signatures, and constants"),
                StatementSource.FromAuthor(VocabularyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be the supplied normalization constraint, Delta the structural "
                            + "defect, and zero_D its distinguished zero. The completion carrier "
                            + "K consists exactly of the parameters in N with zero defect. It is "
                            + "implemented as Mathlib's SubMulAction, so the displayed gauge "
                            + "stability premise is the closure needed to act on K.")),
                    Paragraph(Text(
                        "The signature Sigma is Mathlib's canonical orbitRel quotient K/G. The "
                            + "source's one-orbit naming condition is represented by nonemptiness "
                            + "of K together with IsPretransitive G K. Mathlib's exact "
                            + "pretransitive_iff_unique_quotient_of_nonempty theorem identifies "
                            + "that condition with Sigma carrying a Unique instance.")),
                    Paragraph(Text(
                        "The completion-constant predicate contains both halves of uniqueness: "
                            + "kappa belongs to the gauge-fixed value set and every value in that "
                            + "set equals kappa. It is therefore equivalent to the fixed value set "
                            + "being the singleton containing kappa; an empty set cannot satisfy "
                            + "the predicate vacuously.")),
                    Paragraph(Text(
                        "The unconditioned quotient is not forced to collapse: the Lean probes "
                            + "construct a two-point, gauge-stable completion carrier with two "
                            + "distinct orbit classes. Collapse occurs exactly after the "
                            + "nonempty pretransitive naming condition is supplied."))),
                DescribeRole.Theorem))));

    private static Formula VocabularyFormula()
    {
        Formula group = F.Id("G");
        Formula parameter = F.Id("A");
        Formula defectSpace = F.Id("D");
        Formula valueType = F.Id("R");
        Formula normalization = Seq(Mathcal, Grp(F.Id("N")));
        Formula defect = Delta;
        Formula zeroD = Seq(D(0), Underscore, Grp(defectSpace));
        Formula point = F.Id("a");
        Formula gauge = F.Id("g");
        Formula points = Call("K", normalization, defect, zeroD);
        Formula signature = Call("CompletionSignature", points, group);
        Formula fixedValues = F.Id("S");
        Formula kappa = Kappa;

        Formula gaugeStable = Seq(
            Open, Forall, Sp, gauge, Colon, Sp, group, Comma, Sp,
            point, Colon, Sp, parameter, Comma, Sp,
            point, InMacro, Sp, points, Sp, Rightarrow, Sp,
            Call("smul", gauge, point), InMacro, Sp, points, Close);

        Formula pointClause = Seq(
            Open, Forall, Sp, point, Colon, Sp, parameter, Comma, Sp,
            point, InMacro, Sp, points, Sp, Iff, Sp,
            Open, point, InMacro, Sp, normalization, Sp, Land, Sp,
            Call("Delta", point), Sp, Eq, Sp, zeroD, Close, Close);

        Formula signatureClause = Seq(
            Call("HasStructuralCompletionSignature", normalization, defect, zeroD),
            Sp, Iff, Sp, Call("Nonempty", Call("Unique", signature)));

        Formula constantClause = Seq(
            Open, Forall, Sp, valueType, Comma, Sp,
            fixedValues, Colon, Sp, Call("Set", valueType), Comma, Sp,
            kappa, Colon, Sp, valueType, Comma, Sp,
            Call("IsCompletionConstant", fixedValues, kappa), Sp, Iff, Sp,
            fixedValues, Sp, Eq, Sp, OpenBrace, kappa, CloseBrace, Close);

        return Disp(Seq(
            Forall, Sp, group, Comma, Sp, parameter, Comma, Sp, defectSpace, Comma, Sp,
            Call("Group", group), Sp, Land, Sp, Call("MulAction", group, parameter),
            Sp, Land, Sp, gaugeStable, Sp, Rightarrow, RowBreak,
            pointClause, Sp, Land, RowBreak,
            Open, signatureClause, Close, Sp, Land, RowBreak,
            constantClause, Dot));
    }
}
