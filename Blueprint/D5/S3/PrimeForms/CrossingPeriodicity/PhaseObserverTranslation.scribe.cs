using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.CrossingPeriodicity;

internal sealed class PhaseObserverTranslationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The winding-phase observer carries the admissible crossing sandwich to the "
            + "explicit translation by minus two on every rational additive circle.",
        H("Phase Observer Translation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-observer-descends-to-translation"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation."
                        + "phase_observer_descends_to_translation"),
                H("The phase observer descends to translation"),
                StatementSource.FromAuthor(TranslationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source state space consists of positive matrices satisfying the "
                            + "existing admissibility predicate. Its update is the existing "
                            + "crossing sandwich, which preserves that predicate.")),
                    Paragraph(Text(
                        "For an arbitrary rational modulus m, the observer sends a matrix to "
                            + "its winding phase in the additive quotient by m. The target map "
                            + "is constructed explicitly as subtraction by two.")),
                    Paragraph(Text(
                        "The exact single-step phase law proves that observing after the source "
                            + "update is the same as translating after observation. Thus the "
                            + "phase dynamics descends to the displayed translation."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod")),
        ]));

    private static Formula TranslationFormula()
    {
        Formula modulus = F.Id("m");
        Formula matrix = F.Id("A");
        Formula phase = F.Id("Psi");
        Formula observer = Seq(F.Id("q"), Underscore, Grp(modulus));
        Formula translation = Seq(F.Id("T"), Underscore, Grp(modulus));
        Formula update = F.Id("sigma");
        Formula z = F.Id("z");
        Formula circle = Call("AddCircle", modulus);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, modulus, InMacro, Sp, Mathbb, Grp(F.Id("Q")), Comma, Sp,
                observer, Open, matrix, Close, Eq,
                OpenBracket, phase, Open, matrix, Close, CloseBracket,
                Underscore, Grp(modulus)),
            Seq(
                translation, Colon, Sp, circle, Sp, To, Sp, circle, Comma, Sp,
                translation, Open, z, Close, Eq, z, Minus, D(2)),
            Seq(
                observer, Sp, Circ, Sp, update, Eq,
                translation, Sp, Circ, Sp, observer, Dot),
        ]));
    }
}
