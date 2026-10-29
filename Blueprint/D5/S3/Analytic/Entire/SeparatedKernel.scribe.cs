using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class SeparatedKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite entire separation controls all translates.",
        H("Finite entire separation controls all translates"),
        Blocks(Describe.Lean(DescribeId.Create("entire-separated-translation-span"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/SeparatedKernel.finite_translation_space_of_separated_hankel"),
            H("Finite entire separation controls all translates"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("SeparatedLE(k,F) requires two families indexed by Fin k of entire complex functions whose pointwise product sum equals F at every complex pair. FiniteSeparated means such a natural k exists. Arbitrary entire factors are allowed; they are not assigned Hilbert vectors or polynomial coefficients.")),
                Paragraph(Text("The complete translation span of f is contained in the finite span of the first separated family whenever f(z+w) is finitely separated. This applies to every complex translate, rather than a finite set of samples. Finite dimension follows by inclusion into that actual finite factor span.")),
                Paragraph(Text("Addition, multiplication, scalar multiplication, polynomial evaluation, differentiation in either variable and linear changes of either variable preserve finite separation with the stated exact term bounds. These helpers are consumed by the weighted-kernel and physical-channel proofs. No matrix cutoff or growth hypothesis is imposed."))),
            DescribeRole.Theorem))));
}

