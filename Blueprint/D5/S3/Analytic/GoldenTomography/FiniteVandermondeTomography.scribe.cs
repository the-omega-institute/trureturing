using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FiniteVandermondeTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct finite phase nodes make a matching finite moment window "
            + "faithful.",
        H("Finite Vandermonde Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-moment-readout-injective"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography.finite_moment_readout_injective"),
                H("Distinct nodes give faithful finite moments"),
                StatementSource.FromAuthor(InjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family of pairwise distinct nodes over a field, the first matching number of power moments uniquely determines the hidden amplitude vector.")),
                    Paragraph(Text(
                        "The proof reuses Mathlib's Vandermonde determinant and determinant-kernel machinery. It asserts exact finite injectivity and leaves conditioning and infinite reconstruction outside its scope."))),
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

    private static Formula InjectivityFormula() => Disp(Seq(
        Forall, Sp, F.Id("v"), Comma, Sp,
        Call("Injective", F.Id("v")), Sp, Rightarrow, Sp,
        Call("Injective", Call("finiteMomentReadout", F.Id("v"))), Dot));

}
