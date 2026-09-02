using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class SymmetricConvergentOfZetaSummableDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable."
            + "symmetricConvergent_of_zeroData";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every supplied enumeration of the nontrivial zeta zeros is symmetrically convergent "
            + "for every Weil test function.",
        H("Symmetric Convergence from Frozen Zeta Summability"),
        Blocks(Describe.Lean(
            DescribeId.Create("symmetric-convergence-from-frozen-zeta-summability"),
            DeclarationHandle.Create(Declaration),
            H("Every ZeroData is symmetrically convergent for every Weil test function"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen Zeta23.WeilEF result supplies absolute summability of the "
                        + "multiplicity-weighted zero terms using Riemann-von Mangoldt counts "
                        + "and Fourier-Laplace decay.")),
                Paragraph(Text(
                    "The frozen zero equivalence transports that sum to any supplied ZeroData "
                        + "enumeration. Cofinality of the symmetric index sets then identifies "
                        + "the limit of the finite symmetric cutoffs.")),
                Paragraph(Text(
                    "This moderate extraction makes the hZero premise of O-6 derivable without "
                        + "changing the statement of O-6."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("g");

        return Disp(Seq(
            Forall, Sp, zeros, Colon, Sp,
            Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            Forall, Sp, test, Colon, Sp,
            Operatorname, Grp(F.Id("WeilTestFunction")), Comma, Sp,
            Call("SymmetricConvergent", zeros, test)));
    }
}
