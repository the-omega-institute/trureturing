using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanLaurentEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic periodizer bridge for finite-alphabet lattice configurations.",
        H("KhetanLaurentElimination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clear-laurent-bezout"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout"),
                H("Clear a Laurent Bezout identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fraction-field Laurent Bezout identity is multiplied by nonzero common denominators. The resulting constant is proved nonzero in the coefficient domain, with both multipliers in the original Laurent ring. Localized coprimality is an explicit intermediate premise; its derivation from the line-factor restriction is not established here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clear-laurent-bezout-of-monic-factors"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanLaurentElimination.clear_laurent_bezout_of_monic_factors"),
                H("Produce the identity from monic transverse factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For monic factors, divisibility in the coefficient fraction field descends by polynomial division. Multiplication by a Laurent monomial only changes the dividend by a unit. If each mapped factor is irreducible and its Laurent image does not divide P, polynomial Bezout identities give coprimality with their product and with B. Clearing denominators then gives a nonzero coefficient in the original domain. Identifying these factors with the transverse lattice binomials is a separate obligation."))),
                DescribeRole.Theorem))));
}
