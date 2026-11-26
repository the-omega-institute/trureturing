using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiMixedQuotientFourierDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete Fourier coefficients on the mixed quotient of the Pascadi inverse graph.",
        H("Completion in the two digits"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-mixed-quotient-stationary-sum"),
                DeclarationHandle.Create(Module + "coefficient_eq_stationary_sum"),
                H("Exact stationary sum at arbitrary frequencies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let p be prime. Fix a unit C modulo p squared. The graph sends the unit x modulo p squared and the digit s modulo p to C/x modulo p squared and C*s/x squared modulo p. Its complete coefficient uses the two standard complex additive characters with frequencies A,B modulo p squared and D,E modulo p.")),
                    Paragraph(Text("Write x as the canonical lift of its unit residue a plus p*j with j modulo p. The inverse changes by minus p*j times the squared inverse of the canonical lift, since the square of p*j vanishes. Completing the s and j sums imposes D*a squared = -C*E and A*a squared = C*B modulo p. Each surviving summand is the phase at the canonical lift times p squared. The sum has at most p minus one terms, the size of the residue field unit group."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-mixed-quotient-mixed-sector"),
                DeclarationHandle.Create(Module + "coefficient_eq_zero_of_mixed"),
                H("Vanishing in the mixed sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If exactly one of A and B reduces to zero, the first residue equation has no unit solution, so the coefficient vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-mixed-quotient-unit-sector"),
                DeclarationHandle.Create(Module + "coefficient_unit_sector"),
                H("The unit-sector bound and support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If A and B have nonzero reductions, each eligible residue has the same square, so there are at most two of them. The triangle inequality gives the bound 2*p squared. A nonzero coefficient gives a common solution of the two residue equations and hence D/A = -E/B modulo p."))),
                DescribeRole.Theorem))));
}
