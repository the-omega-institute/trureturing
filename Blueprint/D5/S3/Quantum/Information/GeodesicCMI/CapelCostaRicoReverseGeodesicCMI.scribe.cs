using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoReverseGeodesicCMIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful diagonal three-qubit states with all pair marginals fixed can produce an unbounded reverse geodesic CMI gap at vanishing trace distance.",
        H("Reverse geodesic CMI on a fixed marginal fiber"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-geodesicrelativeentropy-diagonal"),
                DeclarationHandle.Create(Prefix + "geodesicRelativeEntropy_diagonal"),
                H("Classical relative entropy on faithful diagonals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For positive diagonal entries r and s, the modular eigenvalue at E_ij is r_i^(1−t) r_j^t / s_j. The reference vector contributes squared weight s_i at E_ii and vanishes on the other matrix units. This yields the classical relative entropy in equation (62)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-reversecmi"),
                DeclarationHandle.Create(Prefix + "reverseCMI"),
                H("Reverse geodesic conditional mutual information"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (357) orders the joint divergence from the AB marginal tensored with the faithful C reference to the joint state. The subtracted divergence runs from the B marginal tensored with that reference to the BC marginal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-family-fixed-marginals"),
                DeclarationHandle.Create(Prefix + "family_fixed_marginals"),
                H("All three pair marginals are fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Starting from the weights 0, 3/16, 1/8 and 1/16 indexed by Hamming weight, add x times the parity sign for 0 < x < 1/16. Every one-factor partial trace cancels the perturbation and leaves the same faithful diagonal pair marginal (3,5,5,3)/16."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-family-tracedistance"),
                DeclarationHandle.Create(Prefix + "family_traceDistance"),
                H("Exact trace distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the states with parameters x and x squared, the half trace norm of the difference is 4(x−x²)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-family-gap-tendsto-attop"),
                DeclarationHandle.Create(Prefix + "family_gap_tendsto_atTop"),
                H("Divergence of the signed reverse gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Subtract the value at x from the value at x squared. The reduced term cancels. The joint term at 000 is (3/16) times the C reference weight at zero times log(1/x). The other joint terms tend to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-geodesic-cmi-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("No modulus on the faithful diagonal fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The distance tends to zero from above and the signed gap tends to positive infinity, so no right-zero trace-distance modulus governs the faithful diagonal fiber. For the dimension-only question itself, equations (381)–(384) already give a binary obstruction with B trivial, and a fixed independent B can be adjoined by the tensor rule. The parity family above supplies a correlated three-qubit fiber with all three pair marginals fixed."))),
                DescribeRole.Theorem)),
        []));
}
