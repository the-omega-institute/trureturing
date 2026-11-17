using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseHierarchyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full Parrilo hierarchy and actual Bose extensions", H("The full Parrilo hierarchy and actual Bose extensions"), Blocks(
            Paragraph(Text("The complete-graph characterization is prior Gulati-Nechita-Park Theorem 8.16. The star, companion and unnormalized optimization applications are from the note by Haobo Ma then Wenlin Zhang. No priority certification is asserted. The proofs use the full native sum-of-squares hierarchy at every level, including zero and singular matrices.")),
            Describe.Lean(DescribeId.Create("bosehierarchy-parrilo-polar"),
                DeclarationHandle.Create(Prefix + "parriloPolar"),
                H("The positive polar of the actual all-level SOS cone"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("The positive polar consists of P whose ordinary real matrix pairing with every M in ParriloHierarchy.K at level k is nonnegative. That canonical K uses the unrestricted native sum-of-squares predicate for (sum of x_i squared)^k times sum M_ij x_i squared x_j squared."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosehierarchy-gnp-characterization"),
                DeclarationHandle.Create(Prefix + "gnp_characterization"),
                H("The complete-graph characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/gnp2025dickeextensions")),
                Blocks(Paragraph(Text("For every register count r with two distinct selected sites and every real symmetric P, the actual LDUI(P,P) operator has a fully PPT full-Bose extension exactly when P belongs to the positive polar of K_n^(r-2). The proof uses actual tensor trace duality, diagonal twirling of dual witnesses, native homogeneous SOS cut certificates, DPS closedness and finite-dimensional bipolarity. It assumes no GNP theorem or additional axiom.")),
                    Paragraph(Text("Normalized two-particle Dicke weights satisfy P_ii=Y_ii and P_ij=Y_ij/2. The same-individual-matrix theorem identifies these complete witnesses with star witnesses. Root partial transposition bijects fully PPT star witnesses for LDUI and its CLDUI companion, permuting all cuts by symmetric difference with the root. Full Bose support is asserted for the inverse-transposed companion witness.")),
                    Paragraph(Text("Ordinary and adapted DPS use one root and t Bose-supported leaves, with r=t+1. Leaf permutations reduce their cuts to the paper's prefix conventions; full transposition supplies complementary cuts. The resulting comparison is adapted DPS = ordinary DPS intersect PSD of the two-particle symmetric subspace. The separate closed dual-sum theorem retains its closure. GNP Questions 8.7 and 8.21, general non-Bose graph extendibility, non-Bose CLDUI complete-graph comparisons, and unrestricted exact witness lifting remain outside these statements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosehierarchy-objective-values"),
                DeclarationHandle.Create(Prefix + "objectiveValues"),
                H("The actual unnormalized feasible objective set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Attainable values are the real matrix pairings with symmetric P for which the actual LDUI operator has an ordinary DPS witness. No trace constraint is added."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosehierarchy-objective-minimum"),
                DeclarationHandle.Create(Prefix + "objective_minimum"),
                H("Attained unnormalized optimum zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every dimension n, every r with two distinct sites and every objective C in K_n^(r-2), the actual unnormalized ordinary DPS program on LDUI(P,P) has least objective value zero. Feasibility and the complete hierarchy characterization force every pairing to be nonnegative, and P=0 is feasible. In particular n=5,r=3 gives precisely the t=2 Britz-Laurent program. A trace-one or otherwise normalized program is not covered."))), DescribeRole.Theorem))));
}
