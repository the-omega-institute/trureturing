using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class ActualLeechSectorCharactersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute graded traces and modular transformations of the four literal Leech sectors.",
        H("Actual Leech Sector Characters"),
        Blocks(
            Entry("lattice-sector-grade", "latticeSectorGrade", "Lattice parity grades",
                "The fixed and anti-fixed parts of a lattice Sugawara eigenspace are the literal lattice sector grades.",
                DescribeRole.Definition),
            Entry("twisted-sector-grade", "twistedSectorGrade", "Twisted parity grades",
                "At degree n the literal twisted stress eigenspace of weight 3/2 + n/2 is intersected with the selected oscillator-parity eigenspace.",
                DescribeRole.Definition),
            Entry("sector-term", "sectorTerm", "Normalized finite-grade trace",
                "Each term is the identity trace on the corresponding parity-projected grade times its energy exponential with vacuum shift c/24 = 1.",
                DescribeRole.Definition),
            Entry("sector-character", "sectorCharacter", "Ordered sector characters",
                "The four trace series are ordered as the fixed lattice sector, the anti-fixed lattice sector, the oscillator-odd twisted sector and the oscillator-even twisted sector.",
                DescribeRole.Definition),
            Entry("sector-trace-series", "sector_trace_series", "Absolute sums and the holonomy basis",
                "On the upper half-plane each literal graded trace series converges absolutely. The lattice pair is the half-sum and half-difference of the untwisted holonomy traces. The twisted pair is the half-sum and half-difference of the twisted holonomy traces with physical insertion equal to minus oscillator parity.",
                DescribeRole.Theorem),
            Entry("sector-s", "sectorS", "Sector S matrix",
                "The coefficient matrix is one half of the symmetric four by four sign matrix with rows ++++, ++--, +-+- and +--+.",
                DescribeRole.Definition),
            Entry("sector-t", "sectorT", "Sector T matrix",
                "The shifted T matrix is diagonal with entries 1, 1, 1 and -1.",
                DescribeRole.Definition),
            Entry("sector-character-s", "sectorCharacter_S", "S action on the literal characters",
                "Swapping the spatial and temporal holonomies yields the sector S matrix after the parity-trace identities are applied.",
                DescribeRole.Theorem),
            Entry("sector-character-t", "sectorCharacter_T", "T action on the literal characters",
                "Exchanging the twisted holonomy entries fixes their half-sum and reverses their half-difference. Both untwisted entries are fixed.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
