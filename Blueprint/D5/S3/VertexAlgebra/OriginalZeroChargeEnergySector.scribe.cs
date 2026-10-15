using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeEnergySectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full native ghost support and oscillator frequency determine the exceptional zero-energy labels.",
        H("Native Exceptional Energy Support"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-zero-energy-labels"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeEnergySector.zero_energy_labels"),
            H("Complete oscillator and ghost labels"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("D"), Comma, Sp, F.Id("d"), Comma, Sp, F.Id("S"), Comma, Sp,
                Call("oscillatorEnergy", F.Id("d")), Sp, Plus, Sp,
                Call("ghostEnergy", F.Id("S")), Sp, Eq, Sp, Num(0), Sp, Iff, Sp,
                Open, F.Id("d"), Sp, Eq, Sp, Num(0), Sp, Land, Sp,
                Call("GroundZeroSites", F.Id("S")), Close, Sp, Lor, Sp,
                Open, Exists, Sp, F.Id("i"), Sp, InMacro, Sp,
                Call("Fin", Call("rank", F.Id("D"))), Comma, Sp,
                F.Id("d"), Sp, Eq, Sp, Call("single", Call("unitFrequency", F.Id("i")), Num(1)),
                Sp, Land, Sp, Call("NegativeOneSites", F.Id("S")), Close))),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Ghost states are finitely supported functions on all finite subsets of the natural-number site set. Even site 2k is the creator b at mode -k-2, with energy k+2; odd site 2k+1 is the creator c at mode 1-k, with energy k-1. In particular site 1 has energy -1, site 3 is the c zero mode, and site 5 has energy 1.")),
            Paragraph(Text("Removing site 1 leaves only nonnegative site weights. Therefore every ghost subset has energy at least -1. A site above 5 has weight at least 2, so no such site can occur at nonpositive ghost energy. The six possible nonpositive subsets follow from this proved support bound, not from an imposed occupation cutoff.")),
            Paragraph(Text("GroundZeroSites means that S is empty, {3}, {1,5}, or {1,3,5}; NegativeOneSites means that S is {1} or {1,3}. The unitFrequency index is (i,0), whose native oscillator weight is one.")),
            Paragraph(Text("Oscillator frequencies are positive integers. At zero total energy their sum is either zero or one. In the first case the complete oscillator exponent is zero. In the second case exactly one axis at frequency one has occupation one. This argument uses no positivity of the lattice Gram matrix and includes rank zero.")))
        ))));
}
