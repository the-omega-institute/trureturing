using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class CoinAveragesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/CoinAverages.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coin orbit is a plane rotation at interior eigenvalues and a one-dimensional phase at the endpoints.",
        H("Time averages of two Walsh blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orbit-rotation"),
                DeclarationHandle.Create(Prefix + "orbit_rotation"),
                H("Rotation of the initial coin"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("v"), Underscore, Grp(F.Id("a")), Open, F.Id("n"), Close, Sp, Eq, Sp, Operatorname, Grp(F.Id("cos")), Open, F.Id("n"), Theta, Close, Sp, F.Id("s"), Sp, Plus, Sp, Operatorname, Grp(F.Id("sin")), Open, F.Id("n"), Theta, Close, Sp, F.Id("e")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In character a, θ = arccos(ρ(a)), s is the unit vector with entries √p(y), and e is the signed coin vector with its component along s removed and divided by √(1 − ρ(a)²). When ρ(a) = ±1, the direction e is zero and the state is ρ(a)ⁿ s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tendsto-discretepair"),
                DeclarationHandle.Create(Prefix + "tendsto_discretePair"),
                H("The discrete-time pair mean"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("A"), Underscore, Grp(F.Id("T")), Open, F.Id("a"), Comma, F.Id("b"), Close, Sp, To, Sp, F.Id("D"), Open, F.Id("a"), Comma, F.Id("b"), Close))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Here A_T is the average coin inner product of the two orbits over n = 0, …, T−1. For unequal numerical eigenvalues the mean is zero. Equal endpoints contribute one. Equal interior eigenvalues r contribute half of 1 plus (ρ(a XOR b) − r²)/(1 − r²). The continuous-time phase mean is the indicator of equality of the two eigenvalues. The difference lies in [0,1], including the endpoint cases."))),
                DescribeRole.Theorem))));
}
