using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineWernerHolevoDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuantumChannels/girard2022mixedunitaryrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric Werner–Holevo channel attains its Choi rank in each dimension 9 to a power at least two.",
        H("Symmetric Werner–Holevo rank from affine lines"),
        Blocks(
            Describe.Lean(DescribeId.Create("mixed-unitary-rank-power-nine"),
                DeclarationHandle.Create(Module + ".mixedUnitaryRank_power_nine"),
                H("Minimal rank in powers of nine"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(
                        DefinitionDsl.Text(
                            "For every natural exponent d at least two, there exists a completely positive trace-preserving "
                            + "map of type "),
                        Ref("D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel"),
                        DefinitionDsl.Text(
                            " on n by n matrices with the displayed action on every complex matrix. "
                            + "Its mixed-unitary rank is the least length of a finite decomposition into unitary "
                            + "conjugations with nonnegative real weights summing to one. "
                            + "The least length is 3321 in dimension 81.")),
                    Paragraph(DefinitionDsl.Text(
                        "Each direction partitions the affine space into lines of size nine. A flat hollow symmetric "
                        + "unitary acts on each line. The nine-block edge labeling extends to the larger parallel "
                        + "classes. Additive characters turn the distinct endpoint sums into an orthogonal hollow "
                        + "family in each direction. Together with the diagonal characters these matrices form a "
                        + "Hilbert–Schmidt orthogonal basis of the entire complex symmetric matrix subspace.")),
                    Paragraph(DefinitionDsl.Text(
                        "The basis gives a uniform unitary-conjugation mixture with weights 2/(n(n+1)). "
                        + "The Choi range under vectorization is the entire complex symmetric matrix subspace, "
                        + "of dimension n(n+1)/2. A unitary conjugation has a rank-one Choi matrix, so no shorter "
                        + "finite decomposition can have this range. The all-dimension conjecture remains open."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = F.Id("n");
        var x = F.Id("X");
        var d = F.Id("d");
        var phi = new Formula.Power(Phi, Plus);
        var matrices = new Formula.Subscript(F.Id("M"), n);
        var trace = Call("tr", x);
        return new Formula.Aligned([
            Seq(n, Amp, Eq, new Formula.Power(D(9), d), Comma, Quad, Sp,
                d, InMacro, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp, d, Geq, D(2)),
            Seq(phi, Open, x, Close, Amp, Eq,
                new Formula.Fraction(Seq(trace, F.Id("I"), Plus, new Formula.Power(x, F.Id("T"))),
                    Seq(n, Plus, D(1))),
                Comma, Quad, Forall, Sp, x, Sp, InMacro, Sp, matrices, Open, Mathbb, Grp(F.Id("C")), Close),
            Seq(Call("murank", phi), Amp, Eq,
                new Formula.Fraction(Seq(n, Open, n, Plus, D(1), Close), D(2))),
        ]);
    }
}
