using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class FiniteLabelRecordDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/FiniteLabelRecordDilation.";

    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");
    private static readonly LibraryNoteRef KoashiImoto =
        LibraryNoteRef.Create("D5/L/QuantumChannels/koashiimoto2002nondisturbance");
    private static readonly LibraryNoteRef JencovaPetz =
        LibraryNoteRef.Create("D5/L/Divergence/jencovapetz2006sufficiency");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite memory and pure-environment dimensions for perfect label records.",
        H("Perfect label records with a finite pure environment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("perfect-label-record-iff"),
                DeclarationHandle.Create(Prefix + "perfectLabelRecord_iff"),
                H("Sharp joint dimension criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(Kato, KoashiImoto, JencovaPetz),
                Blocks(
                    Paragraph(Text(
                        "Let B be a finite input basis, P a subset of supported coordinates, and l a "
                        + "map from P to a finite label type J. In a diagonal experiment P consists "
                        + "of the positive-reference coordinates. The class size n_j counts the b in P with l(b) = j. "
                        + "The encoder is a complex matrix V "
                        + "from B to Fin d times Fin e with adjoint times itself equal to the identity. "
                        + "Here d is the memory dimension and e is the dimension of the pure "
                        + "Stinespring ancilla. The dimensions are static Hilbert-space counts.")),
                    Paragraph(Text(
                        "The predicate requires one POVM on the memory whose effects are positive "
                        + "semidefinite and sum to the identity. For each b in P the effect for l(b) "
                        + "has trace pairing one with the partial trace of the outer product of "
                        + "the column at b. The partial trace sums the outer products of that column's "
                        + "environment slices. The POVM includes a spare outcome, so an empty support "
                        + "can be handled even when J is empty.")),
                    Paragraph(Text(
                        "For each class j, the miss probability is a sum of nonnegative slice terms. "
                        + "Each term vanishes, putting every slice in the one-eigenspace of the "
                        + "effect for j. Those eigenspaces are mutually orthogonal. Linear independence "
                        + "of the isometric columns bounds each class size by e times the eigenspace "
                        + "dimension. The sum of these dimensions is at most d.")),
                    Paragraph(Text(
                        "For the converse, allocate ceil(n_j/e) disjoint memory coordinates to "
                        + "class j and inject its n_j input coordinates into the product of that block "
                        + "and the environment. Extend the injection to the rest of B using the free "
                        + "joint coordinates. The resulting basis-column matrix is an isometry and "
                        + "diagonal block projectors give the perfect measurement.")),
                    Paragraph(Text(
                        "With two labels of sizes three and one and d = e = 2, the input fits into "
                        + "four joint dimensions and there are two labels. The rounded block sizes "
                        + "are two and one, so three memory dimensions are necessary.")),
                    Paragraph(Text(
                        "Kato Section VI.A gives the unrestricted dimension for exact classical "
                        + "local compression. Koashi and Imoto Theorem 3 describes operations fixing "
                        + "a family of states and Theorem 4 gives the product decomposition for "
                        + "independent choices. Jencova and Petz Section 4, Theorem 5 and Corollary 1 "
                        + "describe sufficient channels through block structure. The finite theorem "
                        + "here applies to perfect reading of a specified basis label."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("B"), d = F.Id("d"), e = F.Id("e"), j = F.Id("j");
        Formula labels = F.Id("J"), label = F.Id("l");
        Formula fiberSize = Seq(F.Id("n"), Underscore, Grp(j));
        Formula rounded = Call("ceil", Seq(fiberSize, Slash, e));
        Formula slots = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, labels), Sp, rounded);
        return Disp(new Formula.Aligned([
            Seq(D(0), Sp, Lt, Sp, e, Sp, Rightarrow),
            Seq(Call("HasPerfectLabelRecord", label, d, e), Sp, Iff, Sp,
                Open, Call("card", b), Sp, Leq, Sp, d, Sp, Cdot, Sp, e,
                Sp, Land, Sp, slots, Sp, Leq, Sp, d, Close),
        ]));
    }
}
