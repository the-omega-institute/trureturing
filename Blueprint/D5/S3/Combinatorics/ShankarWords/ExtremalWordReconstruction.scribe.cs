using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ShankarWords;

internal sealed class ExtremalWordReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reconstruct arbitrary actual extremal words as existing even or odd constructors.",
        H("Actual extremal-word reconstruction"),
        Blocks(Describe.Lean(DescribeId.Create("shankar-extremal-word-reconstruction"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction.extremal_word_reconstruction"),
            H("Literal reconstruction from the original word conditions"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Words/shankar2026canon")),
            Blocks(Paragraph(Text(
                "For every k at least two and every literal word w in actualWords(k), "
                + "the hypothesis descents(w)=extremalValue(k) forces one of the stated "
                + "reconstruction forms. The even case is exactly evenWord(t), with "
                + "k=2t and t at least one. In the odd case k=2t+1, the word is "
                + "exactly oddWord(t,i) for an index i in OddIndex(t). The theorem "
                + "retains the original length, bounded alphabet, three equal letter "
                + "counts, every lattice prefix inequality and full 321 subsequence "
                + "avoidance through membership in actualWords. No candidate "
                + "membership, ordered tiling or restricted cut is assumed. A "
                + "proof-local recursion packs the actual adjacent descents into "
                + "disjoint two-letter tiles. Saturation leaves zero or one interior "
                + "singleton. Avoidance orders the actual tiles into 21,31,32 blocks, "
                + "and letter counts fix their multiplicities. For singleton two, "
                + "two lattice prefix inequalities and a crossing 321 triple force "
                + "the cut j=t or j=2t. For singleton three, avoidance gives "
                + "t+1<=j<=3t; reversing and complementing the literal base identifies "
                + "the odd index with q=3t-j. This proves the inverse relation to "
                + "the existing even and odd construction theorems. It does not "
                + "establish a separately stated universal upper bound or top-fiber "
                + "cardinality, coefficient log-concavity, unimodality or Conjecture 9.3. "
                + "All auxiliary mathematical facts remain inside the live proof.")))))));
}
