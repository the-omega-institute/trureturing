using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LeechPeirceMultiplicitiesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ordinary Golay Leech axis has the full fixed energy-two Peirce multiplicities.",
        H("Ordinary Leech Peirce Multiplicities"),
        Blocks(
            Paragraph(Text("Use the actual admissible Golay integer construction, with real pairing "
                + "equal to the raw dot product divided by eight. Its coordinate equivalence pulls "
                + "the raw vector (4,4,0^22) back to a norm-four charge a in an even unimodular "
                + "positive definite lattice D of rank twenty-four. Let S be the intersection of "
                + "the actual theta fixedSpace with the eigenvalue-two space of the canonical "
                + "inverse-Gram Sugawara zero mode. The operator is the actual zero mode "
                + "L=NormFourVirasoroVector.mode(D,a,1,0).")),
            Describe.Lean(
                DescribeId.Create("actual-leech-peirce-multiplicities"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LeechPeirceMultiplicities.actual_leech_peirce_multiplicities"),
                H("The actual invariant restriction, trace and complete decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The mode preserves all of S. Its restricted full-basis trace "
                    + "is 8215/2. The literal ambient intersections of S with its eigenspaces at "
                    + "0, 1/16, 1/2 and 2 form an independent family whose sum is S, and have "
                    + "dimensions 49152, 47104, 2323 and 1 respectively. Rank, unimodularity, "
                    + "positive definiteness, the full real pairing, rootlessness and the exact "
                    + "raw-axis identity remain in the conclusion. The numbers, trace and "
                    + "decomposition are conclusions of the constructed example."))),
                DescribeRole.Theorem),
            Paragraph(Text("The complete ordinary basis consists of symmetric oscillator pairs "
                + "and sign-orbits of all norm-four charges. The actual quadratic and charged "
                + "mode identities prove invariance on every basis vector. On a neutral pair "
                + "(i,j), the diagonal coefficient is (a_i g_i+a_j g_j)/8, including repeated "
                + "colours. Summing unordered pairs counts each colour rank plus one times; "
                + "the charge contraction is four. Thus the neutral trace is 25/2. On a charged "
                + "orbit the diagonal coefficient is B(a,b)^2/16. The reflection partners at "
                + "pairing plus or minus two lie in distinct sign-orbits. The entire unbounded "
                + "Golay shell distribution, transported by the coordinate-compatible shell "
                + "equivalence, gives charged trace 1+4600/4+47104/16=4095.")),
            Paragraph(Text("The actual quartic L(L-1/16)(L-1/2)(L-2)=0 gives four cubic "
                + "Lagrange projections. Multiplication by L minus the corresponding eigenvalue "
                + "annihilates each projection; each projection fixes that literal eigenspace. "
                + "Their sum is the identity and their eigenvalue-weighted sum is L. Projection "
                + "traces therefore equal eigenspace dimensions. The complete one-sixteenth "
                + "dimension is 47104, and the complete two-eigenline is the span of the "
                + "nonzero actual norm-four vector. With total dimension 98580 and trace "
                + "8215/2, the remaining dimensions are 2323 and 49152.")),
            Paragraph(Text("The lattice vertex construction follows Bakalov-Kac and "
                + "Frenkel-Lepowsky-Meurman. The norm-four Ising formula is due to "
                + "Dong-Mason-Zhu, Theorem 6.3, as recalled by Shimakura, arXiv:1202.6107, "
                + "formula (1.3). The result concerns the ordinary untwisted fixed energy-two "
                + "space. It asserts no orbifold extension, Monster representation, fusion "
                + "completion or string-theoretic realization.")))));
}
