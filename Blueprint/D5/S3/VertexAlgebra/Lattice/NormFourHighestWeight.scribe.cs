using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourHighestWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual norm-four lattice Virasoro modes restrict highest weights to 0, 1/16 and 1/2.",
        H("Highest Weights from the Actual Vacuum Null State"),
        Blocks(
            Paragraph(Text("Let D have an integral symmetric Gram matrix with even diagonal, and let a be a charge "
                + "with B(a,a)=4. For s in C with s squared equal to one, let v be the production norm-four "
                + "lattice state and put L_m=Y(v)_(m+1) on the actual finite-support lattice carrier.")),
            Describe.Lean(
                DescribeId.Create("normfourhighestweight-highest-weight-values"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourHighestWeight.highest_weight_values"),
                H("Allowed highest weights in the actual carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such D,a,s, every complex h and every nonzero actual state w, "
                    + "if L_0 w=h w and L_m w=0 for every positive integer m, then "
                    + "h=0 or h=1/16 or h=1/2. No positivity, rootlessness, rank, determinant, simplicity "
                    + "or diagonalization assumption is required."))),
                DescribeRole.Theorem),
            Paragraph(Text("The state-field iterate identity is summed over all nonnegative offsets. "
                + "Above the descendant's degree, the left sum vanishes by the shorter descendant's "
                + "annihilation bound. Every right offset at least two vanishes by the positive-mode "
                + "hypothesis on w, leaving exactly offsets zero and one. This proves annihilation "
                + "for all higher modes and the top-coefficient recurrence together.")),
            Paragraph(Text("The identity L_(-1)=T is proved only on the vacuum and its consumed Virasoro "
                + "descendants, by comparing the Virasoro and actual translation commutators. "
                + "It is not imposed on w. The actual mode commutator and derivative-state identity "
                + "then give the top coefficient of L_(-k)u as "
                + "(-1)^k(d+(k-1)h)c w when u has degree d and top coefficient c w.")),
            Paragraph(Text("At the literal field coefficient five, the four level-six descendants "
                + "L_(-2)^3 vacuum, L_(-3)^2 vacuum, L_(-4)L_(-2)vacuum and L_(-6)vacuum "
                + "act on w by h(h+2)(h+4), 2h(2h+3), h(3h+2) and 5h respectively. "
                + "Applying this coefficient to the actual null relation with coefficients "
                + "64,93,-264,-108 gives 64h(h-1/16)(h-1/2)w=0. Nonvanishing of w "
                + "and the field property of C give the three asserted values.")),
            Paragraph(Text("The norm-four state and its attribution are those of NormFourVirasoroVector: "
                + "Shimakura, arXiv:1202.6107, equation (1.3), citing Dong-Mason-Zhu, Theorem 6.3. "
                + "The actual lattice-field construction follows Bakalov-Kac, arXiv:math/0402315, "
                + "section 4.1. Imported residue and derivative calculus retain their Carnahan and "
                + "Matsuo-Nagatomo attribution. This theorem supplies a necessary restriction on "
                + "actual highest-weight states; it does not assert existence of each weight or "
                + "classification of representations.")))));
}
