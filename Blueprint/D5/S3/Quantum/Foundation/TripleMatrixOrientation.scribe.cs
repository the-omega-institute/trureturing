using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class TripleMatrixOrientationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/TripleMatrixOrientation.";
    private static readonly LibraryNoteRef Note =
        LibraryNoteRef.Create("D5/L/QuantumStates/barnumhilgert2019spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive readbacks of two overlapping pairs force a common transpose orientation on one actual full Hermitian triple.",
        H("Whole-cone pair positivity and the common orientation"),
        Blocks(
            Law("external-tensor-form", "TensorNormalForm", "The normalized tensor form supplied to Lean",
                "Each actual preparation is supplied with one fixed output unitary and two fixed input transpose bits, with the identity valid on all Hermitian inputs. The external proof input is Jinli Xu, Baodong Zheng and Ajda Fošner, Linear maps preserving tensor products of rank-one Hermitian matrices, J. Aust. Math. Soc. 98 (2015), 407–428, Main Theorem p. 409, (1.1)–(1.2), with Proposition 2.1 pp. 410–411 for a single active factor. Equal dimensions remove zero padding, positivity fixes the sign, and trace normalization on spanning pure products makes the congruence unitary. Lean takes the resulting normalized identities for M and L as explicit hypotheses. https://doi.org/10.1017/S1446788714000603",
                DescribeRole.Definition),
            Law("nested-orientation", "triple_normal", "Compose the two actual preparation forms",
                "The inner bits are ε and δ and the outer bits are α and β. The transpose on the whole pair flips the first two local bits together, so the three bits in (32) are α xor ε, α xor δ and β.",
                DescribeRole.Theorem),
            Law("retained-pair-formula", "retained_pair_formula", "Identify each retained map on the entire triple",
                "The all-vector readback and real spanning of both preparations identify the actual linear pair map with the partial trace in permuted coordinates, the induced two-factor transpose mask, and conjugation back to the actual pair. This is the one-sector formula in (33).",
                DescribeRole.Theorem),
            Law("partial-trace-onto-psd", "traceLast_psd_surjective", "The partial trace reaches the entire retained PSD cone",
                "Tensor an arbitrary retained PSD matrix with a positive trace-one spectator. The retained input can be entangled.",
                DescribeRole.Theorem),
            Law("mixed-mask-obstruction", "pairMaskH_bits", "Whole-cone positivity rules out a mixed transpose",
                "For n at least two, the repository Bell compression supplies a PSD witness whose one-sided partial transpose fails positivity. Full transposition relates the two mixed masks.",
                DescribeRole.Theorem),
            Law("common-orientation", "align_bits", "The three pair parities force the same triple bit",
                "The fixed carriers are H(n), H(n times n) and H((n times n) times n), with the same actual M in both overlapping pair readbacks. The given p13 and p23 must take every PSD matrix on the actual triple to a PSD matrix on the actual pair. With the two normalized forms and both spans, their readbacks give the first two edges of (34). The preparation gives the inner edge. Since the three edges share ε xor δ, this bit is zero and the three triple bits coincide for n at least two.",
                DescribeRole.Theorem))));

    private static DocumentBlock Law(string id, string selector, string title, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
            Blocks(Paragraph(Text(explanation))), role);
}
