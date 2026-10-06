using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualCurrentAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual neutral modes satisfy the Heisenberg commutator and uniform order-two locality.",
        H("Actual Neutral Current Algebra and Locality"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("On single(delta,p), negative current modes multiply by oscillator variables, the zero "
                + "mode is B(e_i,delta), and positive mode m is m times the Gram-weighted partial "
                + "derivative at frequency m-1. Partial derivatives commute. Their mixed multiplication "
                + "commutator supplies the central term, on every charge sector.")),
            Describe.Lean(
                DescribeId.Create("latticeactualcurrentalgebra-neutral-heisenberg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.neutral_heisenberg"),
                H("All-sector actual Heisenberg commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all i,j and integer m,n, [h_i(m),h_j(n)]=m G_ij delta(m+n,0) id. The proof covers "
                        + "both mixed sign branches, the zero charge scalars, and equal-sign commutation; it uses "
                        + "no inverse matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualcurrentalgebra-actual-neutral-neutral-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra.actual_neutral_neutral_locality"),
                H("Uniform neutral locality of order two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every i,j, delta iterated twice kills the coefficient commutator of the actual "
                        + "neutral fields. The Heisenberg formula at the three shifted index pairs has equal "
                        + "central support and cancelling scalar coefficients."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
