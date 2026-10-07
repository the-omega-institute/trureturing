using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualMixedLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual neutral and charged fields obey the order-one mixed locality law.",
        H("Actual Neutral-Charged Commutator"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Negative currents use the actual oscillator creator recurrence. Zero currents use the "
                + "change of charge from delta to alpha+delta. Positive currents use the proved derivative "
                + "of the creation exponential and finite convolution. These three branches give every "
                + "integer current index.")),
            Describe.Lean(
                DescribeId.Create("latticeactualmixedlocality-neutral-raw-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualMixedLocality.neutral_raw_commutator"),
                H("The actual all-integer raw commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("[h_i(m),rawCoeff(alpha,k)]=B(e_i,alpha) rawCoeff(alpha,k-m) as endomorphisms on the "
                        + "whole actual carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualmixedlocality-neutral-actual-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualMixedLocality.neutral_actual_commutator"),
                H("The actual normalized current-charge law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("At integer modes m,n, the coefficient commutator is B(e_i,alpha) "
                        + "(actualField(alpha))_(m+n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualmixedlocality-actual-neutral-charged-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualMixedLocality.actual_neutral_charged_locality"),
                H("Uniform mixed locality of order one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("One normalized delta kills the mixed commutator because the two shifted indices give the "
                        + "same m+n+1 field mode. No kernel or locality hypothesis is imposed."))),
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
