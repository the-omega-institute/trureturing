using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualVertexAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual lattice state-field construction is an ungraded vertex algebra.",
        H("The Actual Ungraded Lattice Vertex Algebra"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("StateFieldVertexAlgebra records a linear state-field map, vacuum, translation, vacuum "
                + "field, creation, creativity, translation vacuum, covariance, locality and full integer "
                + "Borcherds with all three finite supports. actualVertexAlgebra(D) fills this record with "
                + "the actual Y, single(0,1), charge-sensitive T and the proved concrete axioms for every "
                + "ordinary D. This constructor imposes no desired algebra laws as additional premises.")),
            Describe.Lean(
                DescribeId.Create("latticeactualvertexalgebra-translation-as-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualVertexAlgebra.translation_as_mode"),
                H("Concrete translation is intrinsic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every a, T(a)=(Y(a))_(-2) vacuum. Evaluate the proved mode -1 covariance on vacuum, "
                        + "use creation and T(vacuum)=0, and obtain the actual minus-two mode. The record and "
                        + "constructor remain ungraded."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue "
                + "locality and reconstruction by creative local fields, divided derivatives and nested "
                + "normal products.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
