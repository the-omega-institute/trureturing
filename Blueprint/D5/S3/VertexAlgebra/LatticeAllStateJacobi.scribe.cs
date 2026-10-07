using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeAllStateJacobiDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual fields satisfy the full integer Borcherds identity with three finite supports.",
        H("Full Integer Borcherds on the Actual Lattice"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Define the left kernel as choose(p,j) mu(mu(a,r+j,b),p+q-j,c). The two right kernels use "
                + "(-1)^j choose(r,j) mu(a,p+r-j,mu(b,q+j,c)) and its (-1)^r weighted reverse "
                + "mu(b,q+r-j,mu(a,p+j,c)). Actual Hahn truncation separately bounds all three supports.")),
            Paragraph(Text("Integer residue closure gives the p=0 iterate seed. Actual locality gives the high-r "
                + "zero region. Supported Pascal reindexing proves the discrepancy recurrence at (p+1,q,r), "
                + "(p,q+1,r) and (p,q,r+1). Positive p induction and nested induction on negative p and "
                + "distance below the locality boundary give every integer triple.")),
            Describe.Lean(
                DescribeId.Create("latticeallstatejacobi-borcherds"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateJacobi.borcherds"),
                H("All states and all three integer indices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every a,b,c in V and integers p,q,r all three kernels have finite support, and the "
                        + "left sum equals the signed difference of the two right composition sums. There is no "
                        + "Jacobi, support, expansion or locality premise: the concrete construction supplies every "
                        + "one of those obligations."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI "
                + "10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and "
                + "conformal construction. Equation numbers refer to arXiv v1.")),
            Paragraph(Text("Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, supplies residue "
                + "locality and reconstruction by creative local fields, divided derivatives and nested "
                + "normal products.")),
            Paragraph(Text("Finite normal-product and integer residue kernels retain Scott Carnahan attribution: "
                + "vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, "
                + "VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. Actual coefficient proofs are "
                + "re-elaborated on V; no polynomial Fock theorem is transferred between carriers.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
