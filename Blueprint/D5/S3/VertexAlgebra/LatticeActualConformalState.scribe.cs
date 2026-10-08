using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualConformalStateDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary matrix quadratic state has precisely the actual Sugawara field.",
        H("The Actual Arbitrary-Matrix Quadratic State"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Let H be any complex rank-by-rank matrix, with no inverse, symmetry or positivity "
                + "premise. Define omega as single(0,(1/2) sum_i,j H_ij X(i,0)X(j,0)). Define L_m to be "
                + "sugawaraMode(D,H,m), namely the coefficient m+1 of the actual Sugawara field. This "
                + "convention is used in every state law.")),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalstate-quadratic-state-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalState.quadratic_state_field"),
                H("The genuine quadratic state evaluates to the normal current product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all i,j, Y(single(0,X(i,0)X(j,0))) equals "
                        + "normalMinusOne(neutralField(i),neutralField(j)).operator. The actual current state, its "
                        + "minus-one product, and proved normal state-product compatibility give the result "
                        + "independently of occurrence order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualconformalstate-y-omega"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualConformalState.Y_omega"),
                H("The field of the actual omega is the Sugawara field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Y(omega(D,H))=sugawaraField(D,H) for arbitrary H. Finite double-sum linearity and the "
                        + "actual quadratic identity prove this equality."))),
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
            Paragraph(Text("The consumed Sugawara normal-ordering and commutator architecture retains Kalle Kytola, "
                + "VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4, Apache-2.0 "
                + "attribution. The actual carrier and matrix contractions are explicit. The complete "
                + "Virasoro theorem is a separately delivered supplier; these state laws do not replace it "
                + "with a partial proof.")),
            Paragraph(Text("The carrier and formal-series interfaces use pinned Mathlib revision "
                + "db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.")),
            Paragraph(Text("This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, "
                + "PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, "
                + "string theory, AdS/CFT and physical completion are not proved here.")))));
}
