using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualStateDerivativeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual translation of every state differentiates its field at every integer mode.",
        H("Unconditional Actual State Differentiation"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Apply the genuine residue iterate at -2 with the second state equal to the actual "
                + "vacuum. The weight (-1)^j choose(-2,j)=j+1 and the identity field supported only at mode "
                + "-1 reduce the two finite branches. Negative, zero and positive q are handled separately. "
                + "Intrinsic translation identifies the left state with T(a). No conformal matrix or "
                + "inverse is needed.")),
            Describe.Lean(
                DescribeId.Create("latticeactualstatederivative-state-derivative-modes"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualStateDerivative.state_derivative_modes"),
                H("Every integer coefficient of the derivative state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every actual a and integer q, (Y(T(a)))_q=-q (Y(a))_(q-1). The theorem includes "
                        + "arbitrary nonhomogeneous sums and degenerate lattices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualstatederivative-state-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualStateDerivative.state_derivative"),
                H("The actual field of T(a) is its divided derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every actual a, Y(T(a))=dividedDerivative(1,Y(a)). The divided derivative "
                        + "coefficient formula and the preceding all-integer mode theorem identify the genuine "
                        + "lower-truncated fields."))),
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
