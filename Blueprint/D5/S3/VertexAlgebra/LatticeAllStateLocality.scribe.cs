using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeAllStateLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivative, Dong and finite-sum locality give every actual state field and its integer residues.",
        H("All Actual State Locality and Integer Residues"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Consumed finite locality calculus proves symmetry, monotonicity of order, scalar and "
                + "finite-sum transport, derivative locality and Dong normal-product locality. The actual "
                + "charged, mixed and neutral orders start the induction on arbitrary nested words. Finite "
                + "charge and monomial supports then give an order for every pair of states, independent of "
                + "the tested input vector.")),
            Paragraph(Text("Residue reconstruction consumes this proved actual locality, creativity, creation and "
                + "covariance under the same actual T. Relative creative vacuum uniqueness identifies each "
                + "integer residue with the existing Y; membership in its image and the desired iterate are "
                + "not hypotheses.")),
            Describe.Lean(
                DescribeId.Create("latticeallstatelocality-neutral-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateLocality.actual_neutral_neutral_locality"),
                H("Uniform actual neutral locality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The released all-sector Heisenberg commutator gives order-two locality "
                    + "for every pair of neutral fields, on every charge and oscillator polynomial. "
                    + "No positivity or inverse Gram matrix is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatelocality-word-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateLocality.word_locality"),
                H("Every two actual word fields are local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges and finite occurrence words, a finite uniform order kills the "
                        + "coefficient commutator. Each derivative and nested normal product is handled by the "
                        + "consumed locality theorems."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatelocality-statefield-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateLocality.stateField_locality"),
                H("Every two actual state fields are local"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For arbitrary a,b in V there exists a natural N with delta^N([Y(a),Y(b)])=0 as an "
                        + "endomorphism distribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatelocality-residue-closure"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateLocality.residue_closure"),
                H("The same actual Y is closed under all integer residues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every integer r, Y(mu(a,r,b)) equals the actual residueField(r,a,b).operator. Both "
                        + "positive residue cancellation and negative divided-derivative normal products are "
                        + "consumed from the existing generic supplier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatelocality-statefield-iterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateLocality.stateField_iterate"),
                H("Complete finite integer iterate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all a,b,c and integer r,n, both sequences (-1)^j choose(r,j) a_(r-j)(b_(n+j)c) and "
                        + "(-1)^j choose(r,j) b_(r+n-j)(a_j c) have finite support. (mu(a,r,b))_n c is the first "
                        + "sum minus (-1)^r times the second. The negative integer sign and both kernel branches "
                        + "are retained."))),
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
