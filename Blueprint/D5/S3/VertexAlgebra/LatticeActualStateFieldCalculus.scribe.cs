using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualStateFieldCalculusDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Borcherds and residue identities give mode commutators and normal state products.",
        H("Actual Mode Commutators and Normal State Products"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("Actual nonnegative state products truncate by the Hahn order before multiplication by "
                + "any binomial. Borcherds at r=0 then gives the complete mode commutator. The residue "
                + "iterate at -1 identifies the actual state product with the normal field product, after "
                + "computing (-1)^j choose(-1,j)=1.")),
            Describe.Lean(
                DescribeId.Create("latticeactualstatefieldcalculus-nonnegative-products-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.nonnegative_products_finite"),
                H("Inner actual states truncate first"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For arbitrary a,b, j to mu(a,j,b) has finite support. The proof uses the lower Hahn "
                        + "order of Y(a)b; no positive binomial upper bound is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualstatefieldcalculus-mode-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.mode_commutator"),
                H("Every integer mode commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("[a_p,b_q] is the finite sum over j>=0 of choose(p,j) (Y(mu(a,j,b)))_(p+q-j), for all "
                        + "integer p,q. The inner-state support controls the endomorphism sum, including negative "
                        + "p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualstatefieldcalculus-minus-one-product-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.minus_one_product_field"),
                H("Actual minus-one state product is a normal product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Y(mu(a,-1,b))=normalMinusOne(Y(a),Y(b)).operator. At mode q on c the complete two finite "
                        + "sums are sum_j a_(-j-1)(b_(q+j)c) and sum_j b_(q-j-1)(a_j c). The formula follows from "
                        + "the proved iterate and is not a definition or compatibility premise."))),
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
