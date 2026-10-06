using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualGeneratorLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual lattice cocycle and creation coefficients obey the signed contraction laws.",
        H("Actual Cocycle and Creation Contraction"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("The lower triangular Gram matrix plus the half diagonal defines the integral cocycle "
                + "exponent. Adding its transpose gives G; even diagonal makes every self-pairing even. "
                + "Polynomial translation of the actual exponential coefficients gives the signed "
                + "integer-binomial contraction.")),
            Describe.Lean(
                DescribeId.Create("latticeactualgeneratorlocality-epsilon-skew"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualGeneratorLocality.epsilon_skew"),
                H("The actual cocycle skew law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges alpha,beta, epsilon(alpha,beta)=paritySign(B(alpha,beta)) "
                        + "epsilon(beta,alpha), including coincident charges. The lower-matrix symmetrization "
                        + "proves the sign; it is not a field-locality assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualgeneratorlocality-actual-contraction-binomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualGeneratorLocality.actual_contraction_binomial"),
                H("Actual coefficient contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every integer t and natural j, coefficient j of translatedPolynomial(alpha, "
                        + "creationCoeff(beta,t)) is (-1)^j choose(B(alpha,beta),j) creationCoeff(beta,t-j). The "
                        + "choose function is the integer generalized binomial cast to C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualgeneratorlocality-actual-contraction-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualGeneratorLocality.actual_contraction_finite"),
                H("Contraction truncates before any infinite expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For fixed t the coefficient kernel in j has finite support because "
                        + "creationCoeff(beta,t-j)=0 for t-j<0. Negative lattice pairing does not require finite "
                        + "support of the binomial sequence itself."))),
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
