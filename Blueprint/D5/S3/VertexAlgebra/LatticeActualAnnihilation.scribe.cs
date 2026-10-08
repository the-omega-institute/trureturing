using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeActualAnnihilationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Current derivations act on actual creation exponentials and translated polynomials.",
        H("Actual Current Derivations and Creation Exponentials"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("The consumed coefficientwise series derivation obeys Leibniz and commutes with formal "
                + "differentiation. The difference between d(exp(S)) and exp(S)d(S) has zero constant term "
                + "and satisfies the same first-order differential equation. Strong induction on finite "
                + "antidiagonals makes every coefficient zero.")),
            Describe.Lean(
                DescribeId.Create("latticeactualannihilation-actual-exponential-derivation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualAnnihilation.actual_exponential_derivation"),
                H("Coefficientwise chain rule for the actual exponential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every complex-linear polynomial derivation d and actual creation charge alpha, "
                        + "seriesDerivation(d,creationExponential(alpha)) equals creationExponential(alpha) times "
                        + "seriesDerivation(d,creationSeries(alpha)). No annihilation formula is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualannihilation-annihilation-creation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_creation"),
                H("Exact current action on every integer creation coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The Gram-weighted derivative at frequency k sends creationCoeff(alpha,t) to (k+1)^(-1) "
                        + "B(e_i,alpha) creationCoeff(alpha,t-(k+1)). Negative t and the integer-to-natural "
                        + "boundary are proved explicitly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualannihilation-annihilation-transport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_transport"),
                H("Annihilation commutes with actual polynomial translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every oscillator polynomial p the translated annihilation equals the coefficientwise "
                        + "polynomial derivation of translatedPolynomial(alpha,p). Polynomial induction proves this "
                        + "at each variable, sum and product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeactualannihilation-annihilation-convolution"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeActualAnnihilation.annihilation_convolution"),
                H("The finite convolution derivative includes the charge shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Differentiating the actual convolution gives its differentiated polynomial input plus "
                        + "(k+1)^(-1) B(e_i,alpha) times the convolution at s-(k+1). This is the consumed "
                        + "positive-current step of the mixed commutator."))),
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
