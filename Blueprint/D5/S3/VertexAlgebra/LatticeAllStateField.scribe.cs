using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeAllStateFieldDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual fields of every lattice state are creative and translation covariant.",
        H("Actual Fields of Every Lattice State"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric "
                + "with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity "
                + "is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate "
                + "polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct "
                + "sum of that polynomial algebra. Write B for the original integral bilinear form. "
                + "Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is "
                + "single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive "
                + "translation, and mu(a,q,b)=(Y(a))_q b.")),
            Paragraph(Text("For a charge delta and occurrence word, wordField starts with the actual charged ground "
                + "field and right-nests normalMinusOne of each divided current derivative. The occurrences "
                + "of a monomial are e.toMultiset.toList; their multiset and product are proved. Monomial "
                + "basis extension gives polynomialField, and Finsupp.lsum over the finite charge support "
                + "gives Y. Every recursive field is already lower truncated.")),
            Paragraph(Text("Word induction evaluates both finite normal-product branches on the actual vacuum. "
                + "Divided derivatives create the correct oscillator variable, while nonnegative vacuum "
                + "coefficients vanish. Binomial covariance and finite linear extension then transport the "
                + "same actual T to every word and every state.")),
            Describe.Lean(
                DescribeId.Create("latticeallstatefield-statefield-creation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creation"),
                H("Creation on every actual state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every a in V, (Y(a))_(-1) vacuum=a. No reconstruction or locality premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatefield-statefield-creativity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateField.stateField_creativity"),
                H("All nonnegative vacuum modes vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every a in V and every integer q>=0, (Y(a))_q vacuum=0. The proof evaluates the two "
                        + "normal-product sums on each word and extends over finite supports."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatefield-statefield-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateField.stateField_covariance"),
                H("Actual translation covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every a and integer q, [T,(Y(a))_q]=-q (Y(a))_(q-1). The current and charged "
                        + "generator covariance is consumed, and divided-derivative binomial shifts and "
                        + "normal-product covariance give the unrestricted state law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatefield-statefield-vacuum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateField.stateField_vacuum"),
                H("The actual vacuum field is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Y(vacuum)=identityField. The zero charged exponential and translated polynomial are "
                        + "evaluated, with identity mode -1 and all other modes zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeallstatefield-statefield-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeAllStateField.stateField_expansion"),
                H("Exact finite state-field expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Y(a) is the sum over the finite charge support and the finite monomial basis support, "
                        + "with the actual polynomial coefficients multiplying the corresponding wordField. It "
                        + "retains every charge and oscillator occurrence."))),
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
