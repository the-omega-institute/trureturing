using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.LocalCompression;

internal sealed class KatoRankRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Recovery/LocalCompression/KatoRankRefutation.";

    private static readonly LibraryNoteRef Kato =
        LibraryNoteRef.Create("D5/L/Divergence/kato2025exactlocalcompression");
    private static readonly LibraryNoteRef ReebWolf =
        LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved");
    private static readonly LibraryNoteRef Fan =
        LibraryNoteRef.Create("D5/L/Eigenstructure/fan1949weyl");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact recovery dimension is n and the unrestricted Choi marginal-rank minimum is one.",
        H("A faithful classical family for Kato's rank proposal"),
        Blocks(
            Paragraph(Text(
                "Kato's equation (17) defines the normalized Choi state by applying the conditional "
                + "expectation to the second half of a normalized Bell pair. Equation (61) proposes taking "
                + "the least marginal rank over joint unitaries on those two factors. Theorem 1 and "
                + "equation (19) use a purification and its Schmidt rank. Equation (22) gives the rank of "
                + "the original Choi state, and equation (62) counts posterior classes for a classical law.")),
            Describe.Lean(
                DescribeId.Create("faithful-family"),
                DeclarationHandle.Create(Prefix + "faithful_family"),
                H("Exact recovery and Choi marginal rank for every alphabet size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato, ReebWolf, Fan),
                Blocks(
                    Paragraph(Text(
                        "For every n ≥ 1 and 0 < t < 1, give the pair (a,b) probability "
                        + "(t times the indicator of a = b plus (1−t)/n) divided by n. Every "
                        + "joint weight is positive and both marginals are uniform. Applying a "
                        + "channel on B fixes the bipartite density state exactly when it fixes "
                        + "every conditional state on B given A. Their uniform mixture is the "
                        + "reference state. Different labels have different likelihood vectors, "
                        + "so the exact diagonal recovery theorem gives minimum dimension n over "
                        + "all CPTP encoders and decoders.")),
                    Paragraph(Text(
                        "The conditional matrices have diagonal commutant since each pair of "
                        + "coordinates is separated by a conditional law. The trace conditional "
                        + "expectation is singleton coordinate pinching. Its normalized Choi state "
                        + "has diagonal weight 1/n at each (b,b) and zero elsewhere. The unitary "
                        + "permutation takes the basis ket (x,y) to (x−y mod n,y). Tracing the "
                        + "second factor after conjugation leaves the rank-one projector onto "
                        + "coordinate zero. Every candidate marginal has trace one, which proves "
                        + "that the least rank is one. The dimensions agree when n = 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The restriction of equation (61) to the faithful family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "For every member of the family with n ≥ 2, the exact recovery dimensions and the attainable "
                    + "unitary Choi marginal ranks have the same least element."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The two minima differ"),
                StatementSource.FromAuthor(Disp(new Formula.Not(FormulaDsl.Id("claim")))),
                AssessedProvenance.FromRepo(Kato),
                Blocks(Paragraph(Text(
                    "With n = 2 and t = 1/2 the four probabilities in basis order are "
                    + "(3,1,1,3)/8. The recovery minimum is two and the marginal-rank minimum "
                    + "is one, contradicting the common-minimum proposal."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Reeb and Wolf use related grouping of joint eigenvalues into product-basis rows "
                + "in Section 3.3 following Proposition 5. Fan's eigenvalue variational principle "
                + "bounds the mass that a fixed number of marginal coordinates can capture.")))));
}
