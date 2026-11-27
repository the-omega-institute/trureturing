using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class ChiralAnomalyRigidity4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D.";
    private const string Literature = "D5/L/LieTheory/allanach2020anomalies";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local anomaly cancellation for one generation and the parity of weak doublets.",
        H("Chiral anomaly rigidity in four dimensions"),
        Blocks(
            Paragraph(Text("The charges are all left handed. The coordinate order is the quark doublet, "
                + "the conjugate up and down singlets, the lepton doublet, the conjugate charged lepton "
                + "and, for six species, the conjugate neutrino. Write q, d and ν for the quark doublet, "
                + "conjugate down and conjugate neutrino charges.")),
            Result("five-linear", "anomaly5_linear_normal_form", "Elimination of three charges",
                "The mixed color, weak and gravitational equations force the lepton doublet charge "
                + "to be −3q, the charged lepton singlet charge to be 6q and the up singlet charge "
                + "to be −d − 2q."),
            Result("five-cubic", "anomaly5_cubic_factor", "Five-species cubic factorization",
                "After substitution the cubic coefficient is 18q(2q − d)(d + 4q)."),
            Result("five-lines", "anomaly5_classification", "Three labeled solution lines",
                "Over any characteristic-zero field the four anomaly equations hold exactly on the "
                + "scalar multiples of (1, −4, 2, −3, 6), (1, 2, −4, −3, 6) and (0, −1, 1, 0, 0). "
                + "The zero vector belongs to all three lines."),
            Result("five-unique", "anomaly5_projective_unique", "Uniqueness of the labeled direction",
                "A nonzero charge assignment cancels all four anomalies exactly when it lies on "
                + "a unique one of the three labeled lines."),
            Result("five-orbits", "anomaly5_orbit_classification", "Orbits under exchange of quark singlets",
                "A solution is a multiple of the standard direction, becomes such a multiple upon "
                + "exchange of the up and down singlets, or belongs to the vectorlike line. The "
                + "exchange fixes the vectorlike line as a set."),
            Result("six-cubic", "anomaly6_cubic_factor", "Six-species cubic factorization",
                "The charged lepton singlet charge becomes 6q − ν. The reduced cubic is "
                + "18q(2q − d − ν)(d − ν + 4q)."),
            Result("six-planes", "anomaly6_factorization", "Six-species cancellation locus",
                "The up singlet, lepton doublet and charged lepton singlet charges have the values "
                + "−d − 2q, −3q and 6q − ν. Cancellation holds exactly when these linear relations "
                + "hold and at least one of q = 0, d + ν = 2q and ν = d + 4q holds."),
            Result("yukawa-plane", "anomaly6_yukawa_normal_form", "Yukawa and Higgs neutrality",
                "For Higgs charge h, the four Yukawa charge sums are −h, h, h and −h. "
                + "These equations together with anomaly cancellation hold exactly for charges "
                + "(q, −h − q, h − q, −3q, h + 3q, 3q − h). Their down and neutrino singlet "
                + "charges sum to 2q, so the cubic vanishes throughout this plane."),
            Result("spectral-hypercharge", "spectral_triple_hypercharge_compatibility",
                "The finite spectral triple hypercharges",
                "The six rational charges of the finite spectral triple in all-left-handed order "
                + "equal the Yukawa normal form at q = 1/6 and h = 1/2."),
            Result("witten-parity", "witten_parity", "Weak-doublet parity",
                "One weak lepton doublet and one weak quark doublet per color give an even "
                + "total if and only if the color count is odd."),
            Result("witten-three-colors", "sm_witten_even", "Three colors",
                "For three colors the count is four and the doublet parity condition holds."))));

    private static DocumentBlock Result(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Literature)),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
