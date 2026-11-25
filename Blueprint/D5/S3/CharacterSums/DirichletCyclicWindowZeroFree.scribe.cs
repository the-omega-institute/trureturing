using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCyclicWindowZeroFreeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletCyclicWindowZeroFree.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero exclusion from actual cyclic long windows",
        H("Zero exclusion from actual cyclic long windows"),
        Blocks(
            Paragraph(Text("This repo-derived application constructs the actual finite "
                + "cyclic Dirichlet family, its transform and "
                + "its poles internally. It permits the principal character, removes the "
                + "source restriction theta less than one, and uses explicit coefficient "
                + "estimates without exponential loss. The source criterion supplies the "
                + "window-to-zero-exclusion route; the present statement is its actual "
                + "cyclic-family realization with these stated extensions.")),
            Paragraph(Text("For a Dirichlet character chi of order r, use the actual family "
                + "U plus the sum of the real corrected character ramps for powers one "
                + "through r minus one, each weighted by one divided by three r plus one. "
                + "The modulus is positive. The principal character is also allowed, "
                + "with its order-one family consisting solely of U.")),
            Describe.Lean(DescribeId.Create("actual-long-window-zero-free"),
                DeclarationHandle.Create(Module + "gl1_long_window_zero_free"),
                H("The actual long-window criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Fix any real exponent theta, "
                    + "a positive width delta, and a real constant C. Suppose that beyond "
                    + "every cutoff there is a positive Y such that the actual family is "
                    + "at most C times x to the theta for every x between Y and Y to the "
                    + "one plus delta. Then zeta is nonzero at every s with real part "
                    + "greater than theta. Every L-function of "
                    + "chi to the power j is nonzero there for one at most j less than r. "
                    + "There is no hypothesis about zeros, residues, poles, principal "
                    + "parts, analytic continuation, or derivative estimates. At s equal "
                    + "to one, the zeta assertion concerns Mathlib's nonzero totalized "
                    + "value and does not assert analyticity of classical zeta at its pole.")),
                    Paragraph(Text("For nonpositive theta, lifting the windows "
                    + "to a positive exponent "
                    + "below an existing nontrivial zeta zero gives a contradiction. Thus "
                    + "that window premise is impossible; it supplies no new analytic "
                    + "continuation domain. For positive theta the arithmetic Laplace identity "
                    + "gives the normalized "
                    + "continuation. Its simple poles have positive weighted multiplicity. "
                    + "A nearest isolated pole yields high derivative lower bounds; "
                    + "Cauchy's estimate controls the analytic remainder. The one-sided "
                    + "window and gamma tails give the competing moment upper bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-critical-half-plane"),
                DeclarationHandle.Create(Module + "gl1_zero_free_at_half_of_all_windows"),
                H("The critical half-plane consequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If such a window exists for every theta strictly "
                    + "between one half and one, with delta and C allowed to depend on "
                    + "theta, then zeta and every nontrivial cyclic-power L-function "
                    + "have no zeros with real part greater than one half. The zeta "
                    + "value at one is the nonzero totalized Mathlib value, not an "
                    + "assertion of classical analyticity at the pole. The quantified window "
                    + "assumption supplies only a positive delta, a real C and the actual "
                    + "pointwise window bound; exponent inequalities are not repeated."))),
                DescribeRole.Theorem))));
}
