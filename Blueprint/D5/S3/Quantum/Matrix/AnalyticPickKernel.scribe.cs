using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AnalyticPickKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/AnalyticPickKernel";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/donoghue1974monotone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cauchy averaging proves full finite matrix-valued Caratheodory and Pick kernel positivity.",
        H("Analytic matrix Pick kernels"), Blocks(
        Item("caratheodoryGram", "The full Caratheodory Gram matrix",
            "For positive R, samples z_i in the radius-R disk, and a finite complex matrix "
            + "function G, entry (i,a),(j,b) is entry a,b of G(z_i)+G(z_j) star divided by "
            + "1-z_i conjugate(z_j)/R squared. The indices include all sample and vector "
            + "coordinates, so positivity tests arbitrary distinct vectors at different samples.", true),
        Item("finite_circle_caratheodory_posSemidef", "Positivity from the actual Cauchy formula",
            "In every finite matrix dimension and for every finite sample set, suppose R>0, "
            + "G is complex differentiable on the open radius-R disk and continuous on its "
            + "closure, and G(eta)+G(eta) star is positive semidefinite on its boundary circle. "
            + "Then the Caratheodory Gram matrix is positive semidefinite. Put phi_w(eta)="
            + "(1-conjugate(w) eta/R squared) inverse. Its pole is outside the closed disk. "
            + "On the circle, conjugate(phi_z)=eta/(eta-z). The existing Banach-valued "
            + "Cauchy average formula applied to phi_w G gives the G(z) term; taking the "
            + "adjoint of the swapped identity supplies G(w) star. The complete boundary "
            + "integrand factors as C star (G+G star) C, where C[a,(i,b)] is delta_ab "
            + "phi_(z_i). Positivity follows by integration in the actual matrix Loewner order."),
        Item("open_disk_caratheodory_posSemidef", "The open disk without boundary regularity",
            "If G is complex differentiable on the open unit disk and G+G star is positive "
            + "semidefinite there, every finite Caratheodory Gram matrix at R=1 is positive "
            + "semidefinite. Restrict first to smaller closed disks containing the samples, "
            + "then let their radii increase to one. Denominators stay nonzero, and the "
            + "finite matrix positive cone is closed. No values or regularity on the unit "
            + "circle are assumed."),
        Item("imaginaryPart", "Hermitian imaginary part",
            "The imaginary part of A is (-i/2) times A-A star.", true),
        Item("pickGram", "The finite Pick block matrix",
            "Entry (i,a),(j,b) is entry a,b of T(z_i)-T(z_j) star divided by "
            + "z_i-conjugate(z_j). On the upper half-plane all denominators are nonzero.", true),
        Item("upper_half_plane_pick_posSemidef", "Global analytic Pick positivity",
            "For every finite complex matrix dimension, every holomorphic T on the upper "
            + "half-plane with pointwise nonnegative Hermitian imaginary part, and every "
            + "finite family of points there, the full Pick block matrix is positive "
            + "semidefinite. Set psi(u)=i(1+u)/(1-u) and G(u)=-i T(psi(u)). The disk "
            + "theorem applies because G+G star is twice the imaginary part of T. The exact "
            + "domain Cayley identity gives K=(1/2) C L C star, with C diagonal and "
            + "C_(i,a)=1-u_i. The inverse coordinate is u_i=(z_i-i)/(z_i+i). "
            + "No positive kernel, Herglotz measure or Taylor coefficients occur as premises."),
        Paragraph(Text("These are classical Caratheodory, Pick and Loewner arguments, "
            + "implemented through Mathlib's circleAverage_smul_div and closed matrix "
            + "positivity cone; see Donoghue, Monotone Matrix Functions and Analytic "
            + "Continuation, DOI 10.1007/978-3-642-65755-9, and Agler–McCarthy, "
            + "DOI 10.1090/gsm/044. No mathematical novelty is claimed. The real boundary "
            + "Hankel consequence uses additional local analytic and Hermitian real-axis "
            + "hypotheses. Applying it to actual principal matrix powers still requires "
            + "the global analytic and sector supplier bridge. Full independent X,Y "
            + "He–Saunderson–Fawzi compatibility remains open.")))));

    private static DocumentBlock Item(string name, string title, string text, bool definition = false) =>
        Describe.Lean(DescribeId.Create("analytic-pick-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(text))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
