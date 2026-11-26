using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class DirichletGRHDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/GRH.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeros of the Riemann zeta function and Dirichlet L-functions",
        H("Zeros of the Riemann zeta function and Dirichlet L-functions"),
        Blocks(
            Paragraph(Text("Levent Alpöge's proof, written with Claude, reaches the critical line through a nonvanishing theorem. In the compact edition, New.Main compares two bounds for the covolume of the same family of theta lifts. After the main height cancels, the comparison bounds a weighted prime sum from above. A one-sided analytic criterion converts the resulting estimate into nonvanishing for every Dirichlet character to the right of the critical line, with the principal character's pole excluded.")),
            Paragraph(Text("The functional equation then rules out a zero in the left half of the open critical strip by passing to the reflected point for the corresponding character. For the Riemann zeta function the proof specializes to modulus one and uses the functional equation for the completed zeta function. The negative even integers are among the poles of the classical gamma factor, and the zeta statement excludes them explicitly.")),
            Describe.Lean(DescribeId.Create("riemann-hypothesis"),
                DeclarationHandle.Create(Module + "riemannHypothesis"), H("The Riemann hypothesis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every complex zero of the Riemann zeta function other than a negative even integer, with the point 1 excluded, has real part one half. The theorem supplies Mathlib's proposition RiemannHypothesis directly."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("riemann-zeta-zero"),
                DeclarationHandle.Create(Module + "riemannZeta_eq_zero_re"), H("The real part of a zeta zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a specified complex s, the hypotheses are that the zeta value at s vanishes, that s differs from −2(n + 1) for every natural number n, and that s differs from 1. The conclusion is Re(s) = 1/2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dirichlet-nonvanishing"),
                DeclarationHandle.Create(Module + "LFunction_ne_zero_of_half_lt_re"), H("Nonvanishing in the open right half-plane"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let the modulus be any positive integer, and let χ be any complex Dirichlet character of that modulus. For every complex s with Re(s) > 1/2, the value of L(s, χ) is nonzero if χ is nonprincipal or s differs from 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dirichlet-strip"),
                DeclarationHandle.Create(Module + "LFunction_eq_zero_re"), H("All characters in the open critical strip"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive modulus and every complex Dirichlet character χ, if 0 < Re(s) < 1 and L(s, χ) = 0, then Re(s) = 1/2. This includes imprimitive characters."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-dirichlet-strip"),
                DeclarationHandle.Create(Module + "LFunction_eq_zero_re_of_isPrimitive"), H("Primitive characters"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Fix a primitive complex Dirichlet character χ of any positive modulus. Every complex zero s of L(s, χ) with 0 < Re(s) < 1 has Re(s) = 1/2. This follows by applying the theorem for all characters at χ."))),
                DescribeRole.Theorem))));
}
