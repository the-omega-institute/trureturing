using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class FiniteSignedNormalAtomicLocalizingConeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive atomic moments separate mass positivity from signed support localization.",
        H("Finite Signed-Normal Atomic Localizing Cone"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordinary-finite-atomic-hankel-matrix"),
                DeclarationHandle.Create(Prefix + "finiteAtomicHankelMatrix"),
                H("Ordinary finite atomic Hankel matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary moment matrix is the Vandermonde evaluation congruence with "
                        + "the atomic masses on its diagonal. Its construction reuses the existing "
                        + "finite Vandermonde vocabulary and the repository Hermitian-form layer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-support-localizing-matrix"),
                DeclarationHandle.Create(Prefix + "finiteAtomicShiftedLocalizingMatrix"),
                H("First support-localizing matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shifted matrix uses mass times support as its diagonal atomic weight. "
                        + "It therefore tests the support half-line while leaving the ordinary "
                        + "positive-mass moment matrix unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lagrange-atom-isolation-coefficients"),
                DeclarationHandle.Create(Prefix + "lagrangeIsolationCoefficients"),
                H("Lagrange atom-isolation coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At distinct support nodes, Cramer's rule applied to the existing Vandermonde "
                        + "matrix produces coefficients whose polynomial evaluations isolate one "
                        + "chosen atom exactly."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-mass-gives-ordinary-hankel-positivity"),
                DeclarationHandle.Create(Prefix + "finite_atomic_hankel_posSemidef"),
                H("Positive mass gives ordinary Hankel positivity"),
                StatementSource.FromAuthor(HankelPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonnegative atomic diagonal is positive semidefinite, and congruence by the "
                        + "Vandermonde evaluation matrix preserves positive semidefiniteness. "
                        + "The support nodes may have either sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lagrange-isolator-reads-one-shifted-atom"),
                DeclarationHandle.Create(Prefix +
                    "finite_atomic_shifted_localizing_lagrange_readout"),
                H("A Lagrange isolator reads one shifted atom"),
                StatementSource.FromAuthor(IsolatedReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the support map is injective, the Cramer coefficients evaluate to the "
                        + "chosen basis vector. The shifted Hermitian form then equals exactly the "
                        + "chosen mass times its support coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-mass-support-cone-separation"),
                DeclarationHandle.Create(Prefix +
                    "finite_signed_normal_atomic_localizing_cone"),
                H("Finite mass and support cones are separated"),
                StatementSource.FromAuthor(ConeSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Nonnegative masses force the ordinary Hankel matrix into the PSD cone. A "
                            + "positive-mass atom at a distinct negative support point is isolated "
                            + "by a finite polynomial, giving a strictly negative shifted readout.")),
                    Paragraph(Text(
                        "Consequently the first support-localizing matrix is not positive "
                            + "semidefinite. This finite theorem distinguishes positive mass from "
                            + "support in the allowed half-line; it does not construct the "
                            + "completed-xi normal measure."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula HankelPositivityFormula()
    {
        Formula atom = F.Id("atom");
        Formula support = F.Id("support");
        Formula mass = F.Id("mass");
        Formula depth = F.Id("depth");
        return Disp(Seq(
            Open, Forall, Sp, atom, Comma, Sp,
            D(0), Sp, Leq, Sp, Call("mass", atom), Close,
            Sp, Rightarrow, Sp,
            Call("PosSemidef", Call("finiteAtomicHankelMatrix", support, mass, depth))));
    }

    private static Formula IsolatedReadoutFormula()
    {
        Formula support = F.Id("support");
        Formula mass = F.Id("mass");
        Formula target = F.Id("target");
        Formula n = F.Id("n");
        Formula localizing = Call("finiteAtomicShiftedLocalizingMatrix", support, mass, n);
        Formula isolator = Call("lagrangeIsolationCoefficients", support, target);
        return Disp(Seq(
            Call("Injective", support), Sp, Rightarrow, Sp,
            Call("hermForm", localizing, isolator), Sp, Eq, Sp,
            Call("mass", target), Sp, Times, Sp, Call("support", target)));
    }

    private static Formula ConeSeparationFormula()
    {
        Formula atom = F.Id("atom");
        Formula support = F.Id("support");
        Formula mass = F.Id("mass");
        Formula target = F.Id("target");
        Formula n = F.Id("n");
        Formula hankel = Call("finiteAtomicHankelMatrix", support, mass, n);
        Formula localizing = Call("finiteAtomicShiftedLocalizingMatrix", support, mass, n);
        Formula isolator = Call("lagrangeIsolationCoefficients", support, target);
        return Disp(Seq(
            Call("Injective", support), Sp, Land, Sp,
            Open, Forall, Sp, atom, Comma, Sp,
            D(0), Sp, Leq, Sp, Call("mass", atom), Close, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Call("mass", target), Sp, Land, Sp,
            Call("support", target), Sp, Lt, Sp, D(0),
            Sp, Rightarrow, Sp,
            Call("PosSemidef", hankel), Sp, Land, Sp,
            Call("hermForm", localizing, isolator), Sp, Lt, Sp, D(0), Sp, Land, Sp,
            Neg, Sp, Call("PosSemidef", localizing)));
    }
}
