using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CompletionConstants;

internal sealed class CompletionSignatureCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completion points, their problem-isomorphism class, and Gaussian self-duality covary under coordinate change.",
        H("Completion Signature Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-signature-covaries-under-coordinate-change"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/CompletionConstants/CompletionSignatureCovariance"
                        + ".completion_signature_covariance"),
                H("Completion signatures covary under coordinate change"),
                StatementSource.FromAuthor(CompletionCovarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C and CPrime be completion problems with the source seven-part carrier "
                            + "(A, X, D, F, Delta, N, G). A completion coordinate change consists "
                            + "of a parameter equivalence alpha together with exactly the two source "
                            + "conditions: alpha preserves membership in N if and only if, and it "
                            + "preserves zero structural defect if and only if. The completion-point "
                            + "type K(C) is the subtype of normalized parameters with zero defect.")),
                    Paragraph(Text(
                        "The seven displayed conjuncts are the seven semantic assertions carried by "
                            + "the Lean theorem. First, alpha restricts to an equivalence between the "
                            + "two completion-point types. Second, C and CPrime determine the same "
                            + "class in the quotient by completion coordinate changes. This quotient "
                            + "is an isomorphism-class object, not a numerical cardinality.")),
                    Paragraph(Text(
                        "Third, the Gaussian coordinate equivalence S is not the identity. Fourth "
                            + "and fifth, gStd and gAng are fixed respectively by the standard and "
                            + "angular Fourier operators. Sixth, the two coordinate formulas are "
                            + "different functions. Here gStd(x) is exp(-pi x^2), while gAng(x) is "
                            + "exp(-x^2/2); their inequality is witnessed concretely at x equal to one.")),
                    Paragraph(Text(
                        "Seventh, there exists an equivalence Phi between the two Fourier fixed-point "
                            + "types which sends the standard Gaussian fixed point to the angular "
                            + "Gaussian fixed point. Thus the last clause records both the unchanged "
                            + "fixed-point structure and the identity of the transported Gaussian, "
                            + "rather than merely asserting that two unrelated types are equinumerous.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Equiv.subtypeEquiv for the completion-point "
                            + "restriction, Quotient.sound for the problem-isomorphism class, and "
                            + "fourier_gaussian_pi for standard Gaussian self-duality. The angular "
                            + "operator in Lean is exactly the conjugate of the standard operator by "
                            + "the explicit scale sqrt(2*pi). Its fixed-point covariance and the "
                            + "formula exp(-x^2/2) are transported through that coordinate equivalence; "
                            + "no independent explicit angular-kernel integral theorem is claimed."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula script) =>
        Seq(value, Underscore, Grp(script));

    private static Formula Fixed(Formula transform) =>
        Seq(Operatorname, Grp(F.Id("Fix")), Open, transform, Close);

    private static Formula CompletionCovarianceFormula()
    {
        Formula c = F.Id("C");
        Formula cPrime = F.Id("CPrime");
        Formula a = F.Id("a");
        Formula alpha = Alpha;
        Formula normalization = Seq(a, Sp, InMacro, Sp, Mathcal, Grp(F.Id("N")));
        Formula normalizationPrime = Seq(
            Call(alpha, a), Sp, InMacro, Sp, Mathcal, Grp(F.Id("NPrime")));
        Formula defect = Call(Delta, a);
        Formula defectPrime = Call(Seq(Delta, Apos), Call(alpha, a));
        Formula kC = Call(F.Id("K"), c);
        Formula kCPrime = Call(F.Id("K"), cPrime);
        Formula standard = Subscript(Seq(Mathcal, Grp(F.Id("F"))), F.Id("std"));
        Formula angular = Subscript(Seq(Mathcal, Grp(F.Id("F"))), F.Id("ang"));
        Formula standardGaussian = Subscript(F.Id("g"), F.Id("std"));
        Formula angularGaussian = Subscript(F.Id("g"), F.Id("ang"));
        Formula scale = F.Id("S");

        return Disp(Seq(
            Begin, Grp(F.Id("aligned")),
            Alpha, Colon, Sp, F.Id("A"), Sp, Equiv, Sp, F.Id("APrime"), Comma, Amp, RowBreak,
            Forall, Sp, a, Comma, Sp,
            normalization, Sp, Leftrightarrow, Sp, normalizationPrime, Comma, Amp, RowBreak,
            Forall, Sp, a, Comma, Sp,
            defect, Sp, Eq, Sp, Subscript(D(0), F.Id("D")), Sp,
            Leftrightarrow, Sp, defectPrime, Sp, Eq, Sp,
            Subscript(D(0), F.Id("DPrime")), Amp, RowBreak,
            Longrightarrow, Sp,
            Subscript(alpha, kC), Colon, Sp, kC, Sp, Equiv, Sp, kCPrime, Amp, RowBreak,
            Land, Sp,
            Call(Operator(F.Id("IsoClass")), c), Sp, Eq, Sp,
            Call(Operator(F.Id("IsoClass")), cPrime), Amp, RowBreak,
            Land, Sp, scale, Sp, Neq, Sp, Operator(F.Id("id")), Amp, RowBreak,
            Land, Sp, Call(standard, standardGaussian), Sp, Eq, Sp, standardGaussian, Amp, RowBreak,
            Land, Sp, Call(angular, angularGaussian), Sp, Eq, Sp, angularGaussian, Amp, RowBreak,
            Land, Sp, standardGaussian, Sp, Neq, Sp, angularGaussian, Amp, RowBreak,
            Land, Sp, Exists, Sp, Phi, Colon, Sp,
            Fixed(standard), Sp, Equiv, Sp, Fixed(angular), Comma, Sp,
            Call(Phi, standardGaussian), Sp, Eq, Sp, angularGaussian, Dot,
            End, Grp(F.Id("aligned"))));
    }

    private static Formula Operator(Formula name) => Seq(Operatorname, Grp(name));
}
