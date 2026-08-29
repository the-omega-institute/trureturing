using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class GoldenRealizationCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/GoldenRealizationCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden structure has a cross-representation certificate and a repelling countermodel.",
        H("Golden Cross-Representation Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-golden-cross-representation-certificate"),
                DeclarationHandle.Create(
                    Prefix + "canonical_golden_cross_representation_certificate"),
                H("Canonical golden realizations satisfy one typed certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proposition packages the golden quadratic identity, the reciprocal "
                            + "Mobius fixed point, the thirty-six-degree rotation trace, the "
                            + "Fibonacci power recurrence, and the projective contraction "
                            + "radius.")),
                    Paragraph(Text(
                        "The certificate records one structure through several typed realizations. "
                            + "It does not erase carrier types or claim a universal dynamical "
                            + "law for every map containing the golden ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-fixed-point-can-be-repelling"),
                DeclarationHandle.Create(Prefix + "golden_fixed_does_not_force_attraction"),
                H("Golden fixedness alone does not force attraction"),
                StatementSource.FromAuthor(CountermodelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An explicit affine map fixes the golden point and has multiplier varphi "
                        + "squared, which is strictly larger than one. This closes the scope "
                        + "boundary by a concrete countermodel."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula() => Disp(Seq(
        F.Id("varphi"), Caret, D(2), Sp, Eq, Sp,
        F.Id("varphi"), Sp, Plus, Sp, D(1), Sp, Land, Sp,
        D(2), Sp, Call("cos", Seq(Pi, Slash, D(5))), Sp, Eq, Sp,
        F.Id("varphi"), Sp, Land, Sp,
        Call("abs", F.Id("goldenProjectiveMultiplier")), Sp, Lt, Sp, D(1)));

    private static Formula CountermodelFormula() => Disp(Seq(
        Call("IsFixedPt", F.Id("goldenRepellingAffine"), F.Id("varphi")),
        Sp, Land, Sp, D(1), Sp, Lt, Sp,
        Call("abs", Seq(F.Id("varphi"), Caret, D(2)))));
}
