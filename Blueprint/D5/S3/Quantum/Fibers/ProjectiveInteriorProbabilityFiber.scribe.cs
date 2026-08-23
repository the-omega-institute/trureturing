using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class ProjectiveInteriorProbabilityFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared amplitudes on complex projective space have torus-shaped interior fibers.",
        H("Projective Interior Probability Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projective-interior-probability-fiber-equiv-torus"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber."
                        + "projective_interior_probability_fiber_equiv_torus"),
                H("Interior projective probability fibers are tori"),
                StatementSource.FromAuthor(FiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix the standard basis on the complex vector space with n plus one "
                            + "coordinates. The public state carrier is its Mathlib "
                            + "projectivization, and the basis-probability map sends any nonzero "
                            + "representative to its coordinatewise squared amplitudes divided "
                            + "by their total.")),
                    Paragraph(Text(
                        "For a strictly positive probability vector, every representative in "
                            + "the fiber has nonzero coordinates. Scaled affine ratios against "
                            + "coordinate zero therefore have squared norm one and define n "
                            + "relative circle phases.")),
                    Paragraph(Text(
                        "The inverse uses amplitudes whose positive magnitudes are the square "
                            + "roots of the prescribed probabilities, fixes the reference phase "
                            + "to one, and inserts the n relative phases. Direct representative "
                            + "computations prove both inverse laws on the projective fiber."))),
                DescribeRole.Theorem))));

    private static Formula FiberFormula()
    {
        Formula n = F.Id("n");
        Formula index = F.Id("i");
        Formula probability = F.Id("p");
        Formula probabilityAt = Seq(probability, Underscore, Grp(index));
        Formula simplex = Seq(Delta, Underscore, Grp(n));
        Formula basis = F.Id("B");
        Formula map = Seq(F.Id("q"), Underscore, Grp(basis));
        Formula state = F.Id("psi");
        Formula projectiveSpace = new Formula.Power(F.Id("CP"), Grp(n));
        Formula fiber = Seq(
            OpenBrace, OpenBracket, state, CloseBracket, InMacro, Sp, projectiveSpace,
            Sp, Mid, Sp, map, Open, OpenBracket, state, CloseBracket, Close,
            Sp, Eq, Sp, probability, CloseBrace);
        Formula relative = Call("relativePhaseCoordinates", probability);
        Formula torus = new Formula.Power(F.Id("T"), Grp(n));

        return Disp(Seq(
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            probability, InMacro, Sp, Operatorname, Grp(F.Id("int")), Open,
            simplex, Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp, probabilityAt, Sp, Gt, Sp, D(0), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("Bijective")), Open,
            relative, Colon, Sp, fiber, Sp, To, Sp, torus, Close, Dot));
    }
}
